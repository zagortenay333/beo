#include "compiler/sem.h"
#include "compiler/vm.h"
#include "compiler/parser.h"

ienum (Result, U8) {
    RESULT_OK,
    RESULT_DEFER,
    RESULT_ERROR,
};

istruct (MatchPair) {
    Ast *n1;
    Ast *n2;
    Type *t1;
    Type *t2;
};

istruct (Sem) {
    Mem *mem;
    Vm *vm;
    Parser *parser;
    Interns *interns;

    AstFn *main_fn;
    ArrayAstFn fns;
    ArrayType types;
    ArrayAst globals;
    Map(AstId, VmReg) global_to_reg;

    Scope *autoimports;
    Map(IString*, AstFile*) files;

    ArrayAst eval_list;
    ArrayAst check_list;

    U64 error_count;
    U64 next_type_id;
    Bool found_a_sem_edge;

    SemCoreTypes core_types;

    struct { // Info about ongoing match().
        U64 ongoing;
        Ast *dummy1;
        Ast *dummy2;
        Bool applied_cast;
        MatchPair top_pair;
        U64 without_error_reporting;
    } match;
};

static Ast *get_target (Ast *node);
static Result match_vv (Sem *sem, Ast **v1, Ast **v2);
static Result match_nn (Sem *sem, Ast *n1, Ast *n2);
static Result match_nv (Sem *sem, Ast *n, Ast **v);
static Result match_nc (Sem *sem, Ast *n, Ast *c);
static Result match_tt (Sem *sem, Type *t1, Type *t2);
static Result match_tv (Sem *sem, Type *t, Ast **v);
static Void set_const_val (Sem *sem, Ast *node, VmReg reg);
static Void add_to_check_list (Sem *sem, Ast *n, Scope *scope);
static Void check_for_invalid_cycle (Sem *sem, AstTag tag, Ast *node);
static Result error_n Fmt(3, 4) (Sem *sem, Ast *n, CString fmt, ...);
static Result error_nn Fmt(4, 5) (Sem *sem, Ast *n1, Ast *n2, CString fmt, ...);

static U64 get_type_struct_size [] = {
    #define X(_, type, ...) cast(U64, sizeof(type)),
        EACH_TYPE(X)
    #undef X
};

static U8 get_type_struct_align [] = {
    #define X(_, type, ...) alignof(type),
        EACH_TYPE(X)
    #undef X
};

static TypeFlags get_default_type_flags [] = {
    #define X(a, b, flags) flags,
        EACH_TYPE(X)
    #undef X
};

#define MAX_RECORDED_ERRORS 32

#define sem_msg(N, TAG) log_msg(N, TAG, "Typer", 1);

Noreturn
static Void sem_panic (Sem *sem) {
    log_scope_end_all();
    panic();
}

#define get_file(NODE)         (sem_get_file(sem, NODE))
#define get_type(NODE)         ((NODE)->sem_type)
#define set_type(NODE, TYPE)   ((NODE)->sem_type = TYPE)
#define get_scope(NODE)        ((NODE)->sem_scope)
#define set_scope(NODE, SCOPE) ((NODE)->sem_scope = SCOPE)

#define try_get_type(NODE) ({\
    Type *t = get_type(NODE);\
    if (! t) return RESULT_DEFER;\
    t;\
})

#define try_get_type_v(NODE) ({\
    def1(n, acast(Ast*, NODE));\
    Type *t = try_get_type(n);\
    if (n->flags & AST_IS_TYPE) return error_n(sem, n, "Expected value expression.");\
    t;\
})

#define try_get_type_t(NODE) ({\
    def1(n, acast(Ast*, NODE));\
    Type *t = try_get_type(n);\
    if (! (n->flags & AST_IS_TYPE)) return error_n(sem, n, "Expected type expression.");\
    t;\
})

#define try(RESULT, ...) ({\
    def1(R, acast(Result, RESULT));\
    if (R != RESULT_OK) { __VA_ARGS__; return R; }\
    RESULT_OK;\
})

static AstFile *import_file (Sem *sem, IString *path, Ast *error_node) {
    AstFile *file = map_get_ptr(&sem->files, path);
    if (file) return file;

    file = par_parse_file(sem->parser, path);
    if (! file) {
        if (error_node) {
            error_n(sem, error_node, "Unable to import file [%.*s].", STR(*path));
        } else {
            sem_msg(msg, LOG_ERROR);
            astr_push_fmt(msg, "Unable to import file [%.*s].\n", STR(*path));
        }

        sem_panic(sem);
    }

    add_to_check_list(sem, cast(Ast*, file), sem->autoimports);
    map_add(&sem->files, path, file);
    return file;
}

// Top call should have allow_local_var = false.
static Result can_eval (Sem *sem, Ast *node, Bool allow_local_var) {
    if (node->flags & (AST_VISITED | AST_CAN_EVAL)) return RESULT_OK;

    // Local variables cannot be compile-time evaled, but when we
    // enter into a function during this lookup we need to allow
    // references to local variables since then we are looking to
    // see whether the entire function can eval, not just a part
    // of it.
    if (node->tag == AST_FN) allow_local_var = true;

    node->flags |= AST_VISITED;

    reach(r);
    #define RETURN(R) {\
        reached(r);\
        node->flags &= ~AST_VISITED;\
        return R;\
    }

    #define CAN_EVAL(child, ...) try(can_eval(sem, child, allow_local_var), RETURN(R));\

    AST_VISIT_CHILDREN(node, CAN_EVAL);

    Ast *d = get_target(node);
    if (d) {
        if ((d->flags & AST_IS_LOCAL_VAR) && !allow_local_var) RETURN(error_nn(sem, node, d, "Cannot compile-time eval local variable."));
        CAN_EVAL(d);
    }

    node->flags |= AST_CAN_EVAL;
    RETURN(RESULT_OK);

    #undef RETURN
    #undef CAN_EVAL
}

static Void collect_program_ (SemProgram *prog, Ast *node) {
    if (node->flags & AST_VISITED) return;
    node->flags |= AST_VISITED;

    assert_dbg(node->flags & AST_CAN_EVAL);

    if (node->flags & AST_IS_GLOBAL_VAR) array_push(&prog->globals, node);
    if (node->tag == AST_FN) array_push(&prog->fns, cast(AstFn*, node));

    Type *t = get_type(node);
    if (! (t->flags & TYPE_VISITED)) {
        t->flags |= TYPE_VISITED;
        array_push(&prog->types, t);
    }

    #define C(child, ...) collect_program_(prog, child)

    AST_VISIT_CHILDREN(node, C);

    Ast *d = get_target(node);
    if (d) C(d);

    node->flags &= ~AST_VISITED;
    #undef C
}

static SemProgram *collect_program (Sem *sem, Ast *node, Mem *mem) {
    Auto prog = mem_new(mem, SemProgram);
    prog->sem = sem;
    prog->entry = node;
    array_init(&prog->globals, mem);
    array_init(&prog->types, mem);
    array_init(&prog->fns, mem);
    collect_program_(prog, node);
    array_iter (t, &prog->types) t->flags &= ~TYPE_VISITED;
    return prog;
}

// If this returns VM_REG_NIL, then the node could not be 
// evaled and should be compiled to the VM for evaling.
static VmReg ast_eval (Sem *sem, Ast *node) {
    #define TRY(X) ({\
        VmReg val = (X);\
        if (val.tag == VM_REG_NIL) return val;\
        val;\
    })

    #define BINOP(OP) ({\
        VmReg c1 = TRY(ast_eval(sem, cast(AstBaseBinary*, node)->op1));\
        VmReg c2 = TRY(ast_eval(sem, cast(AstBaseBinary*, node)->op2));\
        vm_reg_##OP(c1, c2);\
    })

    #define UNOP(OP) ({\
        VmReg c = TRY(ast_eval(sem, cast(AstBaseUnary*, node)->op));\
        vm_reg_##OP(c);\
    })

    switch (node->tag) {
    case AST_ADD:            return BINOP(add);
    case AST_DIV:            return BINOP(div);
    case AST_EQUAL:          return BINOP(equal);
    case AST_GREATER:        return BINOP(greater);
    case AST_GREATER_EQUAL:  return BINOP(greater_equal);
    case AST_LESS:           return BINOP(less);
    case AST_LESS_EQUAL:     return BINOP(less_equal);
    case AST_MOD:            return BINOP(mod);
    case AST_MUL:            return BINOP(mul);
    case AST_NOT_EQUAL:      return BINOP(mod);
    case AST_SUB:            return BINOP(mod);
    case AST_NEGATE:         return UNOP(negate);
    case AST_NOT:            return UNOP(not);
    case AST_BOOL_LITERAL:   return (VmReg){ .tag=VM_REG_BOOL, .boolean=cast(AstBoolLiteral*, node)->val };
    case AST_FLOAT_LITERAL:  return (VmReg){ .tag=VM_REG_FLOAT, .f64=cast(AstFloatLiteral*, node)->val };
    case AST_INT_LITERAL:    return (VmReg){ .tag=VM_REG_INT, .i64=cast(AstIntLiteral*, node)->val };
    case AST_IDENT:          return ast_eval(sem, cast(AstIdent*, node)->sem_edge);
    case AST_VAR_DEF:        return ast_eval(sem, cast(AstVarDef*, node)->init);
    case AST_LOGICAL_AND: {
        Auto n = cast(AstBaseBinary*, node);
        VmReg out = TRY(ast_eval(sem, n->op1));
        if (out.boolean) out = TRY(ast_eval(sem, n->op2));
        return out;
    }
    case AST_LOGICAL_OR: {
        Auto n = cast(AstBaseBinary*, node);
        VmReg out = TRY(ast_eval(sem, n->op1));
        if (! out.boolean) out = TRY(ast_eval(sem, n->op2));
        return out;
    }
    default: return (VmReg){};
    }

    #undef TRY
    #undef BINOP
}

static Result eval (Sem *sem, Ast *node) {
    try(can_eval(sem, node, false));

    VmReg val = ast_eval(sem, node);

    if (val.tag == VM_REG_NIL) { // We need to compile for the VM in order to eval.
        tmem_new(tm);
        tmem_pin(tm, 0);

        SemProgram *prog  = collect_program(sem, node, tm);
        Ast *original_entry = prog->entry;

        if (prog->entry->tag != AST_FN) {
            // @todo For now we don't actually allocate the return value
            // ast node because the the backend doesn't need one, but it
            // still feels kind of sketchy.
            String fn_name = astr_fmt(tm, "global_var_wrapper@%lu", prog->entry->pos.first_line);
            Ast *fn  = ast_alloc(tm, AST_FN, 0);
            Ast *ret = ast_alloc(tm, AST_RETURN, 0);
            cast(AstFn*, fn)->name = intern_str(sem->interns, fn_name);
            array_push(&cast(AstFn*, fn)->statements, ret);
            cast(AstReturn*, ret)->sem_edge = fn;
            cast(AstReturn*, ret)->result = (prog->entry->tag == AST_VAR_DEF) ? cast(AstVarDef*, prog->entry)->init : prog->entry;
            array_push(&prog->fns, cast(AstFn*, fn));
            prog->entry = fn;
        }

        Vm *vm = vm_new(tm);
        vm_set_prog(vm, prog);

        switch (get_type(original_entry)->tag) {
        case TYPE_FFI:
        case TYPE_ARRAY: 
        case TYPE_RECORD:
        case TYPE_STRING:
        case TYPE_TOP:
        case TYPE_VOID:
            // @todo In order to handle array/string/objects we somehow have to
            // pull them out of one VM and insert them into the other (main) VM...
            return error_n(sem, original_entry, "Expressions of this type cannot compile-time eval at moment.");

        case TYPE_BOOL:
        case TYPE_FLOAT:
        case TYPE_FN: 
        case TYPE_INT:
            vm_run(vm);
            val = array_get(&vm->registers, 0);
            break;
        }

        vm_destroy(vm);
    }

    map_add(&sem->global_to_reg, node->id, val);
    node->flags |= AST_EVALED;
    return RESULT_OK;
}


static Type *alloc_type (Sem *sem, TypeTag tag) {
    Auto type   = mem_alloc(sem->mem, Type, .zeroed=true, .align=get_type_struct_align[tag], .size=get_type_struct_size[tag]);
    type->id    = sem->next_type_id++;
    type->tag   = tag;
    type->flags = get_default_type_flags[tag];
    array_push(&sem->types, type);
    return type;
}

static Type *alloc_type_fn (Sem *sem, AstBaseFn *n) {
    Auto t = cast(TypeFn*, alloc_type(sem, TYPE_FN));
    t->node = n;
    return cast(Type*, t);
}

static Type *alloc_type_record (Sem *sem, AstRecord *n) {
    Auto t = cast(TypeRecord*, alloc_type(sem, TYPE_RECORD));
    t->node = n;
    return cast(Type*, t);
}

static Type *alloc_type_array (Sem *sem, Ast *node, Type *element) {
    Auto t = cast(TypeArray*, alloc_type(sem, TYPE_ARRAY));
    t->node = node;
    t->element = element;
    return cast(Type*, t);
}

static Ast *get_target (Ast *node) {
    switch (node->tag) {
    #define X(TAG, T, ...) case TAG: return cast(T*, node)->sem_edge;
        EACH_AST_SELECTOR(X);
    #undef X
    default: return 0;
    }
}

static Void sem_set_target (Sem *sem, Ast *node, Ast *target) {
    switch (node->tag) {
    #define X(TAG, T, ...) case TAG: cast(T*, node)->sem_edge = target; break;
        EACH_AST_SELECTOR(X);
    #undef X
    default: badpath;
    }

    sem->found_a_sem_edge = true;
}

static AstFile *sem_get_file (Sem *sem, Ast *node) {
    for (Scope *s = get_scope(node); s; s = s->parent) {
        Ast *o = s->owner;
        if (o->tag == AST_FILE) return cast(AstFile*, o);
    }

    return 0;
}

static Void scope_seal (Sem *sem, Scope *scope) {
    scope->owner->flags |= AST_IS_SEALED_SCOPE;
}

static Scope *scope_new (Sem *sem, Scope *parent, Ast *owner) {
    Scope *scope = mem_new(sem->mem, Scope);
    scope->parent = parent;
    scope->owner = owner;
    set_scope(owner, scope);
    map_init(&scope->map, sem->mem);
    return scope;
}

static Result scope_add (Sem *sem, Scope *scope, IString *key, Ast *val, Ast *error_node) {
    Ast *def = map_get_ptr(&scope->map, key);
    if (def) return error_nn(sem, error_node, def, "Attempting to redeclare definition.");

    def = map_get_ptr(&sem->autoimports->map, key);
    if (def) return error_nn(sem, error_node, def, "Attempting to shadow name that is auto-imported.");

    map_add(&scope->map, key, val);
    return RESULT_OK;
}

static Scope *scope_get_ancestor (Scope *s, AstTag tag) {
    for (; s; s = s->parent) if (s->owner->tag == tag) return s;
    return 0;
}

static Ast *scope_lookup_outside_in (Sem *sem, Scope *scope, IString *key, Ast *selector) {
    Ast *target = map_get_ptr(&scope->map, key);
    if (! target) return 0;
    sem_set_target(sem, selector, target);
    return target;
}

// @todo We are not checking for invalid forward references, but implementing
// this should be postponed until we decide whether to add codegen or not.
static Ast *scope_lookup_inside_out (Sem *sem, Scope *scope, IString *key, Ast *selector) {
    Bool crossed_fn_scope = false;

    while (scope) {
        Ast *target = map_get_ptr(&scope->map, key);

        if (target) {
            if (crossed_fn_scope && (target->flags & AST_IS_LOCAL_VAR)) {
                error_nn(sem, selector, target, "Invalid reference to target in enclosing function.");
                return 0;
            }

            sem_set_target(sem, selector, target);
            return target;
        }

        if (scope->owner->tag == AST_FN) crossed_fn_scope = true;
        scope = scope->parent;
    }

    return 0;
}

static Void log_type (Sem *sem, AString *astr, Type *type) {
    if (! type) {
        astr_push_cstr(astr, "$");
        return;
    } else if (type->flags & TYPE_VISITED) {
        switch (type->tag) {
        #define X(TAG, NAME, ...) case TAG: astr_push_cstr(astr, #NAME); break;
            EACH_TYPE(X);
        #undef X
        }
        return;
    }

    type->flags |= TYPE_VISITED;

    switch (type->tag) {
    case TYPE_TOP:    astr_push_cstr(astr, "Top"); break;
    case TYPE_BOOL:   astr_push_cstr(astr, "Bool"); break;
    case TYPE_VOID:   astr_push_cstr(astr, "Void"); break;
    case TYPE_FLOAT:  astr_push_cstr(astr, "Float"); break;
    case TYPE_INT:    astr_push_cstr(astr, "Int"); break;
    case TYPE_STRING: astr_push_cstr(astr, "String"); break;

    case TYPE_FFI: {
        String name = cast(TypeFfi*, type)->name;
        astr_push_fmt(astr, "ffi<%.*s>", STR(name));
    } break;

    case TYPE_RECORD: {
        IString *name = cast(TypeRecord*, type)->node->name;
        astr_push_fmt(astr, "%.*s", STR(*name));
    } break;

    case TYPE_ARRAY: {
        TypeArray *t = cast(TypeArray*, type);
        astr_push_cstr(astr, "[]");
        log_type(sem, astr, t->element);
    } break;

    case TYPE_FN: {
        AstBaseFn *n = cast(TypeFn*, type)->node;
        astr_push_cstr(astr, "Fn (");

        array_iter (n, &n->inputs) {
            log_type(sem, astr, get_type(n));
            if (! ARRAY_ITER_DONE) astr_push_cstr(astr, ", ");
        }

        astr_push_byte(astr, ')');
        if (n->output) { astr_push_cstr(astr, " -> "); log_type(sem, astr, get_type(n->output)); }
    } break;
    }

    type->flags &= ~TYPE_VISITED;
}

static Void log_node_no_flush (Sem *sem, SrcLog *slog, AString *astr, Ast *node) {
    AstFile *file = get_file(node);
    if (! file) return;
    slog_add_src(slog, cast(Ast*, file)->id, *file->path, file->content);
    slog_add_pos(slog, cast(Ast*, file)->id, ast_trimmed_pos(sem->interns, node));
}

static Void log_node (Sem *sem, AString *astr, Ast *node) {
    tmem_new(tm);
    SrcLog *slog = slog_new(tm, slog_default_config);
    log_node_no_flush(sem, slog, astr, node);
    slog_flush(slog, astr);
}

static Void log_nodes (Sem *sem, AString *astr, Ast *n1, Ast *n2) {
    tmem_new(tm);
    SrcLog *slog = slog_new(tm, slog_default_config);
    log_node_no_flush(sem, slog, astr, n1);
    log_node_no_flush(sem, slog, astr, n2);
    slog_flush(slog, astr);
}

Void sem_print_node (Sem *sem, AString *astr, Ast *node) {
    U64 margin = slog_default_config->left_margin;
    astr_push_fmt(astr, "%*s" TERM_RED("TAG") ": %s\n", cast(Int,margin), "", ast_tag_to_cstr[node->tag]);
    log_node(sem, astr, node);
}

Void sem_print_node_out (Sem *sem, Ast *node) {
    tmem_new(tm);
    AString a = astr_new(tm);
    sem_print_node(sem, &a, node);
    astr_println(&a);
}

#define NO_ERROR_REPORTING() (sem->match.without_error_reporting || sem->error_count >= MAX_RECORDED_ERRORS)

static Void error_no_progress (Sem *sem) {
    array_iter (n, &sem->check_list) {
        if (!get_type(n) && (n->tag == AST_VAR_DEF)) {
            check_for_invalid_cycle(sem, n->tag, n);
        }
    }

    array_iter (n, &sem->check_list) {
        Ast *d = get_target(n);
        if (d) continue;

        switch (n->tag) {
        case AST_DOT:   if (get_type(cast(AstDot*, n)->lhs)) { error_n(sem, n, "Reference to undeclared member."); sem_panic(sem); } break;
        case AST_IDENT: { error_n(sem, n, "Reference to undeclared identifier."); sem_panic(sem); } break;
        default: break;
        }
    }

    { // Something couldn't compile-time eval maybe:
        Ast *n = array_try_get(&sem->eval_list, 0);
        if (n) { error_n(sem, n, "Could not compile-time eval node."); sem_panic(sem); }
    }

    { // Unknown reason (compiler error):
        sem_msg(msg, LOG_ERROR);
        astr_push_fmt(msg, "Unable to check the following nodes:\n\n");
        array_iter (n, &sem->check_list) log_node(sem, msg, n);
        sem_panic(sem);
    }
}

static Result error_n Fmt(3, 4) (Sem *sem, Ast *n, CString fmt, ...) {
    if (NO_ERROR_REPORTING()) return RESULT_ERROR;
    sem_msg(msg, LOG_ERROR);
    astr_push_fmt_vam(msg, fmt);
    astr_push_byte(msg, '\n');
    astr_push_byte(msg, '\n');
    log_node(sem, msg, n);
    sem->error_count++;
    return RESULT_ERROR;
}

static Result error_nn Fmt(4, 5) (Sem *sem, Ast *n1, Ast *n2, CString fmt, ...) {
    if (NO_ERROR_REPORTING()) return RESULT_ERROR;
    sem_msg(msg, LOG_ERROR);
    astr_push_fmt_vam(msg, fmt);
    astr_push_byte(msg, '\n');
    astr_push_byte(msg, '\n');
    log_nodes(sem, msg, n1, n2);
    sem->error_count++;
    return RESULT_ERROR;
}

static Result error_nt Fmt(4, 5) (Sem *sem, Ast *n, Type *t, CString fmt, ...) {
    if (NO_ERROR_REPORTING()) return RESULT_ERROR;
    sem_msg(msg, LOG_ERROR);
    astr_push_cstr(msg, "Got type " TERM_START_RED);
    log_type(sem, msg, t);
    astr_push_cstr(msg, TERM_END ", ");
    astr_push_fmt_vam(msg, fmt);
    astr_push_byte(msg, '\n');
    astr_push_byte(msg, '\n');
    log_node(sem, msg, n);
    sem->error_count++;
    return RESULT_ERROR;
}

#define ERROR_MATCH() (error_match(sem, n1, n2, t1, t2))

static Result error_match (Sem *sem, Ast *n1, Ast *n2, Type *t1, Type *t2) {
    if (NO_ERROR_REPORTING()) return RESULT_ERROR;

    MatchPair top = sem->match.top_pair;
    sem_msg(msg, LOG_ERROR);

    astr_push_cstr(msg, "Mismatch " TERM_START_CYAN);
    log_type(sem, msg, top.t1);
    astr_push_cstr(msg, TERM_END " vs " TERM_START_CYAN);
    log_type(sem, msg, top.t2);

    astr_push_cstr(msg, TERM_END ".\n\n");
    log_nodes(sem, msg, top.n1, top.n2);

    if (!(top.t1 == t1 && top.t2 == t2) && !(top.t1 == t2 && top.t2 == t1)) {
        astr_push_cstr(msg, "\nSpecifically: " TERM_START_CYAN);
        log_type(sem, msg, t1);
        astr_push_cstr(msg, TERM_END " vs " TERM_START_CYAN);
        log_type(sem, msg, t2);
        astr_push_cstr(msg, TERM_END ".\n");
    }

    if (n1 && !(top.n1 == n1 && top.n2 == n2) && !(top.n1 == n2 && top.n2 == n1)) {
        astr_push_byte(msg, '\n');
        log_nodes(sem, msg, n1, n2);
    }

    sem->error_count++;
    return RESULT_ERROR;
}

static Result match_structural (Sem *sem, Ast *n1, Ast *n2, Type *t1, Type *t2) {
    assert_dbg(sem->match.ongoing);
    assert_dbg(t1 != t2);

    if (t1->tag != t2->tag) return ERROR_MATCH();

    switch (t1->tag) {
    case TYPE_FN: {
        TypeFn *ty1   = cast(TypeFn*, t1);
        TypeFn *ty2   = cast(TypeFn*, t2);
        ArrayAst *in1 = &ty1->node->inputs;
        ArrayAst *in2 = &ty2->node->inputs;
        Ast *out1     = ty1->node->output;
        Ast *out2     = ty2->node->output;

        if (!out1 != !out2) return ERROR_MATCH();
        if (in1->count != in2->count) return ERROR_MATCH();
        array_iter (x, in1) try(match_nn(sem, x, array_get(in2, ARRAY_IDX)), return R);
        if (out1) try(match_nn(sem, out1, out2), return R);

        return RESULT_OK;
    }

    case TYPE_ARRAY: {
        TypeArray *ty1 = cast(TypeArray*, t1);
        TypeArray *ty2 = cast(TypeArray*, t2);
        return match_tt(sem, ty1->element, ty2->element);
    }

    default: return ERROR_MATCH();
    }
}

static Result match (Sem *sem, Ast **pn1, Ast **pn2, Type *t1, Type *t2) {
    if (!t1 || !t2) return RESULT_DEFER;
    if (t1 == t2)   return RESULT_OK;
    if (t1->tag == TYPE_TOP || t2->tag == TYPE_TOP) return RESULT_OK;

    Ast *n1 = *pn1;
    Ast *n2 = *pn2;

    if (! sem->match.ongoing) sem->match.top_pair = (MatchPair){n1,n2,t1,t2};
    sem->match.ongoing++;

    Result r = RESULT_DEFER;
    reach(r);
    #define RETURN(R) { r = R; goto done; }

    if ((t1->flags & TYPE_IS_DISTINCT) && !(n2->flags & AST_IS_LITERAL)) RETURN(ERROR_MATCH());
    if ((t2->flags & TYPE_IS_DISTINCT) && !(n1->flags & AST_IS_LITERAL)) RETURN(ERROR_MATCH());

    RETURN(match_structural(sem, n1, n2, t1, t2));

    done: {
        reached(r);
        #undef RETURN
        sem->match.ongoing--;
        return r;
    }
}

// The following wrappers around match() use the nomenclature:
//
//     c (constraint): Assert argument is a type expression.
//     v (value):      Assert argument is a value expression.
//     n (node):       Use argument type whether it's a value or type expression.
//     t (type):       Argument is a Type and a dummy node is used to call match().
//
static Result match_vv (Sem *sem, Ast **v1, Ast **v2) { return match(sem, v1, v2, try_get_type_v(*v1), try_get_type_v(*v2)); }
static Result match_nn (Sem *sem, Ast *n1, Ast *n2)   { return match(sem, &n1, &n2, try_get_type(n1), try_get_type(n2)); }
static Result match_nv (Sem *sem, Ast *n, Ast **v)    { return match(sem, &n, v, try_get_type(n), try_get_type_v(*v)); }
static Result match_nc (Sem *sem, Ast *n, Ast *c)     { return match(sem, &n, &c, try_get_type(n), try_get_type_t(c)); }
static Result match_tt (Sem *sem, Type *t1, Type *t2) { return match(sem, &sem->match.dummy1, &sem->match.dummy2, t1, t2); }
static Result match_tv (Sem *sem, Type *t, Ast **v)   { return match(sem, &sem->match.dummy1, v, t, try_get_type_v(*v)); }

static Void check_for_invalid_cycle_ (Sem *sem, AstTag tag, Ast *node, ArrayAst *path) {
    if (! (node->flags & AST_ADDED_TO_CHECK_LIST)) return;

    U64 prev = array_find(path, IT == node);

    if (prev == ARRAY_NIL_IDX) {
        if (node->tag == tag || node->tag == AST_IDENT) array_push(path, node);

        Ast *d = get_target(node);
        if (d && !get_type(d) && (d->tag == tag)) check_for_invalid_cycle_(sem, tag, d, path);

        #define CHECK_FOR_INVALID_CYCLE(child, ...) check_for_invalid_cycle_(sem, tag, child, path);
        AST_VISIT_CHILDREN(node, CHECK_FOR_INVALID_CYCLE);

        if (node->tag == tag || node->tag == AST_IDENT) path->count--;
    } else {
        sem_msg(msg, LOG_ERROR);
        astr_push_fmt(msg, "Invalid cycle.\n\n");
        array_iter_from (d, path, prev) log_node(sem, msg, d);
        sem_panic(sem);
    }
}

static Void check_for_invalid_cycle (Sem *sem, AstTag tag, Ast *node) {
    tmem_new(tm);
    ArrayAst path;
    array_init(&path, tm);
    check_for_invalid_cycle_(sem, tag, node, &path);
}

// This performs checks common to ops that are fusable with
// the assign op (+=, /=, ...) and their unfused counterparts.
static Result check_assign_fusable_op (Sem *sem, AstBaseBinary *n, AstTag op) {
    Type *t1 = try_get_type_v(n->op1);
    Type *t2 = try_get_type_v(n->op2);

    switch (op) {
    case AST_ADD:
    case AST_SUB:
        if (t1->tag != TYPE_INT && t1->tag != TYPE_FLOAT && t1->tag != TYPE_STRING) return error_nt(sem, n->op1, t1, "expected Int or Float type.");
        if (t2->tag != TYPE_INT && t2->tag != TYPE_FLOAT && t1->tag != TYPE_STRING) return error_nt(sem, n->op2, t2, "expected Int or Float type.");
        return RESULT_OK;

    case AST_MUL:
    case AST_DIV:
        if (t1->tag != TYPE_INT && t1->tag != TYPE_FLOAT) return error_nt(sem, n->op1, t1, "expected Int or Float type.");
        if (t2->tag != TYPE_INT && t2->tag != TYPE_FLOAT) return error_nt(sem, n->op2, t2, "expected Int or Float type.");
        return RESULT_OK;

    case AST_MOD:
        if (t1->tag != TYPE_INT) return error_nt(sem, n->op1, t1, "expected int type.");
        if (t2->tag != TYPE_INT) return error_nt(sem, n->op2, t2, "expected int type.");
        return RESULT_OK;

    default: badpath;
    }
}

// RESULT_ERROR means that it's not read only.
static Result check_is_read_only (Sem *sem, Ast *n) {
    if (n->flags & (AST_IS_READ_ONLY | AST_IS_TYPE)) return RESULT_OK;

    reach(r);
    #define RETURN(R) {\
        def1(r, acast(Result, R));\
        reached(r);\
        if (r == RESULT_OK) n->flags |= AST_IS_READ_ONLY;\
        return r;\
    }

    switch (n->tag) {
    case AST_DOT:   { Ast *d = cast(AstDot*, n)->sem_edge;   RETURN(d ? check_is_read_only(sem, d) : RESULT_DEFER); }
    case AST_IDENT: { Ast *d = cast(AstIdent*, n)->sem_edge; RETURN((d && (d->flags & AST_IS_READ_ONLY)) ? RESULT_OK : RESULT_ERROR); }
    case AST_INDEX: { Ast *l = cast(AstIndex*, n)->lhs;      RETURN(check_is_read_only(sem, l)); }
    default:        RETURN(RESULT_ERROR);
    }

    #undef RETURN
}

static Result check_call (Sem *sem, Ast *target, ArrayAst *target_args, Ast *caller, ArrayAst *call_args) {
    if (target_args->count != call_args->count) return error_nn(sem, target, caller, "Argument count in call doesn't match target fn.");

    array_iter (n1, target_args, *) {
        Ast **n2 = array_ref(call_args, ARRAY_IDX);
        Result r = match_vv(sem, n1, n2);
        if (r != RESULT_OK) return r;
    }

    return RESULT_OK;
}

// This function performs a shallow check of @node without
// recursing down the tree; therefore, a node can be marked
// checked even if some node reachable from it is not.
//
// The checks done here include the bulk of the work such
// as setting types, checking that operand types match,
// binding selectors to their targets such as identifiers
// or dot expressions, etc...
static Result check_node (Sem *sem, Ast *node) {
    switch (node->tag) {
    case AST_DUMMY:          return RESULT_OK;
    case AST_BLOCK:          return RESULT_OK;
    case AST_FILE:           return RESULT_OK;
    case AST_BUILTIN_PRINT:  return RESULT_OK;
    case AST_IF:             return match_tv(sem, sem->core_types.type_Bool, &cast(AstIf*, node)->cond);
    case AST_WHILE:          return match_tv(sem, sem->core_types.type_Bool, &cast(AstWhile*, node)->cond);
    case AST_INT_LITERAL:    set_type(node, sem->core_types.type_Int); return RESULT_OK;
    case AST_BOOL_LITERAL:   set_type(node, sem->core_types.type_Bool); return RESULT_OK;
    case AST_FLOAT_LITERAL:  set_type(node, sem->core_types.type_Float); return RESULT_OK;
    case AST_STRING_LITERAL: set_type(node, sem->core_types.type_String); return RESULT_OK;

    case AST_CALL: {
        Auto n = cast(AstCall*, node);
        Type *t = try_get_type(n->lhs);

        if (t == sem->core_types.type_CFn) {
            set_type(node, sem->core_types.type_Top);
            return RESULT_OK;
        } else {
            if (t->tag != TYPE_FN) return error_nt(sem, n->lhs, t, "expected function.");
            try_get_type_v(n->lhs); // Assert it's a value.

            AstBaseFn *fn = cast(TypeFn*, t)->node;
            set_type(node, fn->output ? try_get_type(fn->output) : sem->core_types.type_Void);
            return check_call(sem, cast(Ast*, fn), &fn->inputs, node, &n->args);
        }
    }

    case AST_RECORD: {
        Auto n = cast(AstRecord*, node);
        set_type(node, alloc_type_record(sem, n));
        return RESULT_OK;
    }

    case AST_RECORD_LITERAL: {
        Auto n = cast(AstRecordLiteral*, node);
        Type *t = try_get_type_t(n->lhs);

        if (t->tag != TYPE_RECORD) return error_nt(sem, n->lhs, t, "expected a struct.");

        set_type(node, t);

        Auto d = cast(Ast*, cast(TypeRecord*, t)->node);
        Scope *s = get_scope(d);

        tmem_new(tm);
        Map(IString*, Ast*) dedup;
        map_init(&dedup, tm);

        array_iter (i, &n->inits) {
            Ast *init = cast(Ast*, i);

            Bool found; Auto val = map_uadd(&dedup, i->name, &found);
            if (found) return error_nn(sem, *val, init, "Overriding initializers.");
            *val = init;

            Ast *d = scope_lookup_outside_in(sem, s, i->name, init);
            if (! d) return error_nn(sem, init, s->owner, "Reference to undeclared struct member.");
        }

        return RESULT_OK;
    }

    case AST_RECORD_LIT_INIT: {
        Auto n = cast(AstRecordLitInit*, node);
        Ast *d = n->sem_edge;
        return d ? match_nv(sem, d, &n->val) : RESULT_DEFER;
    }

    case AST_DOT: {
        Auto n = cast(AstDot*, node);
        Type *t = try_get_type(n->lhs);

        if (t->tag == TYPE_FFI) {
            TypeFfi *ffi = cast(TypeFfi*, t);
            VmReg reg; Bool found = map_get(&ffi->obj->record, *n->rhs, &reg);
            if (! found) return error_n(sem, node, "Reference to undeclared ffi function.");
            set_type(node, sem->core_types.type_CFn);
            return RESULT_OK;
        } else {
            if (t->tag != TYPE_RECORD) return error_n(sem, n->lhs, "Invalid lhs for dot operator.");
            try_get_type_v(n->lhs); // Assert it's a value.

            Ast *c = cast(Ast*, cast(TypeRecord*, t)->node);
            Ast *d = scope_lookup_outside_in(sem, get_scope(c), n->rhs, node);

            if (! d) return RESULT_DEFER;

            Type *dt = try_get_type(d);
            node->flags |= AST_IS_LVALUE | (d->flags & AST_IS_TYPE);
            set_type(node, dt);
            return RESULT_OK;
        }
    }

    case AST_ARRAY_LITERAL: {
        Auto n = cast(AstArrayLiteral*, node);
        Type *t = get_type(node);

        if (! t) t = set_type(node, alloc_type_array(sem, node, 0));

        Type *et;
        Ast *el;

        if (n->lhs) {
            el = n->lhs;
            et = try_get_type_t(el);
            array_iter (init, &n->inits) try(match_nc(sem, init, n->lhs));
        } else {
            el = array_get(&n->inits, 0);
            et = try_get_type_v(el);
            array_iter_from (init, &n->inits, 1, *) try(match_nv(sem, el, init));
        }

        cast(TypeArray*, t)->element = et;

        switch (et->tag) {
        case TYPE_ARRAY: break;
        case TYPE_BOOL: break;
        case TYPE_FLOAT: break;
        case TYPE_FN: break;
        case TYPE_INT: break;
        case TYPE_RECORD: break;
        case TYPE_STRING: break;
        default: return error_nt(sem, el, et, "Invalid element type for array.");
        }

        return RESULT_OK;
    }

    case AST_ARRAY_TYPE: {
        Auto n = cast(AstArrayType*, node);
        Type *elem = try_get_type_t(n->element);
        set_type(node, alloc_type_array(sem, node, elem));
        return RESULT_OK;
    }

    case AST_INDEX: {
        Auto n = cast(AstIndex*, node);
        Type *t = try_get_type(n->lhs);
        if (t->tag != TYPE_ARRAY) return error_nt(sem, n->lhs, t, "expected array type.");
        set_type(node, cast(TypeArray*, t)->element);
        node->flags |= AST_IS_LVALUE;
        return RESULT_OK;
    }

    case AST_IDENT: {
        Auto n = cast(AstIdent*, node);
        Ast *d = n->sem_edge;

        if (! d) {
            d = scope_lookup_inside_out(sem, get_scope(node), n->name, node);
            if (! d) return RESULT_DEFER;
        }

        Type *dt = try_get_type(d);

        set_type(node, dt);
        node->flags |= (d->flags & AST_IS_TYPE);
        return RESULT_OK;
    }

    case AST_VAR_DEF: {
        Auto n = cast(AstVarDef*, node);

        if ((node->flags & (AST_IS_LOCAL_VAR|AST_IS_GLOBAL_VAR)) && !(node->flags & AST_IS_FN_ARG)) {
            if (! n->init) return error_n(sem, node, "Missing initializer.");
        } else if (n->init) {
            return error_n(sem, node, "Initializer not supported here.");
        }

        if (n->init && n->constraint) {
            Type *t = try_get_type_t(n->constraint);
            try(match_nv(sem, n->constraint, &n->init));
            set_type(node, t);
        } else if (n->init) {
            Type *t = try_get_type_v(n->init);
            set_type(node, t);
        } else {
            set_type(node, try_get_type_t(n->constraint));
        }

        if ((node->flags & AST_IS_GLOBAL_VAR) && !(node->flags & AST_EVALED)) {
            return RESULT_DEFER;
        }

        return RESULT_OK;
    }

    case AST_FN: {
        Auto n = cast(AstBaseFn*, node);

        array_iter (a, &n->inputs) {
            assert_dbg(a->tag == AST_VAR_DEF);
            Ast *d = cast(AstVarDef*, a)->init;
            if (d) return error_n(sem, d, "Fn arg inits not supported yet.");
        }

        if (n->output) try_get_type_t(n->output);
        Type *t = alloc_type_fn(sem, n);
        set_type(node, t);
        return RESULT_OK;
    }

    case AST_RETURN: {
        Auto n = cast(AstReturn*, node);
        Scope *scope = scope_get_ancestor(get_scope(node), AST_FN);
        if (! scope) return error_n(sem, node, "A return can only appear inside functions.");
        Auto fn = cast(AstBaseFn*, scope->owner);
        if (!n->result != !fn->output) return error_nn(sem, cast(Ast*, fn), node, "Number of return values is not matching.");
        if (n->result) try(match_nv(sem, fn->output, &n->result));
        sem_set_target(sem, node, cast(Ast*, fn));
        return RESULT_OK;
    }

    case AST_BREAK:
    case AST_CONTINUE: {
        Scope *scope = scope_get_ancestor(get_scope(node), AST_WHILE);
        if (! scope) return error_n(sem, node, "A '%s' can only appear inside a while loop.", node->tag == AST_CONTINUE ? "continue" : "break");
        sem_set_target(sem, node, scope->owner);
        return RESULT_OK;
    }

    case AST_ASSIGN: {
        Auto n = cast(AstBaseBinary*, node);
        Type *t = try_get_type_v(n->op1);
        Result r = check_is_read_only(sem, n->op1);

        if (r == RESULT_DEFER) return r;
        if (r == RESULT_OK) return error_n(sem, n->op1, "Cannot assign to read only entity.");
        if (! (n->op1->flags & AST_IS_LVALUE)) return error_n(sem, n->op1, "Invalid assign target.");

        AstTag op = cast(AstAssign*, n)->fused_op;

        if (op != AST_ASSIGN) try(check_assign_fusable_op(sem, n, op));
        try(match_nv(sem, n->op1, &n->op2));

        set_type(node, t);
        return RESULT_OK;
    }

    case AST_NOT: {
        Auto n = cast(AstBaseUnary*, node);
        Type *t = try_get_type_v(n->op);
        if (t->tag != TYPE_BOOL) return error_nt(sem, n->op, t, "expected Bool type.");
        set_type(node, sem->core_types.type_Bool);
        return RESULT_OK;
    }

    case AST_NEGATE: {
        Auto n = cast(AstBaseUnary*, node);
        Type *t = try_get_type_v(n->op);
        if (t->tag != TYPE_INT && t->tag != TYPE_FLOAT) return error_nt(sem, n->op, t, "expected Int or Float type.");
        set_type(node, t);
        return RESULT_OK;
    }

    case AST_LOGICAL_OR:
    case AST_LOGICAL_AND: {
        Auto n = cast(AstBaseBinary*, node);
        Type *t1 = try_get_type_v(n->op1);
        Type *t2 = try_get_type_v(n->op2);
        if (t1->tag != TYPE_BOOL) return error_nt(sem, n->op1, t1, "expected Bool type.");
        if (t2->tag != TYPE_BOOL) return error_nt(sem, n->op2, t2, "expected Bool type.");
        set_type(node, sem->core_types.type_Bool);
        return RESULT_OK;
    }

    case AST_LESS:
    case AST_GREATER:
    case AST_LESS_EQUAL:
    case AST_GREATER_EQUAL: {
        Auto n = cast(AstBaseBinary*, node);
        Type *t = try_get_type_v(n->op1);
        if (t->tag != TYPE_INT && t->tag != TYPE_FLOAT) return error_nt(sem, n->op1, t, "expected int or float type.");
        try(match_vv(sem, &n->op1, &n->op2));
        set_type(node, sem->core_types.type_Bool);
        return RESULT_OK;
    }

    case AST_EQUAL:
    case AST_NOT_EQUAL: {
        Auto n = cast(AstBaseBinary*, node);
        Type *t1 = try_get_type_v(n->op1);
        Type *t2 = try_get_type_v(n->op2);
        if (! (t1->flags & TYPE_CAN_BE_IN_REG)) return error_nt(sem, n->op1, t1, "expected primitive type.");
        if (! (t2->flags & TYPE_CAN_BE_IN_REG)) return error_nt(sem, n->op2, t2, "expected primitive type.");
        try(match_vv(sem, &n->op1, &n->op2));
        set_type(node, sem->core_types.type_Bool);
        return RESULT_OK;
    }

    case AST_MOD:
    case AST_MUL:
    case AST_DIV:
    case AST_ADD:
    case AST_SUB: {
        Auto n = cast(AstBaseBinary*, node);
        Type *t = try_get_type_v(n->op1);
        try(check_assign_fusable_op(sem, n, node->tag));
        try(match_vv(sem, &n->op1, &n->op2));
        set_type(node, t);
        return RESULT_OK;
    }

    default: break;
    }

    badpath;
}

// This is the entry point for semantically analyzing an ast.
// It will recursively add the entire ast into the analyzer.
static Void add_to_check_list (Sem *sem, Ast *n, Scope *scope) {
    if (!n || (n->flags & AST_ADDED_TO_CHECK_LIST)) return;
    n->flags |= AST_ADDED_TO_CHECK_LIST;

    set_scope(n, scope);

    switch (n->tag) {
    #define X(TAG, T) case TAG: if (cast(T*, n)->name) scope_add(sem, scope, cast(T*, n)->name, n, n); break;
        EACH_STATIC_NAME_GENERATOR(X)
    #undef X
    default: break;
    }

    if (n->tag == AST_FN) array_push(&sem->fns, cast(AstFn*, n));
    if (n->flags & AST_IS_GLOBAL_VAR) array_push(&sem->globals, n);
    if (n->flags & AST_CREATES_SCOPE) scope = scope_new(sem, scope, n);
    if ((n->flags & AST_MUST_EVAL) && !(n->flags & AST_EVALED)) array_push(&sem->eval_list, n);

    #define ADD_TO_CHECK_LIST(child, ...) add_to_check_list(sem, child, scope);
    AST_VISIT_CHILDREN(n, ADD_TO_CHECK_LIST);

    if ((n->flags & AST_CREATES_SCOPE)) scope_seal(sem, scope);
    array_push(&sem->check_list, n);
}

static Void check_nodes (Sem *sem) {
    while (true) {
        sem->found_a_sem_edge = false;
        U64 prev_to_check = sem->check_list.count;

        array_iter (n, &sem->check_list) {
            if (check_node(sem, n) == RESULT_OK) {
                n->flags |= AST_CHECKED;
                if (! get_type(n)) set_type(n, sem->core_types.type_Void);
            }

            if (sem->error_count) sem_panic(sem);
        }

        array_iter (n, &sem->eval_list) {
            eval(sem, n);
            if (sem->error_count) sem_panic(sem);
        }

        Bool new_to_check = (prev_to_check < sem->check_list.count);
        Bool checked      = sem->check_list.count - array_find_remove_all(&sem->check_list, IT->flags & AST_CHECKED);
        Bool evaled       = sem->eval_list.count  - array_find_remove_all(&sem->eval_list, IT->flags & AST_EVALED);

        if (!sem->found_a_sem_edge && !new_to_check && !checked && !evaled) break;
    }

    if (sem->check_list.count) error_no_progress(sem);
}

SemProgram *sem_check (Sem *sem, String main_file_path) {
    IString *path  = intern_str(sem->interns, main_file_path);
    AstFile *file  = import_file(sem, path, 0);
    IString *entry = sem->interns->entry_fn_name;

    sem->main_fn = cast(AstFn*, array_find_get(&file->statements, (IT->tag == AST_FN) && (cast(AstFn*, IT)->name == entry)));

    if (! sem->main_fn) {
        sem_msg(msg, LOG_ERROR)
        astr_push_fmt(msg, "No entry function [%.*s] in main file.\n\n", STR(*entry));
        sem_panic(sem);
    }

    check_nodes(sem);

    Auto prog = mem_new(sem->mem, SemProgram);
    prog->sem     = sem;
    prog->fns     = sem->fns;
    prog->types   = sem->types;
    prog->entry   = cast(Ast*, sem->main_fn);
    prog->globals = sem->globals;
    return prog;
}

Sem *sem_new (Mem *mem, Vm *vm, Interns *interns) {
    Sem *sem = mem_new(mem, Sem);
    sem->mem = mem;
    sem->vm = vm;
    sem->interns = interns;
    sem->parser = par_new(mem, interns);

    array_init(&sem->fns, mem);
    array_init(&sem->types, mem);
    array_init(&sem->globals, mem);
    array_init(&sem->eval_list, mem);
    array_init(&sem->check_list, mem);

    map_init(&sem->files, mem);
    map_init(&sem->global_to_reg, mem);

    { // Init autoimports scope:
        Ast *owner = ast_alloc(mem, AST_DUMMY, AST_CREATES_SCOPE);
        sem->autoimports = scope_new(sem, 0, owner);
        scope_seal(sem, sem->autoimports);
        add_to_check_list(sem, owner, sem->autoimports);
    }

    sem->match.dummy1 = ast_alloc(sem->mem, AST_DUMMY, 0);
    sem->match.dummy2 = ast_alloc(sem->mem, AST_DUMMY, 0);
    add_to_check_list(sem, sem->match.dummy1, sem->autoimports);
    add_to_check_list(sem, sem->match.dummy2, sem->autoimports);

    { // Init core types:
        #define init(N, TAG) {\
            Type *t = alloc_type(sem, TAG);\
            Ast *n = ast_alloc(sem->mem, AST_DUMMY, AST_IS_TYPE);\
            add_to_check_list(sem, n, sem->autoimports);\
            set_type(n, t);\
            sem->core_types.type_##N = t;\
            scope_add(sem, sem->autoimports, intern_cstr(sem->interns, #N), n, n);\
        }

        init(CFn, TYPE_FN);
        init(Top, TYPE_TOP);
        init(Int, TYPE_INT);
        init(Bool, TYPE_BOOL);
        init(Void, TYPE_VOID);
        init(Float, TYPE_FLOAT);
        init(String, TYPE_STRING);

        #undef init
    }

    // Add ffi functions to the autoimports scope:
    array_iter (it, &vm->ffi, *) {
        Type *t = alloc_type(sem, TYPE_FFI);
        cast(TypeFfi*, t)->name = it->name;
        cast(TypeFfi*, t)->obj  = it->obj; // @todo Can we get rid of this and use sem_get_const_val() instead?

        Ast *n = ast_alloc(sem->mem, AST_DUMMY, AST_IS_GLOBAL_VAR|AST_MUST_EVAL|AST_EVALED);
        add_to_check_list(sem, n, sem->autoimports);
        set_type(n, t);
        scope_add(sem, sem->autoimports, intern_str(sem->interns, it->name), n, n);
        set_const_val(sem, n, (VmReg){ .tag=VM_REG_OBJ, .obj=cast(VmObj*, it->obj) });
    }

    return sem;
}

static Void set_const_val (Sem *sem, Ast *node, VmReg reg) {
    map_add(&sem->global_to_reg, node->id, reg);
}

VmReg sem_get_const_val (Sem *sem, Ast *node) {
    VmReg reg = {};
    map_get(&sem->global_to_reg, node->id, &reg);
    return reg;
}

SemCoreTypes *sem_get_core_types (Sem *sem) {
    return &sem->core_types;
}
