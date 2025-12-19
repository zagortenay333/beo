#include "compiler/sem.h"
#include "compiler/vm.h"
#include "compiler/parser.h"

istruct (PolyInfo) {
    U64 mark;
    Ast *node;
    ArrayAst *args;
    ArrayAst polyargs;
    ArrayAst instances;
};

istruct (MonoInfo);

istruct (ValueInstance) {
    TypeVar *var;
    Ast **val;
    Ast *instance;
};

istruct (TypeInstance) {
    TypeVar *var;
    Type *t;
    Ast *instance;
    MonoInfo *i;
};

istruct (MonoInfo) {
    U64 depth;
    Ast *instantiator;
    PolyInfo *poly_info;
    SliceAst arg_instances; // Parallel to poly_info->args.
    Array(TypeInstance) type_map;
    Array(ValueInstance) value_map;
    Array(struct { Ast *oldn; Ast *newn; }) instance_map;
};

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

istruct (PendingCast) {
    Ast *to;
    Ast **from;
    Type *to_type;
};

istruct (UntypedLit) {
    Ast *lit;
    Ast *bind;
    Type *tvar;
};

ienum (Subtype, U8) {
    SUBTYPE_ANY_WAY, // (A > B) or (A < B)
    SUBTYPE_ONE_WAY, // (A > B)
    SUBTYPE_TWO_WAY, // (A > B) and (A < B)
};

istruct (Sem) {
    Mem *mem;
    Vm *vm;
    Parser *parser;
    Interns *interns;
    SemCoreTypes core_types;

    AstFn *main_fn;
    ArrayAstFn fns;
    ArrayType types;
    ArrayAst globals;

    Scope *autoimports;
    Map(IString*, AstFile*) files;

    ArrayAst eval_list;
    ArrayAst check_list;
    Array(struct { Ast *from, *to; }) infer_list;

    U64 error_count;
    U64 next_type_id;
    Bool found_a_sem_edge;
    PolyInfo *poly_info;

    Map(TypeId, Ast*) type_def;
    Map(AstId, VmReg) global_to_reg;
    Map(AstId, MonoInfo*) mono_infos;
    Map(AstId, PolyInfo*) poly_infos;

    struct { // Info about ongoing match().
        U64 ongoing;
        Ast *dummy1;
        Ast *dummy2;
        Bool applied_cast;
        MatchPair top_pair;
        U64 without_error_reporting;
    } match;

    struct { // Info about ongoing check_call().
        Bool ongoing;
        Bool bound_var_to_var;
        Bool bound_var_to_val;
        Array(MonoInfo*) mono_infos;
        Array(MonoInfo*) mono_infos_pool;
        ArrayType simple_untyped_lits;
        Array(PendingCast) casts;
        Array(UntypedLit) untyped_lits;
        Array(struct { MonoInfo *i1; MonoInfo *i2; Ast *a; Ast *b; }) values_to_match;

        // These vars act as implicit arguments to match functions
        // that deal with tvar_types and tvar_values. They must be
        // maintained in pop/push or swap/unswap fashion.
        //
        //     Result match_* (Sem *sem, Type *t1, Type *t2) {}
        //                                     ^^--i1    ^^--i2
        MonoInfo *i1, *i2;
    } call_check;
};

static Ast *get_target (Ast *node);
static Result match_vv (Sem *sem, Ast **v1, Ast **v2);
static Result match_nn (Sem *sem, Ast *n1, Ast *n2);
static Result match_nv (Sem *sem, Ast *n, Ast **v);
static Result match_nc (Sem *sem, Ast *n, Ast *c);
static Result match_tt (Sem *sem, Type *t1, Type *t2);
static Result match_tv (Sem *sem, Type *t, Ast **v);
static Result match_structural (Sem *sem, Ast *n1, Ast *n2, Type *t1, Type *t2);
static Result match (Sem *sem, Ast **pn1, Ast **pn2, Type *t1, Type *t2, Subtype subtype);
static Void add_to_infer_list (Sem *sem, Ast *from, Ast *to);
MonoInfo *sem_get_mono_info (Sem *sem, Ast *node);
static Ast *instantiate_poly_arg (Sem *sem, Ast *arg, MonoInfo *info, Ast *instance);
static Bool check_sequence_returns (Sem *sem, ArrayAst *seq);
static Void set_const_val (Sem *sem, Ast *node, VmReg reg);
static Void add_to_check_list (Sem *sem, Ast *n, Scope *scope);
static Void check_for_invalid_cycle (Sem *sem, AstTag tag, Ast *node);
static Result error_n Fmt(3, 4) (Sem *sem, Ast *n, CString fmt, ...);
static Result error_nn Fmt(4, 5) (Sem *sem, Ast *n1, Ast *n2, CString fmt, ...);
static Result match_tuples (Sem *sem, AstTuple *tup1, AstTuple *tup2, Type *t1, Type *t2, Subtype subtype);
static Result check_call (Sem *sem, Ast *target, ArrayAst *target_args, Ast *caller, ArrayAst *call_args, Bool);

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
#define MAX_RECURSIVE_INSTANTIATIONS 1024

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

inl Bool is_tvar (Type *t)             { return (t->tag == TYPE_VAR) || (t->flags & TYPE_IS_UNTYPED_LIT); }
inl Bool is_tvar_fn (Type *t)          { return (t->flags & TYPE_IS_TVAR_FN); }
inl Bool is_tvar_dot (Type *t)         { return (t->tag == TYPE_VAR) && (cast(TypeVar*, t)->node->tag == AST_DOT); }
inl Bool is_tvar_call (Type *t)        { return (t->tag == TYPE_VAR) && (cast(TypeVar*, t)->node->tag == AST_CALL); }
inl Bool is_tvar_type (Type *t)        { return (t->tag == TYPE_VAR) && (cast(TypeVar*, t)->node->tag == AST_ARG_POLY_TYPE); }
inl Bool is_tvar_value (Type *t)       { return (t->tag == TYPE_VAR) && (cast(TypeVar*, t)->node->tag == AST_ARG_POLY_VALUE); }
inl Bool is_tvar_array_lit (Type *t)   { return (t->tag == TYPE_ARRAY) && (t->flags & TYPE_IS_UNTYPED_LIT); }
inl Bool is_tvar_tuple_lit (Type *t)   { return (t->tag == TYPE_TUPLE) && (t->flags & TYPE_IS_UNTYPED_LIT); }

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

static Bool type_has_polyargs (Type *type) {
    switch (type->tag) {
    case TYPE_FN:      { Ast *n = cast(Ast*, cast(TypeFn*, type)->node); return n->flags & AST_HAS_POLY_ARGS; }
    case TYPE_ARRAY:   { Ast *n = cast(Ast*, cast(TypeArray*, type)->node); return n->flags & AST_HAS_POLY_ARGS; }
    case TYPE_TUPLE:   { Ast *n = cast(Ast*, cast(TypeTuple*, type)->node); return n->flags & AST_HAS_POLY_ARGS; }
    case TYPE_RECORD:  { Ast *n = cast(Ast*, cast(TypeRecord*, type)->node); return n->flags & AST_HAS_POLY_ARGS; }
    case TYPE_OPTION:  { Type *t = cast(TypeOption*, type)->underlying; return type_has_polyargs(t); }
    case TYPE_BOOL:    return false;
    case TYPE_ENUM:    return false;
    case TYPE_FLOAT:   return false;
    case TYPE_INT:     return false;
    case TYPE_TOP:     return false;
    case TYPE_FFI:     return false;
    case TYPE_STRING:  return false;
    case TYPE_VOID:    return false;
    case TYPE_MISC:    return false;
    case TYPE_VAR:     return true;
    }
    badpath;
}

static Ast *get_type_constructor (Type *type) {
    switch (type->tag) {
    case TYPE_ARRAY:   return cast(Ast*, cast(TypeArray*, type)->node);
    case TYPE_FN:      return cast(Ast*, cast(TypeFn*, type)->node);
    case TYPE_OPTION:  return cast(Ast*, cast(TypeOption*, type)->node);
    case TYPE_RECORD:  return cast(Ast*, cast(TypeRecord*, type)->node);
    case TYPE_TUPLE:   return cast(Ast*, cast(TypeTuple*, type)->node);
    case TYPE_VAR:     return cast(Ast*, cast(TypeVar*, type)->node);
    case TYPE_INT:     return 0;
    case TYPE_MISC:    return 0;
    case TYPE_STRING:  return 0;
    case TYPE_FFI:     return 0;
    case TYPE_TOP:     return 0;
    case TYPE_BOOL:    return 0;
    case TYPE_ENUM:    return 0;
    case TYPE_FLOAT:   return 0;
    case TYPE_VOID:    return 0;
    }
    badpath;
}

static Type *get_underlying_from_distinct_type (Sem *sem, Type *t) {
    Auto n = cast(AstTypeDistinct*, map_get_assert(&sem->type_def, t->id));
    return get_type(n->val);
}

static IString *get_name (Ast *node) {
    switch (node->tag) {
    #define X(TAG, TYPE) case TAG: return cast(TYPE*, node)->name;
        EACH_STATIC_NAME_GENERATOR(X)
    #undef X

    case AST_IDENT: return cast(AstIdent*, node)->name;
    default: badpath;
    }
}

static Ast *get_init (Ast *node) {
    switch (node->tag) {
    case AST_VAR_DEF:        return cast(AstVarDef*, node)->init;
    case AST_ARG_POLY_TYPE:  return cast(AstArgPolyType*, node)->init;
    case AST_ARG_POLY_VALUE: return cast(AstArgPolyValue*, node)->init;
    default:                 return 0;
    }
}

// Top call should have allow_local_var = false.
static Result can_eval_ (Sem *sem, Ast *node, Bool allow_local_var) {
    if (! (node->flags & AST_CHECKED)) return RESULT_DEFER;
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

    #define V(child, ...) try(can_eval_(sem, child, allow_local_var), RETURN(R));\

    AST_VISIT_CHILDREN(node, V);

    Ast *d = get_target(node);
    if (d) {
        if ((d->flags & AST_IS_LOCAL_VAR) && !allow_local_var) RETURN(error_nn(sem, node, d, "Cannot compile-time eval local variable."));
        V(d);
    }

    node->flags |= AST_CAN_EVAL;
    RETURN(RESULT_OK);

    #undef V
    #undef RETURN
}

static Result can_eval (Sem *sem, Ast *node) {
    Result result = can_eval_(sem, node, false);

    if (result == RESULT_OK) {
        Type *t = get_type(node);

        again: switch (t->tag) {
        case TYPE_BOOL: break;
        case TYPE_FLOAT: break;
        case TYPE_INT: break;
        case TYPE_STRING: break;
        case TYPE_VOID: break;
        case TYPE_ENUM: break;

        case TYPE_FN:
        case TYPE_FFI:
        case TYPE_TOP:
        case TYPE_VAR:
        case TYPE_MISC: {
            result = RESULT_ERROR;
        } break;

        case TYPE_OPTION: {
            t = cast(TypeOption*, t)->underlying;
            goto again;
        }

        case TYPE_ARRAY: {
            Type *elem = cast(TypeArray*, t)->element;
            if (! (elem->flags & TYPE_IS_PRIMITIVE)) result = RESULT_ERROR;
        } break;

        case TYPE_TUPLE: {
            AstTuple *tup = cast(TypeTuple*, t)->node;
            array_iter (m, &tup->members) {
                if (! (get_type(m)->flags & TYPE_IS_PRIMITIVE)) {
                    result = RESULT_ERROR;
                    break;
                }
            }
        } break;

        case TYPE_RECORD: {
            AstRecord *rec = cast(TypeRecord*, t)->node;
            array_iter (m, &rec->members) {
                if (! (get_type(m)->flags & TYPE_IS_PRIMITIVE)) {
                    result = RESULT_ERROR;
                    break;
                }
            }
        } break;
        }
    }

    return (result == RESULT_ERROR) ?
           error_n(sem, node, "Only expressions with type primitive, string, or array/record of primitive types can eval at compile time.") :
           result;
}

static Void collect_program_ (SemProgram *prog, Ast *node) {
    if (node->flags & AST_VISITED) return;
    node->flags |= AST_VISITED;

    assert_dbg(node->flags & AST_CAN_EVAL);

    if (node->flags & AST_IS_GLOBAL_VAR) array_push(&prog->globals, node);
    if (node->tag == AST_FN) array_push(&prog->fns, cast(AstFn*, node));

    Type *t = get_type(node);
    if (t && !(t->flags & TYPE_VISITED)) {
        t->flags |= TYPE_VISITED;
        array_push(&prog->types, t);
    }

    #define V(child, ...) collect_program_(prog, child)

    AST_VISIT_CHILDREN(node, V);

    Ast *d = get_target(node);
    if (d) V(d);

    node->flags &= ~AST_VISITED;
    #undef V
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
    case AST_ADD:           return BINOP(add);
    case AST_DIV:           return BINOP(div);
    case AST_EQUAL:         return BINOP(equal);
    case AST_GREATER:       return BINOP(greater);
    case AST_GREATER_EQUAL: return BINOP(greater_equal);
    case AST_LESS:          return BINOP(less);
    case AST_LESS_EQUAL:    return BINOP(less_equal);
    case AST_MOD:           return BINOP(mod);
    case AST_MUL:           return BINOP(mul);
    case AST_NOT_EQUAL:     return BINOP(mod);
    case AST_SUB:           return BINOP(mod);
    case AST_NEGATE:        return UNOP(negate);
    case AST_NOT:           return UNOP(not);
    case AST_INT_LITERAL:   return (VmReg){ .tag=VM_REG_INT, .i64=cast(AstIntLiteral*, node)->val };
    case AST_BOOL_LITERAL:  return (VmReg){ .tag=VM_REG_BOOL, .boolean=cast(AstBoolLiteral*, node)->val };
    case AST_FLOAT_LITERAL: return (VmReg){ .tag=VM_REG_FLOAT, .f64=cast(AstFloatLiteral*, node)->val };
    case AST_IDENT:         return ast_eval(sem, cast(AstIdent*, node)->sem_edge);
    case AST_VAR_DEF:       return ast_eval(sem, cast(AstVarDef*, node)->init);
    case AST_ENUM_FIELD:    return sem_get_const_val(sem, node);
    case AST_BUILTIN_LINE:  return (VmReg){ .tag=VM_REG_INT, .i64=cast(I64, node->pos.first_line) };
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
    try(can_eval(sem, node));

    VmReg val = ast_eval(sem, node);

    if (val.tag == VM_REG_NIL) { // We need to run the expression inside a VM.
        tmem_new(tm);
        tmem_pin(tm, 0);

        SemProgram *prog = collect_program(sem, node, tm);

        // We have to construct an AST for an imaginary entry function.
        // Right now we dont bother constructing the return signature
        // AST node because the the backend doesn't need one, but it
        // still feels kind of sketchy.
        if (prog->entry->tag != AST_FN) {
            AstFile *file  = get_file(prog->entry);
            String fn_name = astr_fmt(tm, "global_var_wrapper:%.*s:%lu", STR(*file->path), prog->entry->pos.first_line);

            Ast *fn  = ast_alloc(tm, AST_FN, 0);
            Ast *ret = ast_alloc(tm, AST_RETURN, 0);

            fn->pos  = prog->entry->pos;
            ret->pos = prog->entry->pos;

            cast(AstFn*, fn)->name = intern_str(sem->interns, fn_name);

            cast(AstReturn*, ret)->sem_edge = fn;
            cast(AstReturn*, ret)->result = (prog->entry->tag == AST_VAR_DEF) ? cast(AstVarDef*, prog->entry)->init : prog->entry;
            array_push(&cast(AstFn*, fn)->statements, ret);

            array_push(&prog->fns, cast(AstFn*, fn));
            prog->entry = fn;
        }

        Vm *vm = vm_new(tm);
        vm_compile_prog(vm, prog);
        Bool ok = vm_run(vm);

        if (ok) {
            val = vm_transfer_result(sem->vm, vm);
            vm_destroy(vm);
        } else {
            vm_destroy(vm);
            return error_n(sem, node, "Unable to compile-time eval expression.");
        }
    }

    set_const_val(sem, node, val);
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

static Type *alloc_type_var (Sem *sem, Ast *n, TypeFlags f) {
    Auto *t = cast(TypeVar*, alloc_type(sem, TYPE_VAR));
    t->node = n;
    cast(Type*, t)->flags |= f;
    return cast(Type*, t);
}

static Type *alloc_type_misc (Sem *sem, Ast *n) {
    Auto t = cast(TypeMisc*, alloc_type(sem, TYPE_MISC));
    t->node = n;
    return cast(Type*, t);
}

static Type *alloc_type_option (Sem *sem, Type *underlying, Ast *node) {
    Auto t = cast(TypeOption*, alloc_type(sem, TYPE_OPTION));
    t->node = node;
    t->underlying = underlying;
    return cast(Type*, t);
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

static Type *alloc_type_tuple (Sem *sem, AstTuple *n) {
    Auto t = cast(TypeTuple*, alloc_type(sem, TYPE_TUPLE));
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

AstFile *sem_get_file (Sem *sem, Ast *node) {
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

Scope *sem_scope_get_ancestor (Scope *s, AstTag tag) {
    for (; s; s = s->parent) if (s->owner->tag == tag) return s;
    return 0;
}

static Scope *scope_of_instance (Ast *node) {
    for (Scope *s = get_scope(node); s && s->owner; s = s->parent) {
        if (s->owner->flags & AST_IS_POLYMORPH_INSTANCE) return s;
    }
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

    if (type->flags & TYPE_IS_DISTINCT) {
        Auto n = cast(AstTypeDistinct*, map_get_assert(&sem->type_def, type->id));
        astr_push_fmt(astr, "%.*s", STR(*n->name));
        type->flags &= ~TYPE_VISITED;
        return;
    }

    switch (type->tag) {
    case TYPE_TOP:    astr_push_cstr(astr, "Top"); break;
    case TYPE_BOOL:   astr_push_cstr(astr, "Bool"); break;
    case TYPE_VOID:   astr_push_cstr(astr, "Void"); break;
    case TYPE_FLOAT:  astr_push_cstr(astr, "Float"); break;
    case TYPE_INT:    astr_push_cstr(astr, "Int"); break;
    case TYPE_STRING: astr_push_cstr(astr, "String"); break;

    case TYPE_VAR: {
        Ast *n = cast(TypeVar*, type)->node;

        if (n->tag == AST_FN_POLY) {
            IString *name = cast(AstFnPoly*, n)->name;
            astr_push_fmt(astr, "%.*s", STR(*name));
        } else if (n->tag == AST_CALL) {
            IString *name = get_name(cast(AstCall*, n)->sem_edge);
            astr_push_fmt(astr, "%.*s(", STR(*name));
            array_iter (arg, &cast(AstCall*, n)->args) {
                log_type(sem, astr, get_type(arg));
                if (! ARRAY_ITER_DONE) astr_push_cstr(astr, ", ");
            }
            astr_push_byte(astr, ')');
        } else if (is_tvar_type(type)) {
            IString *name = get_name(cast(TypeVar*, type)->node);
            astr_push_fmt(astr, "$%.*s", STR(*name));
        } else {
            astr_push_cstr(astr, "$");
        }
    } break;

    case TYPE_MISC: {
        astr_push_cstr(astr, "Type(");
        astr_push_cstr(astr, ast_tag_to_cstr[cast(TypeMisc*, type)->node->tag]);
        astr_push_byte(astr, ')');
    } break;

    case TYPE_ENUM: {
        IString *name = cast(TypeRecord*, type)->node->name;
        astr_push_fmt(astr, "enum %.*s", STR(*name));
    } break;

    case TYPE_OPTION: {
        astr_push_byte(astr, '?');
        log_type(sem, astr, cast(TypeOption*, type)->underlying);
    } break;

    case TYPE_FFI: {
        String name = cast(TypeFfi*, type)->name;
        astr_push_fmt(astr, "ffi %.*s", STR(name));
    } break;

    case TYPE_TUPLE: {
        Auto t = cast(TypeTuple*, type);
        astr_push_cstr(astr, "(");
        array_iter (m, &t->node->members) {
            log_type(sem, astr, get_type(m));
            if (! ARRAY_ITER_DONE) astr_push_cstr(astr, ", ");
        }
        astr_push_cstr(astr, ")");
    } break;

    case TYPE_RECORD: {
        IString *name = cast(TypeRecord*, type)->node->name;
        astr_push_fmt(astr, "record %.*s", STR(*name));
    } break;

    case TYPE_ARRAY: {
        Auto t = cast(TypeArray*, type);
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

static Void log_poly_trace (Sem *sem, AString *astr, Ast *node) {
    Scope *scope = scope_of_instance(node);
    if (! scope) return;

    astr_push_cstr(astr, "\nPolymorph instantiation trace:\n\n");

    U64 margin = slog_default_config->left_margin;

    while (scope) {
        MonoInfo *info = sem_get_mono_info(sem, scope->owner);
        AstFile *file  = get_file(info->instantiator);

        astr_push_fmt(astr, "%*s" TERM_RED("FILE") ": (byte=%lu, line=%lu, file=", cast(Int,margin), "", info->instantiator->pos.offset, info->instantiator->pos.first_line);
        astr_push_str_quoted(astr, *file->path);

        if (info->type_map.count) {
            astr_push_byte(astr, ' ');
            array_iter (x, &info->type_map, *) {
                IString *n = get_name(x->var->node);
                astr_push_fmt(astr, "%.*s=", STR(*n));
                log_type(sem, astr, x->t);
                if (! ARRAY_ITER_DONE) astr_push_cstr(astr, ", ");
            }
        }

        astr_push_cstr(astr, ")");
        scope = scope_of_instance(info->instantiator);
        if (scope) astr_push_byte(astr, '\n');
    }

    astr_push_byte(astr, '\n');
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
        if (!get_type(n) && ((n->tag == AST_VAR_DEF) || (n->tag == AST_TYPE_ALIAS) || (n->tag == AST_TYPE_DISTINCT))) {
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
    log_poly_trace(sem, msg, n);
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
    log_poly_trace(sem, msg, n2);
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
    log_poly_trace(sem, msg, n);
    sem->error_count++;
    return RESULT_ERROR;
}

static Result error_unbound_polyvars (Sem *sem, Ast *caller, Ast *target) {
    assert_dbg(sem->call_check.ongoing);
    if (NO_ERROR_REPORTING()) return RESULT_ERROR;

    tmem_new(tm);
    sem_msg(msg, LOG_ERROR);
    SrcLog *slog = slog_new(tm, slog_default_config);

    astr_push_cstr(msg, "Unable to bind all poly variables.\n\n");
    log_nodes(sem, msg, caller, target);

    astr_push_cstr(msg, "\nHere are the unbound variables:\n\n");
    array_iter (info, &sem->call_check.mono_infos) {
        array_iter (x, &info->type_map, *)  if (!x->t || is_tvar_type(x->t)) log_node_no_flush(sem, slog, msg, get_type_constructor(cast(Type*, x->var)));
        array_iter (x, &info->value_map, *) if (! x->val) log_node_no_flush(sem, slog, msg, get_type_constructor(cast(Type*, x->var)));
    }

    slog_flush(slog, msg);
    log_poly_trace(sem, msg, caller);
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

static Void implicit_cast (Sem *sem, Ast **pn, Ast *to, Type *to_type) {
    Ast *n = *pn;

    if (sem->call_check.ongoing) {
        assert_dbg((to != sem->match.dummy1) && (to != sem->match.dummy2));
        PendingCast *found = array_find_ref(&sem->call_check.casts, (IT->to == to) && (IT->from == pn));
        if (! found) array_push_lit(&sem->call_check.casts, .to=to, .to_type=to_type, .from=pn);
    } else {
        Ast *c = ast_alloc(sem->mem, AST_CAST, 0);
        c->pos = n->pos;
        c->flags |= (n->flags & (AST_MUST_EVAL|AST_IS_LITERAL));
        cast(AstCast*, c)->expr = n;

        add_to_check_list(sem, c, get_scope(n));
        set_type(c, to_type);

        *pn = c;
        sem->match.applied_cast = true;
    }
}

MonoInfo *sem_get_mono_info (Sem *sem, Ast *node) {
    return map_get_ptr(&sem->mono_infos, node->id);
}

static PolyInfo *get_poly_info (Sem *sem, Ast *node) {
    return map_get_ptr(&sem->poly_infos, node->id);
}

static MonoInfo *alloc_mono_info (Sem *sem, Ast *polymorph, Ast *instantiator) {
    assert_dbg(polymorph->flags & (AST_IS_POLYMORPH | AST_IS_MACRO));

    MonoInfo *info = array_pop_or(&sem->call_check.mono_infos_pool, 0);

    if (info) {
        info->type_map.count     = 0;
        info->value_map.count    = 0;
        info->instance_map.count = 0;
    } else {
        info = mem_new(sem->mem, MonoInfo);
        array_init(&info->type_map, sem->mem);
        array_init(&info->value_map, sem->mem);
        array_init(&info->instance_map, sem->mem);
    }

    info->poly_info    = get_poly_info(sem, polymorph);
    info->instantiator = instantiator;
    array_push(&sem->call_check.mono_infos, info);

    array_iter (n, &info->poly_info->polyargs) {
        TypeVar *t = cast(TypeVar*, get_type(n));
        if (n->tag == AST_ARG_POLY_TYPE) array_push_lit(&info->type_map, .var=t);
        else                             array_push_lit(&info->value_map, .var=t);
    }

    return info;
}

static PolyInfo *alloc_poly_info (Sem *sem, Ast *polymorph) {
    PolyInfo *info = mem_new(sem->mem, PolyInfo);

    if (polymorph->tag == AST_RECORD_POLY) {
        info->args = &cast(AstRecordPoly*, polymorph)->args;
    } else {
        assert_dbg(ast_get_base_flags[polymorph->tag] & AST_BASE_FN);
        info->args = &cast(AstBaseFn*, polymorph)->inputs;
    }

    info->node = polymorph;
    array_init(&info->polyargs, sem->mem);
    array_init(&info->instances, sem->mem);
    map_add(&sem->poly_infos, polymorph->id, info);
    return info;
}

static Void bind_simple_untyped_lit (Sem *sem, Type *t) {
    assert_dbg(is_tvar_array_lit(t) || is_tvar_tuple_lit(t));

    if (sem->call_check.ongoing) {
        array_push(&sem->call_check.simple_untyped_lits, t);
    } else {
        t->flags &= ~TYPE_IS_UNTYPED_LIT;
    }
}

static Void bind_simple_untyped_lit_recursively (Sem *sem, Type *t) {
    if (is_tvar_array_lit(t)) {
        t->flags &= ~TYPE_IS_UNTYPED_LIT;
        AstArrayLiteral *lit = cast(AstArrayLiteral*, cast(TypeArray*, t)->node);
        array_iter (x, &lit->inits) bind_simple_untyped_lit_recursively(sem, get_type(x));
    } else if (is_tvar_tuple_lit(t)) {
        t->flags &= ~TYPE_IS_UNTYPED_LIT;
        array_iter (x, &cast(TypeTuple*, t)->node->members) bind_simple_untyped_lit_recursively(sem, get_type(x));
    }
}

// This is a type variable assigned to a record call whose
// arguments contain type variables:
//
//     record Foo ($T) {}
//
//     fn foo (x: Foo($T)) {}
//                ^^^^^^^------ tvar_call
//
// Instead of instantiating a struct with type vars, we assign
// a type variable to the invocation itself and match against
// it structurally.
static Result match_tvar_call (Sem *sem, Ast *n1, Ast **pn2, Type *t1, Type *t2) {
    assert_dbg(sem->match.ongoing);
    assert_dbg(is_tvar_call(t1));
    assert_dbg(cast(TypeVar*, t1)->node->tag == AST_CALL);

    Ast *n2 = *pn2;
    AstCall *call = cast(AstCall*, cast(TypeVar*, t1)->node);
    Ast *target = get_target(call->lhs);

    if (is_tvar_call(t2)) {
        AstCall *call2 = cast(AstCall*, cast(TypeVar*, t2)->node);
        if (target != get_target(call2->lhs)) return ERROR_MATCH();

        array_iter (a, &call->args, *) {
            Ast **b = array_ref(&call2->args, ARRAY_IDX);
            match_nn(sem, *a, *b);
        }

        return RESULT_OK;
    }

    if (t2->tag == TYPE_RECORD) {
        Ast *poly = get_target(call->lhs);
        MonoInfo *info = sem_get_mono_info(sem, cast(Ast*, cast(TypeRecord*, t2)->node));
        ArrayAst *args = &cast(AstCall*, info->instantiator)->args;

        if (!info || (info->poly_info->node != poly)) return ERROR_MATCH();

        array_iter (a, &call->args, *) {
            Ast **b = array_ref(args, ARRAY_IDX);
            match_nn(sem, *a, *b);
        }

        return RESULT_OK;
    }

    return ERROR_MATCH();
}

// Match a polymorphic function to the variable it is
// being assigned to via the assignment operator or
// by being passed as argument to a fn:
//
//     fn foo (x: $T) -> T {}
//     x = foo;
//         ^^^-------------------- assignment via identifier
//     bar(fn (x: $T) {});
//         ^^^^^^^^^^^^^---------- assignment via fn literal
//
static Result match_tvar_fn (Sem *sem, Ast *n1, Ast *n2, Type *t1, Type *t2) {
    assert_dbg(sem->match.ongoing);
    assert_dbg(is_tvar_fn(t1));

    if (t2->tag != TYPE_FN) return ERROR_MATCH();

    AstBaseFn *fn = cast(TypeFn*, t2)->node;
    Ast *instantiator = cast(TypeVar*, t1)->node;
    assert_dbg(instantiator->tag == AST_IDENT || instantiator->tag == AST_FN_POLY);

    if (! sem->call_check.ongoing) {
        ArrayAst a1 = { .data=cast(Ast**, &fn), .count=1, .capacity=1 };
        ArrayAst a2 = { .data=&instantiator, .count=1, .capacity=1 };
        return check_call(sem, cast(Ast*, fn), &a1, instantiator, &a2, false);
    }

    AstBaseFn *poly_fn = (instantiator->tag == AST_FN_POLY) ? cast(AstBaseFn*, instantiator ): cast(AstBaseFn*, get_target(instantiator));
    if ((poly_fn->inputs.count != fn->inputs.count) || (!!poly_fn->output != !!fn->output)) return ERROR_MATCH();

    MonoInfo *prev_m1 = sem->call_check.i1;
    sem->call_check.i1 = array_find_get(&sem->call_check.mono_infos, IT->instantiator == instantiator);
    if (! sem->call_check.i1) sem->call_check.i1 = alloc_mono_info(sem, cast(Ast*, poly_fn), instantiator);

    reach(r);
    #define RETURN(R) { reached(r); sem->call_check.i1 = prev_m1; return R; }

    array_iter (a, &poly_fn->inputs) try(match_nn(sem, a, array_get(&fn->inputs, ARRAY_IDX)), RETURN(R));
    if (fn->output) try(match_nn(sem, poly_fn->output, fn->output), RETURN(R));

    RETURN(RESULT_OK);
    #undef RETURN
}

// Array literals not in standalone position have a variable
// type so that we can implicitly cast it's inits to the type
// of the expression that the array literal is being matched
// against. For example:
//
//     var x: []?Int = [42, 420];
//                     ^^^^^^^^^---- tvar_array_lit
//
static Result match_tvar_array_lit (Sem *sem, Ast *n1, Ast **pn2, Type *t1, Type *t2) {
    assert_dbg(sem->match.ongoing);
    assert_dbg(is_tvar_array_lit(t2));

    Ast *n2 = *pn2;
    AstArrayLiteral *lit = cast(AstArrayLiteral*, cast(TypeArray*, t2)->node);
    Ast **init0 = array_ref(&lit->inits, 0);

    if (is_tvar_array_lit(t1)) {
        AstArrayLiteral *lit1 = cast(AstArrayLiteral*, cast(TypeArray*, t1)->node);
        if (lit->inits.count != lit1->inits.count) return ERROR_MATCH();
        try(match_vv(sem, array_ref(&lit1->inits, 0), init0));
        bind_simple_untyped_lit(sem, t1);
        bind_simple_untyped_lit(sem, t2);
        return RESULT_OK;
    }

    if (t1->tag == TYPE_ARRAY) {
        TypeArray *a = cast(TypeArray*, t1);

        if (a->node->tag == AST_ARRAY_TYPE) {
            try(match_nv(sem, cast(AstArrayType*, a->node)->element, init0));
        } else {
            try(match_tv(sem, a->element, init0));
        }

        bind_simple_untyped_lit(sem, t2);
        return RESULT_OK;
    }

    return ERROR_MATCH();
}

// Tuple literals not in standalone position have variable
// type for the same reason outlined in match_tvar_array_lit().
static Result match_tvar_tuple_lit (Sem *sem, Ast *n1, Ast **pn2, Type *t1, Type *t2) {
    assert_dbg(sem->match.ongoing);
    assert_dbg(is_tvar_tuple_lit(t2));

    Ast *n2 = *pn2;
    AstTuple *lit = cast(TypeTuple*, t2)->node;

    if (is_tvar_tuple_lit(t1)) {
        try(match_tuples(sem, cast(TypeTuple*, t1)->node, lit, t1, t2, SUBTYPE_ANY_WAY));
        bind_simple_untyped_lit(sem, t1);
        bind_simple_untyped_lit(sem, t2);
        return RESULT_OK;
    }

    if (t1->tag == TYPE_TUPLE) {
        try(match_tuples(sem, cast(TypeTuple*, t1)->node, lit, t1, t2, SUBTYPE_ONE_WAY));
        bind_simple_untyped_lit(sem, t2);
        return RESULT_OK;
    }

    return ERROR_MATCH();
}

static Type *get_tvar_type (MonoInfo *info, TypeVar *var, MonoInfo **out_info) {
    assert_dbg(is_tvar_type(cast(Type*, var)));
    if (! info) return 0;
    TypeInstance *e = array_find_ref(&info->type_map, IT->var == var);
    if (!e->t || is_tvar_type(e->t)) return 0;
    if (out_info) *out_info = e->i;
    return e->t;
}

static Void set_tvar_type (Sem *sem, MonoInfo *i1, MonoInfo *i2, TypeVar *var, Type *t) {
    assert_dbg(is_tvar_type(cast(Type*, var)));
    TypeInstance *e = array_find_ref(&i1->type_map, IT->var == var);
    e->t   = t;
    e->i   = i2;
    if (is_tvar_type(t)) sem->call_check.bound_var_to_var = true;
    else                 sem->call_check.bound_var_to_val = true;
}

// Match against a polymorphic type argument:
//
//        fn foo ($T, x: $R) {}
//                ^^-----^^------------ tvar_type
//
static Result match_tvar_type (Sem *sem, Ast *n1, Ast *n2, Type *t1, Type *t2) {
    assert_dbg(sem->match.ongoing);
    assert_dbg(is_tvar_type(t1));
    if (t2->tag == TYPE_MISC) return ERROR_MATCH();
    set_tvar_type(sem, sem->call_check.i1, sem->call_check.i2, cast(TypeVar*, t1), t2);
    if (is_tvar_type(t2)) set_tvar_type(sem, sem->call_check.i2, sem->call_check.i1, cast(TypeVar*, t2), t1);
    return RESULT_OK;
}

static Result match_tvar (Sem *sem, Ast **pn1, Ast **pn2, Type *t1, Type *t2, Subtype subtype) {
    assert_dbg(sem->match.ongoing);
    assert_dbg(is_tvar(t1) || is_tvar(t2));

    Ast *n1 = *pn1;
    Ast *n2 = *pn2;
    MonoInfo *prev_m1 = sem->call_check.i1;
    MonoInfo *prev_m2 = sem->call_check.i2;

    if (is_tvar_type(t1)) { Type *t = get_tvar_type(sem->call_check.i1, cast(TypeVar*, t1), &sem->call_check.i1); t1 = t ? t : t1; }
    if (is_tvar_type(t2)) { Type *t = get_tvar_type(sem->call_check.i2, cast(TypeVar*, t2), &sem->call_check.i2); t2 = t ? t : t2; }

    Result r;
    reach(r);
    #define RETURN(R)   { r = R; goto done; }
    #define RETURN_S(R) { swap(sem->call_check.i1, sem->call_check.i2); RETURN(R); }

    if (t1 == t2)                     RETURN(RESULT_OK);
    if (!is_tvar(t1) && !is_tvar(t2)) RETURN(match(sem, pn1, pn2, t1, t2, subtype));
    if (is_tvar_type(t1))             RETURN(match_tvar_type(sem, n1, n2, t1, t2));
    if (is_tvar_type(t2))             RETURN_S(match_tvar_type(sem, n2, n1, t2, t1));
    if (is_tvar_array_lit(t2))        RETURN(match_tvar_array_lit(sem, n1, pn2, t1, t2));
    if (is_tvar_array_lit(t1))        RETURN_S(match_tvar_array_lit(sem, n2, pn1, t2, t1));
    if (is_tvar_call(t1))             RETURN(match_tvar_call(sem, n1, pn2, t1, t2));
    if (is_tvar_call(t2))             RETURN_S(match_tvar_call(sem, n2, pn1, t2, t1));
    if (is_tvar_tuple_lit(t2))        RETURN(match_tvar_tuple_lit(sem, n1, pn2, t1, t2));
    if (is_tvar_tuple_lit(t1))        RETURN_S(match_tvar_tuple_lit(sem, n2, pn1, t2, t1));
    if (is_tvar_fn(t1))               RETURN(match_tvar_fn(sem, n1, n2, t1, t2));
    if (is_tvar_fn(t2))               RETURN_S(match_tvar_fn(sem, n2, n1, t2, t1));

    badpath;

    done: {
        sem->call_check.i1 = prev_m1;
        sem->call_check.i2 = prev_m2;
        #undef RETURN
        #undef RETURN_S
        reached(r);
        return r;
    }
}

static Result match_substructural (Sem *sem, Ast *n1, Ast **pn2, Type *t1, Type *t2) {
    assert_dbg(sem->match.ongoing);
    assert_dbg(t1 != t2);

    Ast *n2 = *pn2;

    reach(r);
    #define RETURN(R, ...) {\
        def1(r, R);\
        reached(r);\
        __VA_OPT__(if (false)) if (r == RESULT_OK) implicit_cast(sem, pn2, n1, t1);\
        return r;\
    }

    switch (t1->tag) {
    case TYPE_OPTION: {
        Type *underlying = cast(TypeOption*, t1)->underlying;

        if (t2->tag == TYPE_OPTION) {
            RETURN(match_structural(sem, n1, n2, t1, t2), NOCAST);
        } else if (n2->tag == AST_NIL) {
            RETURN(RESULT_OK);
        } else {
            RETURN(match_tt(sem, underlying, t2));
        }
    }

    default: RETURN(match_structural(sem, n1, n2, t1, t2), NOCAST);
    }

    #undef RETURN
}

static Result match_tuples (Sem *sem, AstTuple *tup1, AstTuple *tup2, Type *t1, Type *t2, Subtype subtype) {
    Auto ty1 = cast(TypeTuple*, t1);
    Auto ty2 = cast(TypeTuple*, t2);

    Ast *n1 = cast(Ast*, tup1);
    Ast *n2 = cast(Ast*, tup2);

    if (ty1->node->members.count != ty2->node->members.count) return ERROR_MATCH();

    array_iter (m1, &ty1->node->members, *) {
        Ast **m2 = array_ref(&ty2->node->members, ARRAY_IDX);
        try(match(sem, m1, m2, get_type(*m1), get_type(*m2), subtype));
    }

    return RESULT_OK;
}

static Result match_structural (Sem *sem, Ast *n1, Ast *n2, Type *t1, Type *t2) {
    assert_dbg(sem->match.ongoing);
    assert_dbg(t1 != t2);

    if (t1->tag != t2->tag) return ERROR_MATCH();

    switch (t1->tag) {
    case TYPE_OPTION: {
        Type *u1 = cast(TypeOption*, t1)->underlying;
        Type *u2 = cast(TypeOption*, t2)->underlying;
        return match_tt(sem, u1, u2);
    }

    case TYPE_FN: {
        Auto ty1      = cast(TypeFn*, t1);
        Auto ty2      = cast(TypeFn*, t2);
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

    case TYPE_TUPLE: {
        return match_tuples(sem, cast(TypeTuple*, t1)->node, cast(TypeTuple*, t2)->node, t1, t2, SUBTYPE_TWO_WAY);
    }

    case TYPE_ARRAY: {
        TypeArray *ty1 = cast(TypeArray*, t1);
        TypeArray *ty2 = cast(TypeArray*, t2);
        return match_tt(sem, ty1->element, ty2->element);
    }

    default: return ERROR_MATCH();
    }
}

// This function can cause one of the nodes to be implicitly casted,
// which is done by writing through the double pointer.
//
// For the sake of simplifying the calling code, this function will
// return RESULT_DEFER if it performs an implicit cast. That way
// the caller doesn't have to worry about having stored the wrong
// pointer in a local variable.
static Result match (Sem *sem, Ast **pn1, Ast **pn2, Type *t1, Type *t2, Subtype subtype) {
    Ast *n1 = *pn1;
    Ast *n2 = *pn2;

    repeat:

    if (!t1 || !t2) return RESULT_DEFER;
    if (t1 == t2)   return RESULT_OK;
    if (t1->tag == TYPE_TOP || t2->tag == TYPE_TOP) return RESULT_OK;

    if (t1->flags & TYPE_IS_DISTINCT) {
        if (! (n2->flags & AST_IS_LITERAL)) {
            sem->match.top_pair = (MatchPair){n1,n2,t1,t2};
            return ERROR_MATCH();
        }

        t1 = get_underlying_from_distinct_type(sem, t1);
        goto repeat;
    }

    if (t2->flags & TYPE_IS_DISTINCT) {
        if (! (n1->flags & AST_IS_LITERAL)) {
            sem->match.top_pair = (MatchPair){n1,n2,t1,t2};
            return ERROR_MATCH();
        }

        t2 = get_underlying_from_distinct_type(sem, t2);
        goto repeat;
    }

    if (! sem->match.ongoing) sem->match.top_pair = (MatchPair){n1,n2,t1,t2};
    sem->match.ongoing++;

    Result r = RESULT_DEFER;
    reach(r);
    #define RETURN(R) { r = R; goto done; }

    if (is_tvar(t1) || is_tvar(t2)) RETURN(match_tvar(sem, pn1, pn2, t1, t2, subtype));
    if (subtype == SUBTYPE_TWO_WAY) RETURN(match_structural(sem, n1, n2, t1, t2));
    if (subtype == SUBTYPE_ONE_WAY) RETURN(match_substructural(sem, n1, pn2, t1, t2));

    sem->match.without_error_reporting++;
    r = match_substructural(sem, n1, pn2, t1, t2);
    sem->match.without_error_reporting--;

    if (r == RESULT_ERROR) {
        // swap(sem->call_check.i1, sem->call_check.i2);
        r = match_substructural(sem, n2, pn1, t2, t1);
        // swap(sem->call_check.i1, sem->call_check.i2);
    }

    done: {
        reached(r);
        #undef RETURN
        sem->match.ongoing--;
        if (!sem->match.applied_cast) return r;
        sem->match.applied_cast = 0;
        return RESULT_DEFER;
    }
}

// The following wrappers around match() use the nomenclature:
//
//     c (constraint): Assert argument is a type expression.
//     v (value):      Assert argument is a value expression.
//     n (node):       Use argument type whether it's a value or type expression.
//     t (type):       Argument is a Type and a dummy node is used to call match().
//
// These functions also make specific choices for the subtype relation.
static Result match_vv (Sem *sem, Ast **v1, Ast **v2) { return match(sem, v1, v2, try_get_type_v(*v1), try_get_type_v(*v2), SUBTYPE_ANY_WAY); }
static Result match_nn (Sem *sem, Ast *n1, Ast *n2)   { return match(sem, &n1, &n2, try_get_type(n1), try_get_type(n2), SUBTYPE_TWO_WAY); }
static Result match_nv (Sem *sem, Ast *n, Ast **v)    { return match(sem, &n, v, try_get_type(n), try_get_type_v(*v), SUBTYPE_ONE_WAY); }
static Result match_nc (Sem *sem, Ast *n, Ast *c)     { return match(sem, &n, &c, try_get_type(n), try_get_type_t(c), SUBTYPE_TWO_WAY); }
static Result match_tt (Sem *sem, Type *t1, Type *t2) { return match(sem, &sem->match.dummy1, &sem->match.dummy2, t1, t2, SUBTYPE_TWO_WAY); }
static Result match_tv (Sem *sem, Type *t, Ast **v)   { return match(sem, &sem->match.dummy1, v, t, try_get_type_v(*v), SUBTYPE_ONE_WAY); }

static IString *instantiate_poly_name (Sem *sem, IString *base, Ast *instantiator, U64 n) {
    IString *path = get_file(instantiator)->path;
    String name   = astr_fmt(sem->mem, "%.*s:%.*s:%lu:%lu", STR(*base), STR(*path), instantiator->pos.first_line, n);
    return intern_str(sem->interns, name);
}

static Ast *instantiate_poly_arg_helper (Ast *old_node, Ast *new_node, Void *context) {
    Auto sem      = cast(Sem*, cast(Void**, context)[0]);
    Auto info     = cast(MonoInfo*, cast(Void**, context)[1]);
    Auto instance = cast(Ast*, cast(Void**, context)[2]);

    if (new_node) {
        new_node->flags &= ~(AST_IN_POLY_ARG_POSITION | AST_HAS_POLY_ARGS);
        if (old_node->flags & AST_HAS_POLY_ARGS) array_push_lit(&info->instance_map, .oldn=old_node, .newn=new_node);
        if (old_node->tag == AST_DOT) new_node->flags &= ~AST_IS_TYPE;
        if ((old_node->tag == AST_CAST) && !cast(AstCast*, old_node)->to) {
            assert_dbg(! (old_node->flags & AST_IN_POLY_ARG_POSITION));
            add_to_infer_list(sem, old_node, new_node);
        }
        return 0;
    } else {
        switch (old_node->tag) {
        case AST_ARG_POLY_TYPE:  return instantiate_poly_arg(sem, old_node, info, instance);
        // case AST_ARG_POLY_CODE:  return instantiate_poly_arg(sem, old_node, info, instance);
        // case AST_ARG_POLY_VALUE: return instantiate_poly_arg(sem, old_node, info, instance);
        default:                 return 0;
        }
    }
}

static Ast *instantiate_poly_arg (Sem *sem, Ast *arg, MonoInfo *info, Ast *instance) {
    Scope *instance_scope = get_scope(instance);

    switch (arg->tag) {
    case AST_VAR_DEF: {
        AstVarDef *n = cast(AstVarDef*, arg);
        Ast *r = ast_alloc(sem->mem, AST_VAR_DEF, 0);
        r->flags |= AST_IS_LOCAL_VAR;
        r->flags |= AST_IS_FN_ARG;

        r->pos = arg->pos;
        cast(AstVarDef*, r)->name = n->name;
        if (arg->flags & AST_HAS_POLY_ARGS) array_push_lit(&info->instance_map, .oldn=arg, .newn=r);

        if (n->constraint) {
            Void *ctx [] = { sem, info, instance };
            cast(AstVarDef*, r)->constraint = ast_deep_copy(sem->mem, n->constraint, instantiate_poly_arg_helper, ctx);
        } else {
            Ast *c = ast_alloc(sem->mem, AST_DUMMY, AST_IS_TYPE);
            c->pos = n->init->pos;
            add_to_check_list(sem, c, instance_scope);
            set_type(c, get_type(n->init));
            cast(AstVarDef*, r)->constraint = c;
        }

        if (instance->tag == AST_FN) array_push(&cast(AstBaseFn*, instance)->inputs, r);
        add_to_check_list(sem, r, instance_scope);
        return r;
    }

    case AST_ARG_POLY_TYPE: {
        TypeVar *t = cast(TypeVar*, get_type(arg));
        TypeInstance *b = array_find_ref(&info->type_map, IT->var == t);
        Ast *c = get_type_constructor(b->t);
        Ast *r = ast_alloc(sem->mem, AST_DUMMY, AST_IS_POLYMORPH_INSTANCE | AST_IS_TYPE | AST_EVALED);

        if (c) b->t = get_type(c);
        b->instance = r;
        r->pos = arg->pos;
        add_to_check_list(sem, r, instance_scope);
        scope_add(sem, instance_scope, cast(AstArgPolyType*, arg)->name, r, r);
        array_push_lit(&info->instance_map, .oldn=arg, .newn=r);

        if (! type_has_polyargs(b->t)) {
            set_type(r, b->t);
            bind_simple_untyped_lit_recursively(sem, b->t);
        }

        return r;
    }

    #if 0
    case AST_ARG_POLY_VALUE: {
        AstArgPolyValue *n = cast(AstArgPolyValue*, arg);
        TypeVar *t = cast(TypeVar*, get_type(arg));
        ValueInstance *b = array_find_ref(&info->value_map, IT->var == t);
        Ast *r = ast_alloc(sem->mem, AST_VAR_DEF, AST_IS_POLYMORPH_INSTANCE | AST_CAN_EVAL);

        r->pos = arg->pos;
        cast(AstVarDef*, r)->name = n->name;
        Void *ctx [] = { sem, info, instance };
        cast(AstVarDef*, r)->constraint = (n->constraint->tag == AST_DUMMY) ? n->constraint : ast_deep_copy(sem->mem, n->constraint, instantiate_poly_arg_helper, ctx);

        b->instance = r;
        add_to_check_list(sem, r, instance_scope);
        array_push_lit(&info->instance_map, .oldn=arg, .newn=r);
        assert_dbg(b->val);
        map_add(&sem->node_to_val, r->id, (Value){ .ptr=b->val });
        return r;
    }

    case AST_ARG_POLY_CODE: {
        TypeVar *t = cast(TypeVar*, get_type(arg));
        ValueInstance *b = array_find_ref(&info->value_map, IT->var == t);
        Ast *r = ast_alloc(sem->mem, AST_CALL_MACRO_ARG, 0);

        r->pos = arg->pos;
        cast(AstCallMacroArg*, r)->code = ((AstCallMacroArg*)*b->val)->code;
        cast(AstCallMacroArg*, r)->parsed_ast = ((AstCallMacroArg*)*b->val)->parsed_ast;

        b->instance = r;
        add_to_check_list(sem, r, instance_scope);
        scope_add(sem, instance_scope, cast(AstArgPolyCode*, arg)->name, r, r);
        array_push_lit(&info->instance_map, .oldn=arg, .newn=r);
        return r;
    }
    #endif

    default: badpath;
    }
}

static Ast *instantiate_polymorph (Sem *sem, MonoInfo *info, MonoInfo **out_instance_info) {
    assert_dbg(sem->call_check.ongoing);

    Ast *polymorph      = info->poly_info->node;
    ArrayAst *instances = &info->poly_info->instances;
    AstFlags is_macro   = (polymorph->flags & AST_IS_MACRO) ? AST_IS_MACRO_INSTANCE : 0;

    if (! is_macro) { // Look for a cached instance:
        sem->match.without_error_reporting++;
        MonoInfo *prev = sem->call_check.i1;
        sem->call_check.i1 = info;

        array_iter (prev_instance, instances) {
            MonoInfo *prev_info = sem_get_mono_info(sem, prev_instance);

            array_iter (a, &info->type_map, *) {
                TypeInstance *b = array_ref(&prev_info->type_map, ARRAY_IDX);
                Result r = match_tt(sem, a->t, b->t);
                assert_dbg(r != RESULT_DEFER);
                if (r != RESULT_OK) goto continue_outer;
            }

            // array_iter (a, &info->value_map, *) {
                // Ast *b = *array_ref(&prev_info->value_map, ARRAY_IDX)->val;
                // Type *t = get_type(b);
                // if (! (t->flags & TYPE_IS_PRIMITIVE)) goto continue_outer;
                // if (! vm_value_match(t, get_const(sem, info, *a->val, 0), sem_get_const(sem, b))) goto continue_outer;
            // }

            sem->call_check.i1 = prev;
            sem->match.without_error_reporting--;
            *out_instance_info = prev_info;
            return prev_instance;
            continue_outer:;
        }

        sem->call_check.i1 = prev;
        sem->match.without_error_reporting--;
    }

    AstTag tag     = (polymorph->tag == AST_RECORD_POLY) ? AST_RECORD : AST_FN;
    Ast *fn_output = (tag == AST_FN) ? cast(AstBaseFn*, polymorph)->output : 0;
    Ast *instance  = ast_alloc(sem->mem, tag, AST_IS_POLYMORPH_INSTANCE | is_macro);
    instance->pos  = polymorph->pos;

    // @todo What about attributes?? We are not copying those at all.

    if (tag == AST_FN) {
        AstFnPoly *p = cast(AstFnPoly*, polymorph);
        cast(AstFn*, instance)->name = instantiate_poly_name(sem, p->name, info->instantiator, instances->count);
        if (fn_output && (fn_output->tag != AST_ARG_POLY_TYPE)) cast(AstBaseFn*, instance)->output = ast_deep_copy(sem->mem, fn_output, 0, 0);
        array_iter (s, &p->statements) {
            Ast *copy = ast_deep_copy(sem->mem, s, 0, 0);
            array_push(&cast(AstFn*, instance)->statements, copy);
        }
    } else {
        assert_dbg(tag == AST_RECORD);
        AstRecordPoly *p = cast(AstRecordPoly*, polymorph);
        cast(AstRecord*, instance)->name = instantiate_poly_name(sem, p->name, info->instantiator, instances->count);
        array_iter (f, &p->members) {
            Ast *copy = ast_deep_copy(sem->mem, f, 0, 0);
            array_push(&cast(AstRecord*, instance)->members, copy);
        }
    }

    add_to_check_list(sem, instance, get_scope(is_macro ? info->instantiator : polymorph));
    map_add(&sem->mono_infos, instance->id, info);
    array_push(instances, instance);

    ArrayAst arg_instances;
    array_init(&arg_instances, sem->mem);
    array_iter (arg, info->poly_info->args) array_push(&arg_instances, instantiate_poly_arg(sem, arg, info, instance));
    if (fn_output && (fn_output->tag == AST_ARG_POLY_TYPE)) cast(AstBaseFn*, instance)->output = instantiate_poly_arg(sem, fn_output, info, instance);
    info->arg_instances = slice_from(&arg_instances, SliceAst);

    *out_instance_info = info;
    return instance;
}

static Result check_call_args_layout (Sem *sem, Ast *target, ArrayAst *target_args, Ast *caller, ArrayAst *call_args) {
    if (call_args->count > target_args->count) {
        return error_nn(sem, caller, target, "Too many call args. Got %lu, but expected %lu.", call_args->count, target_args->count);
    }

    array_ensure_count(call_args, target_args->count, true);

    // Reorder named arguments:
    array_iter (arg, call_args) {
        if (!arg || arg->tag != AST_CALL_NAMED_ARG) continue;

        IString *name = cast(AstCallNamedArg*, arg)->name;
        U64 def = array_find(target_args, get_name(IT) == name);

        if (def == ARRAY_NIL_IDX) return error_nn(sem, arg, target, "Referencing unknown argument");
        if (def == ARRAY_IDX) continue;

        Ast *arg2 = array_get(call_args, def);
        if (arg2 && (arg2->tag != AST_CALL_NAMED_ARG || name == cast(AstCallNamedArg*, arg2)->name)) {
            return error_nn(sem, arg, arg2, "Duplicate call args.");
        }

        array_swap(call_args, def, ARRAY_IDX);
        ARRAY_IDX--; // To stay on current index next iteration.
    }

    // Insert missing default arguments:
    array_iter (arg, call_args) {
        if (arg) {
            if (arg->tag == AST_CALL_NAMED_ARG) array_set(call_args, ARRAY_IDX, cast(AstCallNamedArg*, arg)->arg);
            continue;
        }

        Ast *def  = array_get(target_args, ARRAY_IDX);
        Ast *init = get_init(def);

        if (! init) return error_nn(sem, def, caller, "Argument does not have default value and is omitted from call.");

        Ast *n    = ast_alloc(sem->mem, AST_CALL_DEFAULT_ARG, 0);
        n->pos    = caller->pos;
        n->flags |= (def->flags & AST_IS_TYPE);

        if (init->flags & AST_MUST_EVAL) {
            cast(AstCallDefaultArg*, n)->arg = init;
        } else {
            // :NoCheckPolyArgInit
            Ast *arg = ast_deep_copy(sem->mem, init, 0, 0);
            arg->flags |= AST_MUST_EVAL;
            cast(AstCallDefaultArg*, n)->arg = arg;
            add_to_check_list(sem, arg, get_scope(def));
        }

        add_to_check_list(sem, n, get_scope(caller));
        array_set(call_args, ARRAY_IDX, n);
    }

    if (call_args->count > 254) return error_n(sem, caller, "Max number of arguments to a function is 254.");
    return RESULT_OK;
}

static Result check_call (Sem *sem, Ast *target, ArrayAst *target_args, Ast *caller, ArrayAst *call_args, Bool check_layout) {
    Auto c = &sem->call_check;

    assert_dbg(! c->i1);
    assert_dbg(! c->ongoing);

    if (target->flags & AST_IS_POLYMORPH) {
        PolyInfo *poly_info = get_poly_info(sem, target);

        array_iter_from (i, &poly_info->instances, poly_info->mark) {
            MonoInfo *info = sem_get_mono_info(sem, i);
            array_iter (x, &info->type_map, *)  try_get_type(x->instance);
            array_iter (x, &info->value_map, *) if (! (x->instance->flags & AST_EVALED)) return RESULT_DEFER;
            poly_info->mark++;
        }
    }

    if (check_layout) try(check_call_args_layout(sem, target, target_args, caller, call_args));
    if (target->flags & (AST_IS_POLYMORPH | AST_IS_MACRO)) c->i1 = alloc_mono_info(sem, target, caller);

    Result r = RESULT_OK;
    reach(r);
    #define RETURN(R) { r = R; goto done; }

    c->ongoing          = true;
    c->bound_var_to_var = true;
    c->bound_var_to_val = true;

    while (c->bound_var_to_var && c->bound_var_to_val) {
        c->bound_var_to_var = false;
        c->bound_var_to_val = false;

        array_iter (argt, target_args) {
            Ast **argc = array_ref(call_args, ARRAY_IDX);
            r = (argt->tag == AST_ARG_POLY_TYPE) ? match_nc(sem, argt, *argc) : match_nv(sem, argt, argc);
            if (r != RESULT_OK) RETURN(r);
        }
    }

    array_iter (info, &c->mono_infos) {
        if (array_find_ref(&info->value_map, !IT->val)) RETURN(error_unbound_polyvars(sem, caller, target));
        if (array_find_ref(&info->type_map, !IT->t || is_tvar_type(IT->t))) RETURN(error_unbound_polyvars(sem, caller, target));
    }

    // array_iter (x, &c->values_to_match, *) {
        // Type *t1; Value v1 = get_const(sem, x->i1, x->a, &t1);
        // Type *t2; Value v2 = get_const(sem, x->i2, x->b, &t2);
        // if (! vm_value_match(t1, v1, v2)) RETURN(error_nn(sem, x->a, x->b, "Value mismatch."));
    // }

    array_iter (info, &c->mono_infos) {
        Scope *parent_instance = scope_of_instance(info->instantiator);
        if (! parent_instance) continue;
        MonoInfo *parent_info = sem_get_mono_info(sem, parent_instance->owner);
        if (parent_info->depth >= MAX_RECURSIVE_INSTANTIATIONS) RETURN(error_n(sem, info->instantiator, "Too many recursive instantiations."));
        info->depth = parent_info->depth + 1;
    }

    array_iter (info, &c->mono_infos) {
        MonoInfo *instance_info = 0;
        Ast *instance = instantiate_polymorph(sem, info, &instance_info);

        if (instance_info != info) { // Cached instance used, so this MonoInfo is obsolete.
            array_remove_fast(&c->mono_infos, ARRAY_IDX);
            ARRAY_IDX--; // Because of the remove above.
            array_iter (i, &c->mono_infos) array_iter (x, &i->type_map, *) if (x->i == info) x->i = instance_info;
        }

        array_iter (i, &instance_info->instance_map, *) {
            array_iter (x, &c->untyped_lits, *) if (i->oldn == x->bind) { x->bind = i->newn; break; }
            array_iter (x, &c->casts, *) {
                if (i->oldn != x->to) continue;
                x->to = (i->oldn->tag == AST_ARG_POLY_VALUE) ? cast(AstVarDef*, i->newn)->constraint : i->newn;
                break;
            }
        }

        if (info != c->i1) {
            map_add(&sem->mono_infos, info->instantiator->id, info);
            add_to_infer_list(sem, instance, info->instantiator);
        }

        sem_set_target(sem, info->instantiator, instance);
    }

    array_iter (info, &c->mono_infos) {
        array_iter (x, &info->type_map, *) {
            if (get_type(x->instance)) continue;
            Ast *c = get_type_constructor(x->t);
            Type *t = get_type(c);
            Ast *b = is_tvar_fn(t) ? get_target(cast(TypeVar*, t)->node) : (x->i ? array_find_ref(&x->i->instance_map, IT->oldn == c)->newn : c);
            add_to_infer_list(sem, b, x->instance);
        }
    }

    done: {
        c->ongoing = false;

        if (r == RESULT_OK) {
            array_iter (x, &c->casts, *)            implicit_cast(sem, x->from, x->to, x->to_type);
            array_iter (x, &c->untyped_lits, *)     add_to_infer_list(sem, x->bind, x->lit);
            array_iter (x, &c->simple_untyped_lits) x->flags &= ~TYPE_IS_UNTYPED_LIT;
        } else {
            array_iter (x, &c->untyped_lits, *) set_type(x->lit, x->tvar);
            array_push_many(&c->mono_infos_pool, &c->mono_infos);
        }

        c->i1 = 0;
        c->i2 = 0;
        c->casts.count = 0;
        c->mono_infos.count = 0;
        c->untyped_lits.count = 0;
        c->values_to_match.count = 0;
        c->simple_untyped_lits.count = 0;

        #undef RETURN
        reached(r);
        return r;
    }
}

static Void check_for_invalid_cycle_ (Sem *sem, AstTag tag, Ast *node, ArrayAst *path) {
    if (! (node->flags & AST_ADDED_TO_CHECK_LIST)) return;

    U64 prev = array_find(path, IT == node);

    if (prev == ARRAY_NIL_IDX) {
        if (node->tag == tag || node->tag == AST_IDENT) array_push(path, node);

        Ast *d = get_target(node);
        if (d && !get_type(d) && (d->tag == tag)) check_for_invalid_cycle_(sem, tag, d, path);

        #define V(child, ...) check_for_invalid_cycle_(sem, tag, child, path);
        AST_VISIT_CHILDREN(node, V);
        #undef V

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

static Bool check_statement_returns (Sem *sem, Ast *node) {
    switch (node->tag) {
    case AST_RETURN: return true;
    case AST_BLOCK:  return check_sequence_returns(sem, &cast(AstBlock*, node)->statements);
    case AST_IF: {
        Auto n = cast(AstIf*, node);
        if (! n->else_arm) return false;
        return check_statement_returns(sem, n->then_arm) && check_statement_returns(sem, n->else_arm);
    }
    default: return false;
    }
}

// @todo If we later add codegen, this function will have to be
// updated to iterate a bit more carefully. The same is true
// for a number of other undocumented places...
static Bool check_sequence_returns (Sem *sem, ArrayAst *seq) {
    array_iter (stmt, seq) {
        if (! check_statement_returns(sem, stmt)) continue;

        if (! ARRAY_ITER_DONE) {
            array_iter_from (stmt, seq, ARRAY_IDX+1) {
                switch (stmt->tag) {
                case AST_FN:
                case AST_RECORD:
                case AST_TYPE_ALIAS:
                case AST_TYPE_DISTINCT:
                    break;
                default:
                    error_n(sem, stmt, "Unreachable code.");
                }
            }
        }

        return true;
    }

    return false;
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
    case AST_NIL:            return RESULT_OK;
    case AST_BLOCK:          return RESULT_OK;
    case AST_FILE:           return RESULT_OK;
    case AST_BUILTIN_PRINT:  return RESULT_OK;
    case AST_CALL_NAMED_ARG: return RESULT_OK;
    case AST_IF:             return match_tv(sem, sem->core_types.type_Bool, &cast(AstIf*, node)->cond);
    case AST_WHILE:          return match_tv(sem, sem->core_types.type_Bool, &cast(AstWhile*, node)->cond);
    case AST_INT_LITERAL:    set_type(node, sem->core_types.type_Int); return RESULT_OK;
    case AST_BOOL_LITERAL:   set_type(node, sem->core_types.type_Bool); return RESULT_OK;
    case AST_FLOAT_LITERAL:  set_type(node, sem->core_types.type_Float); return RESULT_OK;
    case AST_STRING_LITERAL: set_type(node, sem->core_types.type_String); return RESULT_OK;

    case AST_BUILTIN_VAL: {
        Auto n = cast(AstBaseUnary*, node);
        Type *t = try_get_type_v(n->op);
        if (t->tag != TYPE_OPTION) return error_nt(sem, node, t, "expected an Option type.");
        set_type(node, cast(TypeOption*, t)->underlying);
        return RESULT_OK;
    }

    case AST_BUILTIN_IS_NIL: {
        Auto n = cast(AstBaseUnary*, node);
        Type *t = try_get_type_v(n->op);
        if (t->tag != TYPE_OPTION) return error_nt(sem, node, t, "expected an Option type.");
        set_type(node, sem->core_types.type_Bool);
        return RESULT_OK;
    }

    case AST_BUILTIN_FN_NAME: {
        Scope *fn_scope = sem_scope_get_ancestor(get_scope(node), AST_FN);
        if (! fn_scope) return error_n(sem, node, "The builtin .fn_name() must appear inside a function.");
        set_type(node, sem->core_types.type_String);
        return RESULT_OK;
    }

    case AST_BUILTIN_LINE: {
        set_type(node, sem->core_types.type_Int);
        return RESULT_OK;
    }

    case AST_BUILTIN_FILE: {
        set_type(node, sem->core_types.type_String);
        return RESULT_OK;
    }

    case AST_BUILTIN_STACK_TRACE: {
        Scope *fn_scope = sem_scope_get_ancestor(get_scope(node), AST_FN);
        if (! fn_scope) return error_n(sem, node, "The builtin .stack_trace() must appear inside a function.");
        set_type(node, sem->core_types.type_String);
        return RESULT_OK;
    }

    case AST_IMPORT: {
        Auto n = cast(AstImport*, node);
        Type *t = try_get_type_v(n->path_gen);

        if (t->tag != TYPE_STRING) return error_nt(sem, node, t, "expected String type.");
        if (! (n->path_gen->flags & AST_EVALED)) return RESULT_DEFER;

        String path = cast(VmObjString*, sem_get_const_val(sem, n->path_gen).obj)->string;
        n->path = intern_str(sem->interns, path);
        import_file(sem, n->path, node);

        scope_add(sem, get_scope(node), n->name, node, node);
        set_type(node, alloc_type_misc(sem, node));

        return RESULT_OK;
    }

    case AST_IMPORT_FFI: {
        Auto n = cast(AstImportFfi*, node);
        Type *t = try_get_type_v(n->path_gen);

        if (t->tag != TYPE_STRING) return error_nt(sem, node, t, "expected String type.");
        if (! (n->path_gen->flags & AST_EVALED)) return RESULT_DEFER;

        String path = cast(VmObjString*, sem_get_const_val(sem, n->path_gen).obj)->string;
        n->path = intern_str(sem->interns, path);

        FfiModule *module = array_find_ref(&sem->vm->ffi_modules, str_match(IT->name, path));
        if (! module) return error_n(sem, node, "Reference to undeclared ffi module.");

        scope_add(sem, get_scope(node), n->name, node, node);

        Type *type = alloc_type(sem, TYPE_FFI);
        cast(TypeFfi*, type)->name = module->name;
        cast(TypeFfi*, type)->obj  = module->obj;
        set_type(node, type);

        return RESULT_OK;
    }

    case AST_DEFER: {
        sem_set_target(sem, node, node->sem_scope->owner);
        return RESULT_OK;
    }

    case AST_CAST: {
        // As of now we only have implicit casts so there is
        // not much to check here.
        assert_dbg(get_type(node));
        return RESULT_OK;
    }

    case AST_CALL_DEFAULT_ARG: {
        AstCallDefaultArg *n = cast(AstCallDefaultArg*, node);
        set_type(node, try_get_type(n->arg));
        return RESULT_OK;
    }

    case AST_CALL: {
        Auto n = cast(AstCall*, node);
        Ast *d = n->sem_edge;

        if (d) { // Wait for poly instance to get typed:
            if (d->tag == AST_FN) {
                Ast *out = cast(AstBaseFn*, d)->output;
                set_type(node, (out ? try_get_type(out) : sem->core_types.type_Void));
            } else {
                assert_dbg(d->tag == AST_RECORD);
                set_type(node, try_get_type(d));
            }

            return RESULT_OK;
        }

        Type *t = try_get_type(n->lhs);

        if (t == sem->core_types.type_CFn) {
            set_type(node, sem->core_types.type_Top);
            return RESULT_OK;
        }

        if (t->tag == TYPE_FN) {
            try_get_type_v(n->lhs); // Assert it's a value.
            AstBaseFn *fn = cast(TypeFn*, t)->node;
            if (cast(Ast*, fn)->flags & AST_IS_MACRO) return error_nn(sem, node, cast(Ast*, fn), "Cannot call macro using the parens operator (). Use the : operator.");
            set_type(node, fn->output ? try_get_type(fn->output) : sem->core_types.type_Void);
            return check_call(sem, cast(Ast*, fn), &fn->inputs, node, &n->args, true);
        }

        if (t->tag == TYPE_MISC) {
            Ast *c = cast(TypeMisc*, t)->node;

            if (c->flags & AST_IS_MACRO) {
                return error_nn(sem, node, c, "Cannot call macro using the parens operator (). Use the : operator.");
            } else if (c->tag == AST_FN_POLY) {
                try(check_call(sem, c, &cast(AstBaseFn*, c)->inputs, node, &n->args, true));
                if ((n->lhs->tag == AST_IDENT) || (n->lhs->tag == AST_DOT)) sem_set_target(sem, n->lhs, n->sem_edge);
                return RESULT_DEFER; // Wait for poly instance to get typed.
            } else if (c->tag == AST_RECORD_POLY) {
                node->flags |= AST_IS_TYPE;

                if (node->flags & AST_HAS_POLY_ARGS) {
                    try(check_call_args_layout(sem, c, &cast(AstRecordPoly*, c)->args, node, &n->args));
                    set_type(node, alloc_type_var(sem, node, 0));
                    sem_set_target(sem, node, c);
                    return RESULT_OK;
                } else {
                    try(check_call(sem, c, &cast(AstRecordPoly*, c)->args, node, &n->args, true));
                    return RESULT_DEFER; // Wait for poly instance to get typed.
                }
            }
        }

        return error_nt(sem, n->lhs, t, "expected function or poly-struct type.");
    }

    case AST_ENUM: {
        Auto n = cast(AstEnum*, node);

        if (! get_type(node)) {
            Type *t = alloc_type(sem, TYPE_ENUM);
            cast(TypeEnum*, t)->node = n;
            set_type(node, t);
        }

        U64 idx = n->scratch;
        I64 val = 0;

        array_iter_from (field, &n->members, idx) {
            assert_dbg(field->tag == AST_ENUM_FIELD);
            Auto f = cast(AstEnumField*, field);

            if (field->flags & AST_EVALED) val = sem_get_const_val(sem, field).i64;

            if (f->init) {
                if (! (f->init->flags & AST_EVALED)) {
                    n->scratch = ARRAY_IDX;
                    return RESULT_DEFER;
                }

                val = sem_get_const_val(sem, f->init).i64;
            }

            set_const_val(sem, field, (VmReg){ .tag=VM_REG_INT, .i64=val });
            field->flags |= AST_EVALED;
            val++;
        }

        return RESULT_OK;
    }

    case AST_ENUM_FIELD: {
        Auto n = cast(AstEnumField*, node);
        if (n->init) try(match_tv(sem, sem->core_types.type_Int, &n->init));
        set_type(node, sem->core_types.type_Int);
        return RESULT_OK;
    }

    case AST_TUPLE: {
        Auto n = cast(AstTuple*, node);
        Ast *f = array_get(&n->members, 0);

        try_get_type(f);
        if (f->flags & AST_IS_TYPE) array_iter_from (f, &n->members, 1) try_get_type_t(f);
        else                        array_iter_from (f, &n->members, 1) try_get_type_v(f);

        node->flags |= (f->flags & AST_IS_TYPE) ? AST_IS_TYPE : AST_IS_LITERAL;
        Type *t = set_type(node, alloc_type_tuple(sem, n));
        if ((node->flags & AST_IS_LITERAL) && !(node->flags & AST_IN_STANDALONE_POSITION)) t->flags |= TYPE_IS_UNTYPED_LIT;

        return RESULT_OK;
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

        array_iter (i, &n->inits) {
            Auto init = cast(Ast*, i);
            Ast *d = scope_lookup_outside_in(sem, s, i->name, init);
            if (! d) return error_nn(sem, init, s->owner, "Reference to undeclared struct member.");
        }

        map_iter (slot, &s->map) {
            if (slot->val->tag != AST_VAR_DEF) continue; // If it's a poly instance skip the arg instances.

            Auto def = cast(AstVarDef*, slot->val);
            U64 idx  = array_find(&n->inits, IT->name == slot->key);

            if (idx == ARRAY_NIL_IDX) {
                if (! def->init) return error_nn(sem, node, cast(Ast*, def), "Missing initializer in record literal, and there is not default initializer in record definition.");

                // Let's construct the missing initializer AST:
                Ast *init = ast_alloc(sem->mem, AST_RECORD_LIT_INIT, 0);
                init->pos = node->pos;
                cast(AstRecordLitInit*, init)->sem_edge = cast(Ast*, def);
                cast(AstRecordLitInit*, init)->name     = slot->key;
                cast(AstRecordLitInit*, init)->val      = def->init;
                array_push(&n->inits, cast(AstRecordLitInit*, init));
                add_to_check_list(sem, init, get_scope(node));
            }
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
        } else if (t->tag == TYPE_ENUM) {
            Auto c = cast(Ast*, cast(TypeEnum*, t)->node);
            Ast *d = scope_lookup_outside_in(sem, get_scope(c), n->rhs, node);
            if (! d) return RESULT_DEFER;
            Type *t = try_get_type(get_scope(d)->owner);
            set_type(node, t);
        } else if (t->tag == TYPE_MISC && cast(TypeMisc*, t)->node->tag == AST_IMPORT) {
            AstImport *i = cast(AstImport*, cast(TypeMisc*, t)->node);
            Ast *f = cast(Ast*, map_get_assert(&sem->files, i->path));
            Ast *d = scope_lookup_outside_in(sem, get_scope(f), n->rhs, node);
            if (!d || !get_type(d)) return RESULT_DEFER;
            set_type(node, get_type(d));
            node->flags |= d->flags & (AST_IS_TYPE | AST_IS_LVALUE);
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
        }

        return RESULT_OK;
    }

    case AST_ARRAY_LITERAL: {
        Auto n = cast(AstArrayLiteral*, node);

        Type *et;

        if (n->lhs) {
            Ast *el = n->lhs;
            et = try_get_type_t(el);
            array_iter (init, &n->inits, *) try(match_nv(sem, n->lhs, init));
        } else {
            Ast *el = array_get(&n->inits, 0);
            et = try_get_type_v(el);
            array_iter_from (init, &n->inits, 1, *) try(match_nv(sem, el, init));
        }

        if (et->flags & TYPE_IS_SPECIAL) return error_n(sem, node, "Invalid element type for array.");

        Type *t = set_type(node, alloc_type_array(sem, node, 0));
        if (! (node->flags & AST_IN_STANDALONE_POSITION)) t->flags |= TYPE_IS_UNTYPED_LIT;

        cast(TypeArray*, t)->element = et;

        return RESULT_OK;
    }

    case AST_ARRAY_TYPE: {
        Auto n = cast(AstArrayType*, node);
        Type *elem = try_get_type_t(n->element);
        set_type(node, alloc_type_array(sem, node, elem));
        return RESULT_OK;
    }

    case AST_INDEX: {
        Auto n   = cast(AstIndex*, node);
        Type *tl = try_get_type(n->lhs);
        Type *ti = try_get_type_v(n->idx);

        if (ti->tag != TYPE_INT) return error_nt(sem, n->idx, ti, "expected Int type.");

        if (tl->tag == TYPE_ARRAY) {
            set_type(node, cast(TypeArray*, tl)->element);
        } else if (tl->tag == TYPE_TUPLE) {
            if (! (n->idx->flags & AST_MUST_EVAL)) {
                n->idx->flags |= AST_MUST_EVAL;
                array_push(&sem->eval_list, n->idx);
            }

            if (! (n->idx->flags & AST_EVALED)) return RESULT_DEFER;

            I64 idx = sem_get_const_val(sem, n->idx).i64;
            AstTuple *tup = cast(TypeTuple*, tl)->node;
            if (idx < 0 || cast(U64, idx) >= tup->members.count) return error_n(sem, n->idx, "Out of bounds tuple access: (idx=%li count=%li)", idx, tup->members.count);

            Ast *m = array_get(&tup->members, idx);
            set_type(node, get_type(m));
        } else {
            return error_nt(sem, n->lhs, tl, "expected array or tuple type.");
        }

        node->flags |= AST_IS_LVALUE;
        return RESULT_OK;
    }

    case AST_IDENT: {
        Auto n = cast(AstIdent*, node);
        Ast *d = n->sem_edge;

        if (d) {
            if (get_type(node) && (d->tag == AST_FN_POLY)) return RESULT_DEFER;
        } else {
            d = scope_lookup_inside_out(sem, get_scope(node), n->name, node);
            if (! d) return RESULT_DEFER;
        }

        Type *dt = try_get_type(d);

        if (!(node->flags & AST_IN_POLY_ARG_POSITION) && is_tvar_type(dt)) {
            return error_nn(sem, node, d, "Cannot reference a polymorphic expression from this position.");
        } else if (d->tag == AST_FN_POLY) {
            if (node->flags & AST_IN_STANDALONE_POSITION) {
                set_type(node, dt);
            } else {
                ArrayAst *a = &cast(AstBaseFn*, d)->inputs;
                U64 i = array_find(a, (IT->tag == AST_ARG_POLY_TYPE) || (IT->tag == AST_ARG_POLY_VALUE));
                if (i != ARRAY_NIL_IDX) return error_n(sem, node, "Polymorphic functions with comptime arguments cannot be assigned.");
                set_type(node, alloc_type_var(sem, node, TYPE_IS_TVAR_FN));
            }

            return RESULT_DEFER;
        } else {
            set_type(node, dt);
            node->flags |= (d->flags & AST_IS_TYPE);
            return RESULT_OK;
        }
    }

    case AST_VAR_DEF: {
        Auto n = cast(AstVarDef*, node);

        if ((node->flags & (AST_IS_LOCAL_VAR|AST_IS_GLOBAL_VAR)) && !(node->flags & AST_IS_FN_ARG)) {
            if (! n->init) return error_n(sem, node, "Missing initializer.");
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

        if (n->init) {
            Type *t = try_get_type_v(n->init);
            if (t->flags & TYPE_IS_SPECIAL) return error_nt(sem, n->init, t, "expected concrete type");
        }

        if (!(node->flags & AST_IS_LOCAL_VAR) && n->init && !(n->init->flags & AST_EVALED)) return RESULT_DEFER;

        return RESULT_OK;
    }

    case AST_TYPE_ALIAS: {
        Auto n = cast(AstTypeAlias*, node);
        set_type(node, try_get_type_t(n->val));
        return RESULT_OK;
    }

    case AST_TYPE_DISTINCT: {
        Auto n = cast(AstTypeDistinct*, node);
        Type *t = try_get_type_t(n->val);

        if (t->flags & TYPE_IS_SPECIAL) return error_nt(sem, n->val, t, "expected a concrete type");

        U64 size = get_type_struct_size[t->tag];
        Type *dt = mem_alloc(sem->mem, Type, .align=get_type_struct_align[t->tag], .size=size);
        memcpy(dt, t, size);
        dt->id = sem->next_type_id++;
        array_push(&sem->types, dt);

        dt->flags |= TYPE_IS_DISTINCT;
        map_add(&sem->type_def, dt->id, node);
        set_type(node, dt);
        return RESULT_OK;
    }

    case AST_TYPEOF: {
        Auto n = cast(AstBaseUnary*, node);
        Type *t = try_get_type(n->op);
        set_type(node, t);
        return RESULT_OK;
    }

    case AST_OPTION_TYPE: {
        Auto n = cast(AstBaseUnary*, node);
        Type *t = try_get_type_t(n->op);

        if ((t->flags & TYPE_IS_SPECIAL) || (t->tag == TYPE_OPTION)) return error_nt(sem, node, t, "which is an invalid operand to option type.");

        set_type(node, alloc_type_option(sem, t, node));
        return RESULT_OK;
    }

    case AST_FN_TYPE: {
        Auto n = cast(AstBaseFn*, node);
        array_iter (a, &n->inputs) try_get_type_t(a);
        if (n->output) try_get_type_t(n->output);
        Type *t = alloc_type_fn(sem, n);
        set_type(node, t);
        return RESULT_OK;
    }

    case AST_ARG_POLY_VALUE: {
        Auto n = cast(AstArgPolyValue*, node);

        if (n->init && n->constraint) {
            try_get_type_t(n->constraint);
            if (! (n->constraint->flags & AST_HAS_POLY_ARGS)) try(match_nv(sem, n->constraint, &n->init));
        } else if (n->init) {
            Type *t = try_get_type_v(n->init);
            if (t->flags & TYPE_IS_SPECIAL) return error_nt(sem, n->init, t, "expected a concrete type.");
            // @todo Why are we allocating a dummy node here?
            n->constraint = ast_alloc(sem->mem, AST_DUMMY, AST_IS_TYPE);
            n->constraint->pos = ast_trimmed_pos(sem->interns, node);
            add_to_check_list(sem, n->constraint, get_scope(node));
            set_type(n->constraint, t);
        }

        set_type(node, alloc_type_var(sem, node, 0));
        return RESULT_OK;
    }

    case AST_ARG_POLY_TYPE: {
        Auto n = cast(AstArgPolyType*, node);
        if (! (node->flags & AST_IN_POLY_ARG_POSITION)) return error_n(sem, node, "Poly type definition in invalid position.");
        if (n->init) try_get_type_t(n->init);
        set_type(node, alloc_type_var(sem, node, 0));
        return RESULT_OK;
    }

    case AST_FN_POLY: {
        Auto n = cast(AstBaseFn*, node);
        Type *t = get_type(node);

        if (! t) {
            array_iter (a, &n->inputs) {
                Ast *init = get_init(a);

                // Note we must check whether the AST_MUST_EVAL
                // flag is set because of :NoCheckPolyArgInit.
                if (init && (init->flags & AST_MUST_EVAL) && !(init->flags & AST_EVALED)) return RESULT_DEFER;
            }

            if (n->output) try_get_type_t(n->output);

            if (node->flags & AST_IN_STANDALONE_POSITION) {
                set_type(node, alloc_type_misc(sem, node));
                return RESULT_OK;
            } else {
                sem_print_node_out(sem, node);
                set_type(node, alloc_type_var(sem, node, TYPE_IS_TVAR_FN));
                U64 i = array_find(&n->inputs, (IT->tag == AST_ARG_POLY_TYPE) || (IT->tag == AST_ARG_POLY_VALUE));
                return (i == ARRAY_NIL_IDX) ? RESULT_DEFER : error_n(sem, node, "Polymorphic functions with comptime arguments cannot be assigned.");
            }
        }

        return (t->tag == TYPE_VAR) ? RESULT_DEFER : RESULT_OK;
    }

    case AST_FN: {
        Auto n = cast(AstBaseFn*, node);
        if (n->output) try_get_type_t(n->output);
        Type *t = alloc_type_fn(sem, n);
        set_type(node, t);
        return RESULT_OK;
    }

    case AST_RETURN: {
        Auto n = cast(AstReturn*, node);
        Scope *scope = sem_scope_get_ancestor(get_scope(node), AST_FN);
        if (! scope) return error_n(sem, node, "A return can only appear inside functions.");
        Auto fn = cast(AstBaseFn*, scope->owner);
        if (!n->result != !fn->output) return error_nn(sem, cast(Ast*, fn), node, "Number of return values is not matching.");
        if (n->result) try(match_nv(sem, fn->output, &n->result));
        sem_set_target(sem, node, cast(Ast*, fn));
        return RESULT_OK;
    }

    case AST_RECORD_POLY: {
        AstRecordPoly *n = cast(AstRecordPoly*, node);

        array_iter (a, &n->args) {
            Ast *init = get_init(a);
            if (init && (init->flags & AST_MUST_EVAL) && !(init->flags & AST_EVALED)) return RESULT_DEFER;
        }

        set_type(node, alloc_type_misc(sem, node));
        return RESULT_OK;
    }

    case AST_BREAK:
    case AST_CONTINUE: {
        IString *label = (node->tag == AST_BREAK) ? cast(AstBreak*, node)->label : cast(AstContinue*, node)->label;

        for (Scope *s = node->sem_scope; s; s = s->parent) {
            if (s->owner->tag == AST_WHILE) {
                IString *l = cast(AstWhile*, s->owner)->label;
                if (!label || (label == l)) {
                    sem_set_target(sem, node, s->owner);
                    return RESULT_OK;
                }
            }
        }

        return error_n(sem, node, "Could not find corresponding while loop for '%s'.", (node->tag == AST_BREAK) ? "break" : "continue");
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
        if (! (t1->flags & TYPE_IS_PRIMITIVE)) return error_nt(sem, n->op1, t1, "expected primitive type.");
        if (! (t2->flags & TYPE_IS_PRIMITIVE)) return error_nt(sem, n->op2, t2, "expected primitive type.");
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

static Void add_to_infer_list (Sem *sem, Ast *from, Ast *to) {
    array_push_lit(&sem->infer_list, .from=from, .to=to);
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

    if ((n->tag == AST_FN_POLY) || (n->tag == AST_RECORD_POLY)) {
        PolyInfo *prev = sem->poly_info;
        sem->poly_info = alloc_poly_info(sem, n);
        array_iter (arg, sem->poly_info->args) add_to_check_list(sem, arg, scope);
        if (ast_get_base_flags[n->tag] & AST_BASE_FN) add_to_check_list(sem, cast(AstBaseFn*, n)->output, scope);
        sem->poly_info = prev;
    } else {
        #define V(child, ...) add_to_check_list(sem, child, scope);
        AST_VISIT_CHILDREN(n, V);
        #undef V
        if ((n->tag == AST_ARG_POLY_TYPE) || (n->tag == AST_ARG_POLY_VALUE)) array_push(&sem->poly_info->polyargs, n);
    }

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

        array_iter (infer, &sem->infer_list, *) {
            Type *t = get_type(infer->from);
            if (!t || type_has_polyargs(t)) continue;
            set_type(infer->to, t);
            infer->to->flags |= (infer->from->flags & AST_IS_TYPE);
            infer->from = 0; // Mark for removal.
        }

        array_iter (n, &sem->eval_list) {
            eval(sem, n);
            if (sem->error_count) sem_panic(sem);
        }

        U64 cn = sem->check_list.count;
        U64 en = sem->eval_list.count;
        U64 in = sem->infer_list.count;

        Bool new_to_check = (prev_to_check < sem->check_list.count);
        Bool inferred     = in - array_find_remove_all(&sem->infer_list, !IT.from);
        Bool checked      = cn - array_find_remove_all(&sem->check_list, IT->flags & AST_CHECKED);
        Bool evaled       = en - array_find_remove_all(&sem->eval_list, IT->flags & AST_EVALED);

        if (!sem->found_a_sem_edge && !new_to_check && !checked && !evaled && !inferred) break;
    }

    if (sem->check_list.count) error_no_progress(sem);

    array_iter (fn, &sem->fns) {
        if (! cast(AstBaseFn*, fn)->output) continue;

        if (! check_sequence_returns(sem, &fn->statements)) {
            error_n(sem, cast(Ast*, fn), "Not all control paths return.");
            sem_panic(sem);
        }
    }
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
    array_init(&sem->infer_list, mem);
    array_init(&sem->call_check.mono_infos, mem);
    array_init(&sem->call_check.mono_infos_pool, mem);
    array_init(&sem->call_check.simple_untyped_lits, mem);
    array_init(&sem->call_check.casts, mem);
    array_init(&sem->call_check.untyped_lits, mem);
    array_init(&sem->call_check.values_to_match, mem);

    map_init(&sem->files, mem);
    map_init(&sem->type_def, mem);
    map_init(&sem->global_to_reg, mem);
    map_init(&sem->poly_infos, mem);
    map_init(&sem->mono_infos, mem);

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

    return sem;
}

static Void set_const_val (Sem *sem, Ast *node, VmReg reg) {
    map_add(&sem->global_to_reg, node->id, reg);
}

VmReg sem_get_const_val (Sem *sem, Ast *node) {
    assert_dbg(node->flags & AST_EVALED);
    VmReg reg = {};
    map_get(&sem->global_to_reg, node->id, &reg);
    return reg;
}

SemCoreTypes *sem_get_core_types (Sem *sem) {
    return &sem->core_types;
}
