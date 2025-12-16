#include "compiler/vm.h"
#include "compiler/ast.h"
#include "compiler/sem.h"
#include "compiler/interns.h"

istruct (ContinuePatch) {
    Ast *while_loop;
    U32 continue_block;
};

istruct (BreakPatch) {
    Ast *while_loop;
    U32 break_patch;
};

istruct (Defer) {
    Ast *statement;
    Ast *scope_owner;
};

istruct (Emitter) {
    Mem *mem;
    Vm *vm;
    U16 next_reg;
    AstFn *fn;
    Ast *debug_node;
    Map(AstId, VmRegOp) binds;
    Array(Defer) defers;
    Array(BreakPatch) break_patches;
    Array(ContinuePatch) continue_patches;
};

static VmObjRecord *get_ffi (Vm *vm, String name);
static Void emit_statement (Emitter *em, Ast *stmt);
static VmRegOp emit_expression (Emitter *em, Ast *expr, I32);
static Void print_reg (Vm *vm ,VmReg *reg, Bool runtime, Bool newline);

#define ENCODE_U32(N) (N)&0xff, (N>>8)&0xff, (N>>16)&0xff, (N>>24)&0xff

static U32 read_u32 (U8 *p) {
    return (p[3]<<24) | (p[2]<<16) | (p[1]<<8) | p[0];
}

static Void patch_u32 (Emitter *em, U32 pos, U32 patch) {
    U8 *p = array_ref(&em->vm->instructions, pos);
    p[0]  = (patch)&0xff;
    p[1]  = (patch>>8)&0xff;
    p[2]  = (patch>>16)&0xff;
    p[3]  = (patch>>24)&0xff;
}

static U32 get_bytecode_pos (Emitter *em) {
    assert_always(em->vm->instructions.count <= UINT32_MAX);
    return cast(U32, em->vm->instructions.count);
}

static VmRegOp reg_push (Emitter *em) {
    if (em->next_reg > UINT8_MAX) {
        printf(TERM_RED("ERROR(Vm): ") "Too many local variables and temporaries. Max allowed is 256.\n\n");
        sem_print_node_out(em->vm->sem->sem, cast(Ast*, em->fn));
        panic();
    }

    return cast(VmRegOp, em->next_reg++);
}

static Void reg_pop (Emitter *em) {
    assert_always(em->next_reg > 0);
    em->next_reg--;
}

static Void print_obj (Vm *vm, VmObj *obj, Bool runtime) {
    switch (obj->tag) {
    case VM_OBJ_STRING: {
        if (runtime) printf("%.*s", STR(cast(VmObjString*, obj)->string));
        else         printf("\"%.*s\"", STR(cast(VmObjString*, obj)->string));
    } break;
    case VM_OBJ_ARRAY: {
        printf("[");
        array_iter (it, &cast(VmObjArray*, obj)->array, *) {
            print_reg(vm, it, runtime, false);
            if (! ARRAY_ITER_DONE) printf(", ");
        }
        printf("]");
    } break;
    case VM_OBJ_RECORD: {
        printf("{ ");
        map_iter (slot, &cast(VmObjRecord*, obj)->record) {
            printf("%.*s: ", STR(slot->key));
            print_reg(vm, &slot->val, runtime, false);
            printf(", ");
        }
        printf("}");
    } break;
    }
}

static Void print_cfn (Vm *vm, VmCFunction cfn) {
    array_iter (it, &vm->ffi_modules, *) {
        assert_dbg(it->tag == VM_REG_OBJ);
        assert_dbg(it->obj->tag == VM_OBJ_RECORD);

        map_iter (slot, &it->obj->record) {
            assert_dbg(slot->val.tag == VM_REG_CFN);
            if (slot->val.cfn == cfn) printf("cfn<%.*s>\n", STR(slot->key));
        }
    }
}

static Void print_reg (Vm *vm, VmReg *reg, Bool runtime, Bool newline) {
    switch (reg->tag) {
    case VM_REG_NIL:   printf("nil"); break;
    case VM_REG_INT:   printf("%li", reg->i64); break;
    case VM_REG_FLOAT: printf("%f", reg->f64); break;
    case VM_REG_BOOL:  printf("%s", reg->boolean ? "true" : "false"); break;
    case VM_REG_FN:    printf("fn<%.*s>", STR(*reg->fn->ast->name)); break;
    case VM_REG_CFN:   print_cfn(vm, reg->cfn); break;
    case VM_REG_OBJ:   print_obj(vm, reg->obj, runtime); break;
    }

    if (newline) printf("\n");
}

static Void add_reg_bind (Emitter *em, Ast *var_def, VmRegOp reg) {
    map_add(&em->binds, var_def->id, reg);
}

// Returns index into vm->constants.
static U32 get_fn_from_ast (Vm *vm, AstFn *ast) {
    assert_always(vm->constants.count <= UINT32_MAX);

    array_iter (r, &vm->constants, *) {
        if (r->tag != VM_REG_FN) continue;
        if (r->fn->ast == ast) return cast(U32, ARRAY_IDX);
    }

    badpath;
}

// Returns index into vm->globals.
static U32 get_global_from_ast (Vm *vm, Ast *ast) {
    assert_always(vm->sem->globals.count <= UINT32_MAX);

    array_iter (global, &vm->sem->globals) {
        if (global == ast) {
            return cast(U32, ARRAY_IDX);
        }
    }

    badpath;
}

static Void record_debug_info (Emitter *em) {
    array_ensure_count(&em->vm->debug_info, em->vm->instructions.count + 1, true);
    array_set(&em->vm->debug_info, em->vm->instructions.count, em->debug_node);
}

#define emit_bytes(EM, ...) ({\
    def1(em, EM);\
    record_debug_info(em);\
    array_push_n(&em->vm->instructions, __VA_ARGS__);\
})

static Void emit_const (Emitter *em, VmRegOp result, VmReg val) {
    U32 idx = em->vm->constants.count;
    assert_always(idx < UINT32_MAX);
    array_push(&em->vm->constants, val);
    emit_bytes(em, VM_OP_CONST_GET, result, ENCODE_U32(idx));
}

// @todo We should deduplicate string literals...
static VmRegOp emit_const_string (Emitter *em, String str, VmRegOp result) {
    // String literal VmObj's are not allocated using
    // the gc since we never want them to be freed.
    Auto o = mem_new(em->vm->mem, VmObjString);
    o->base.tag = VM_OBJ_STRING;
    o->string = str;
    emit_const(em, result, (VmReg){ .tag=VM_REG_OBJ, .obj=&o->base });
    return result;
}

static Void emit_binary_op (Emitter *em, Ast *expr, VmOp op, VmRegOp result) {
    Auto n = cast(AstBaseBinary*, expr);
    VmRegOp arg1 = emit_expression(em, n->op1, -1);
    VmRegOp arg2 = emit_expression(em, n->op2, -1);
    emit_bytes(em, op, result, arg1, arg2);
}

static Void emit_unary_op (Emitter *em, Ast *expr, VmOp op, VmRegOp result) {
    Auto n = cast(AstBaseUnary*, expr);
    VmRegOp arg = emit_expression(em, n->op, -1);
    emit_bytes(em, op, result, arg);
}

static Void emit_move (Emitter *em, VmRegOp to, VmRegOp from) {
    emit_bytes(em, VM_OP_MOVE, to, from);
}

// This function is used for emitting defers right before
// explicit terminators like return, break, continue, ...
//
// The defers that appear at the end of a scope are emitted
// by the emit_sequence() function.
static Void emit_defers (Emitter *em, Ast *outermost_scope_owner) {
    Auto until = array_find(&em->defers, IT.scope_owner == outermost_scope_owner);
    assert_dbg(until != ARRAY_NIL_IDX);

    array_iter_back (d, &em->defers, *) {
        if (ARRAY_IDX == until) break;
        if (d->statement) emit_statement(em, d->statement);
    }
}

// Use this to emit a scoped sequence of statements. It will handle defers.
static Void emit_sequence (Emitter *em, Ast *scope_owner, ArrayAst *statements) {
    assert_dbg(scope_owner->flags & AST_CREATES_SCOPE);
    array_push_lit(&em->defers, .statement=0, .scope_owner=scope_owner); // Push sentinel.
    array_iter (s, statements) emit_statement(em, s);
    array_iter_back (d, &em->defers, *) if (d->statement && (d->scope_owner == scope_owner)) emit_statement(em, d->statement);
    array_find_remove_all(&em->defers, IT.scope_owner == scope_owner);
}

// The @pref argument can be either a VmRegOp into which to place
// the resulting register or -1 to indicate that a new register
// should be allocated.
static VmRegOp emit_expression (Emitter *em, Ast *expr, I32 pref) {
    assert_dbg((pref == -1) || (pref >= 0 && pref <= UINT8_MAX));
    VmRegOp result_reg = (pref == -1) ? reg_push(em) : pref;

    Ast *prev_debug_node = em->debug_node;
    em->debug_node = expr;

    switch (expr->tag) {
    case AST_ADD:           emit_binary_op(em, expr, VM_OP_ADD, result_reg); break;
    case AST_DIV:           emit_binary_op(em, expr, VM_OP_DIV, result_reg); break;
    case AST_MOD:           emit_binary_op(em, expr, VM_OP_MOD, result_reg); break;
    case AST_MUL:           emit_binary_op(em, expr, VM_OP_MUL, result_reg); break;
    case AST_SUB:           emit_binary_op(em, expr, VM_OP_SUB, result_reg); break;
    case AST_EQUAL:         emit_binary_op(em, expr, VM_OP_EQUAL, result_reg); break;
    case AST_NOT_EQUAL:     emit_binary_op(em, expr, VM_OP_NOT_EQUAL, result_reg); break;
    case AST_LESS:          emit_binary_op(em, expr, VM_OP_LESS, result_reg); break;
    case AST_LESS_EQUAL:    emit_binary_op(em, expr, VM_OP_LESS_EQUAL, result_reg); break;
    case AST_GREATER:       emit_binary_op(em, expr, VM_OP_GREATER, result_reg); break;
    case AST_GREATER_EQUAL: emit_binary_op(em, expr, VM_OP_GREATER_EQUAL, result_reg); break;

    case AST_NEGATE: emit_unary_op(em, expr, VM_OP_NEGATE, result_reg); break;
    case AST_NOT:    emit_unary_op(em, expr, VM_OP_NOT, result_reg); break;

    case AST_CAST: {
        Auto n = cast(AstCast*, expr);
        emit_expression(em, n->expr, result_reg);
    } break;

    case AST_NIL: {
        emit_const(em, result_reg, (VmReg){ .tag = VM_REG_NIL });
    } break;

    case AST_BOOL_LITERAL: {
        Bool val = cast(AstBoolLiteral*, expr)->val;
        emit_const(em, result_reg, (VmReg){ .tag = VM_REG_BOOL, .boolean = val });
    } break;

    case AST_INT_LITERAL: {
        I64 val = cast(AstIntLiteral*, expr)->val;
        emit_const(em, result_reg, (VmReg){ .tag = VM_REG_INT, .i64 = val });
    } break;

    case AST_FLOAT_LITERAL: {
        F64 val = cast(AstFloatLiteral*, expr)->val;
        emit_const(em, result_reg, (VmReg){ .tag = VM_REG_FLOAT, .f64 = val });
    } break;

    case AST_STRING_LITERAL: {
        Auto n = cast(AstStringLiteral*, expr);
        emit_const_string(em, *n->str, result_reg);
    } break;

    case AST_ARRAY_LITERAL: {
        Auto n = cast(AstArrayLiteral*, expr);

        emit_bytes(em, VM_OP_ARRAY_NEW, result_reg);

        array_iter (init, &n->inits) {
            VmRegOp init_reg = emit_expression(em, init, -1);
            emit_bytes(em, VM_OP_ARRAY_PUSH, result_reg, init_reg);
            reg_pop(em);
        }
    } break;

    case AST_RECORD_LITERAL: {
        Auto n = cast(AstRecordLiteral*, expr);

        emit_bytes(em, VM_OP_RECORD_NEW, result_reg);

        array_iter (init, &n->inits) {
            VmRegOp init_reg = emit_expression(em, init->val, -1);

            VmRegOp key_reg = reg_push(em);
            emit_const_string(em, *init->name, key_reg);

            emit_bytes(em, VM_OP_RECORD_SET, result_reg, key_reg, init_reg);

            reg_pop(em);
            reg_pop(em);
        }
    } break;

    case AST_TUPLE: {
        Auto n = cast(AstTuple*, expr);

        assert_dbg(! (expr->flags & AST_IS_TYPE));

        emit_bytes(em, VM_OP_ARRAY_NEW, result_reg);

        array_iter (m, &n->members) {
            VmRegOp init_reg = emit_expression(em, m, -1);
            emit_bytes(em, VM_OP_ARRAY_PUSH, result_reg, init_reg);
            reg_pop(em);
        }
    } break;

    case AST_INDEX: {
        Auto n = cast(AstIndex*, expr);
        Sem *sem = em->vm->sem->sem;
        VmRegOp arr_reg = emit_expression(em, n->lhs, -1);

        if (sem_get_type(sem, n->lhs)->tag == TYPE_ARRAY) {
            VmRegOp idx_reg = emit_expression(em, n->idx, -1);
            emit_bytes(em, VM_OP_ARRAY_GET, arr_reg, idx_reg, result_reg);
        } else {
            assert_dbg(sem_get_type(sem, n->lhs)->tag == TYPE_TUPLE);
            VmRegOp idx_reg = reg_push(em);
            emit_const(em, idx_reg, sem_get_const_val(sem, n->idx));
            emit_bytes(em, VM_OP_ARRAY_GET, arr_reg, idx_reg, result_reg);
        }

        reg_pop(em);
        reg_pop(em);
    } break;

    case AST_DOT: {
        Auto n = cast(AstDot*, expr);
        Sem *sem = em->vm->sem->sem;
        Type *t = sem_get_type(sem, n->lhs);

        if (t->tag == TYPE_RECORD) {
            VmRegOp rec_reg = emit_expression(em, n->lhs, -1);
            VmRegOp key_reg = emit_const_string(em, *n->rhs, reg_push(em));
            emit_bytes(em, VM_OP_RECORD_GET, rec_reg, key_reg, result_reg);
            reg_pop(em);
            reg_pop(em);
        } else if (t->tag == TYPE_ENUM) {
            VmReg reg = sem_get_const_val(sem, n->sem_edge);
            assert_dbg(reg.tag == VM_REG_INT);
            emit_const(em, result_reg, reg);
        } else {
            badpath;
        }
    } break;

    case AST_CALL: {
        Auto n = cast(AstCall*, expr);

        Bool needs_result_move = (result_reg != em->next_reg - 1);
        VmRegOp result = needs_result_move ? reg_push(em) : result_reg;

        VmRegOp fn_reg = emit_expression(em, n->lhs, reg_push(em));
        array_iter (arg, &n->args) emit_expression(em, arg, reg_push(em));

        SemCoreTypes *core_types = sem_get_core_types(em->vm->sem->sem);

        if (sem_get_type(em->vm->sem->sem, n->lhs) == core_types->type_CFn) {
            emit_bytes(em, VM_OP_CALL_FFI, fn_reg, 2 + cast(U8, n->args.count));
        } else {
            emit_bytes(em, VM_OP_CALL, fn_reg);
        }

        if (needs_result_move) {
            emit_move(em, result_reg, result);
            em->next_reg = result;
        } else {
            em->next_reg = result + 1;
        }

        result_reg = result;
    } break;

    case AST_FN: {
        U32 fn_idx = get_fn_from_ast(em->vm, cast(AstFn*, expr));
        emit_bytes(em, VM_OP_CONST_GET, result_reg, ENCODE_U32(fn_idx));
    } break;

    case AST_CALL_DEFAULT_ARG: {
        Auto n = cast(AstCallDefaultArg*, expr);
        VmReg val = sem_get_const_val(em->vm->sem->sem, n->arg);
        emit_const(em, result_reg, val);
    } break;

    case AST_IDENT: {
        Auto n = cast(AstIdent*, expr);
        Ast *def = n->sem_edge;

        if (def->tag == AST_FN) {
            U32 fn_idx = get_fn_from_ast(em->vm, cast(AstFn*, def));
            emit_bytes(em, VM_OP_CONST_GET, result_reg, ENCODE_U32(fn_idx));
        } else if (def->flags & AST_IS_LOCAL_VAR) {
            VmRegOp reg; Bool found = map_get(&em->binds, def->id, &reg);
            assert_dbg(found);

            if (pref == -1) {
                em->next_reg = result_reg;
                result_reg = reg;
            } else {
                emit_move(em, result_reg, reg);
            }
        } else if (def->flags & AST_IS_GLOBAL_VAR) {
            I64 global_idx = get_global_from_ast(em->vm, def);
            emit_bytes(em, VM_OP_GLOBAL_GET, result_reg, ENCODE_U32(global_idx));
        } else {
            badpath;
        }
    } break;

    case AST_BUILTIN_PRINT: {
        Auto n = cast(AstBaseUnary*, expr);
        VmRegOp result_reg = emit_expression(em, n->op, -1);
        emit_bytes(em, VM_OP_PRINT, result_reg);
    } break;

    case AST_BUILTIN_FN_NAME: {
        Scope *fn_scope = sem_scope_get_ancestor(expr->sem_scope, AST_FN);
        assert_dbg(fn_scope->owner->tag == AST_FN);
        IString *fn_name = cast(AstFn*, fn_scope->owner)->name;
        emit_const_string(em, *fn_name, result_reg);
    } break;

    case AST_BUILTIN_FILE: {
        Scope *file_scope = sem_scope_get_ancestor(expr->sem_scope, AST_FILE);
        assert_dbg(file_scope->owner->tag == AST_FILE);
        IString *file_name = cast(AstFile*, file_scope->owner)->path;
        emit_const_string(em, *file_name, result_reg);
    } break;

    case AST_BUILTIN_LINE: {
        VmReg val = sem_get_const_val(em->vm->sem->sem, expr);
        emit_const(em, result_reg, val);
    } break;

    case AST_BUILTIN_VAL: {
        Auto n = cast(AstBaseUnary*, expr);
        emit_expression(em, n->op, result_reg);
    } break;

    case AST_BUILTIN_STACK_TRACE: {
        emit_bytes(em, VM_OP_STACK_TRACE, result_reg);
    } break;

    case AST_BUILTIN_IS_NIL: {
        Auto n = cast(AstBaseUnary*, expr);
        emit_expression(em, n->op, result_reg);
        emit_bytes(em, VM_OP_IS_NIL, result_reg, result_reg);
    } break;

    case AST_LOGICAL_AND:
    case AST_LOGICAL_OR: {
        Auto n = cast(AstBaseBinary*, expr);

        emit_expression(em, n->op1, result_reg);

        emit_bytes(em, (expr->tag == AST_LOGICAL_AND) ? VM_OP_JUMP_IF_FALSE : VM_OP_JUMP_IF_TRUE);
        U32 patch_jump = get_bytecode_pos(em);
        emit_bytes(em, 0, 0, 0, 0, result_reg);

        emit_expression(em, n->op2, result_reg);

        patch_u32(em, patch_jump, get_bytecode_pos(em));
    } break;

    default: badpath;
    }

    if (pref == -1) em->next_reg = result_reg + 1;
    em->debug_node = prev_debug_node;

    return result_reg;
}

static Void emit_statement (Emitter *em, Ast *stmt) {
    Ast *prev_debug_node = em->debug_node;
    em->debug_node = stmt;

    switch (stmt->tag) {
    case AST_FN: break;
    case AST_ENUM: break;
    case AST_RECORD: break;
    case AST_TYPE_ALIAS: break;
    case AST_TYPE_DISTINCT: break;

    case AST_BLOCK: {
        U16 r = em->next_reg;
        emit_sequence(em, stmt, &cast(AstBlock*, stmt)->statements);
        em->next_reg = r;
    } break;

    case AST_VAR_DEF: {
        Auto n = cast(AstVarDef*, stmt);
        VmRegOp result_reg = emit_expression(em, n->init ? n->init : n->constraint, -1);
        map_add(&em->binds, stmt->id, result_reg);
    } break;

    case AST_ASSIGN: {
        Auto n = cast(AstBaseBinary*, stmt);
        AstTag f = cast(AstAssign*, stmt)->fused_op;

        #define emit_rhs(R) ({\
            VmRegOp rhs;\
            if (f == AST_ASSIGN) {\
                rhs = emit_expression(em, n->op2, R);\
            } else {\
                stmt->tag = f;\
                rhs = emit_expression(em, stmt, R);\
                stmt->tag = AST_ASSIGN;\
            }\
            rhs;\
        })

        if (n->op1->tag == AST_IDENT) {
            Ast *def = cast(AstIdent*, n->op1)->sem_edge;

            if (def->flags & AST_IS_GLOBAL_VAR) {
                VmRegOp val_reg = emit_rhs(-1);
                U32 global_idx  = get_global_from_ast(em->vm, def);
                emit_bytes(em, VM_OP_GLOBAL_SET, val_reg, ENCODE_U32(global_idx));
            } else {
                VmRegOp result_reg;
                Bool found = map_get(&em->binds, def->id, &result_reg);
                assert_dbg(found);
                emit_rhs(result_reg);
            }
        } else if (n->op1->tag == AST_INDEX) {
            Auto lhs = cast(AstIndex*, n->op1);
            VmRegOp arr_reg = emit_expression(em, lhs->lhs, -1);
            VmRegOp idx_reg = emit_expression(em, lhs->idx, -1);
            VmRegOp val_reg = emit_rhs(-1);
            emit_bytes(em, VM_OP_ARRAY_SET, arr_reg, idx_reg, val_reg);
            reg_pop(em);
        } else if (n->op1->tag == AST_DOT) {
            Auto lhs = cast(AstDot*, n->op1);
            VmRegOp rec_reg = emit_expression(em, lhs->lhs, -1);
            VmRegOp key_reg = emit_const_string(em, *lhs->rhs, reg_push(em));
            VmRegOp val_reg = emit_rhs(-1);
            emit_bytes(em, VM_OP_RECORD_SET, rec_reg, key_reg, val_reg);
            reg_pop(em);
        } else {
            badpath;
        }

        #undef emit_rhs
    } break;

    case AST_RETURN: {
        Auto n = cast(AstReturn*, stmt);
        if (n->result) emit_expression(em, n->result, 0);
        emit_defers(em, n->sem_edge);
        emit_bytes(em, VM_OP_RETURN);
    } break;

    case AST_IF: {
        Auto n = cast(AstIf*, stmt);

        VmRegOp cond = emit_expression(em, n->cond, -1);

        emit_bytes(em, VM_OP_JUMP_IF_FALSE);
        U32 patch_if_jump = get_bytecode_pos(em);
        emit_bytes(em, 0, 0, 0, 0, cond);

        emit_statement(em, n->then_arm);

        U32 patch_else_jump = UINT32_MAX;
        if (n->else_arm) {
            emit_bytes(em, VM_OP_JUMP);
            patch_else_jump = get_bytecode_pos(em);
            emit_bytes(em, 0, 0, 0, 0);
        }

        patch_u32(em, patch_if_jump, get_bytecode_pos(em));

        if (n->else_arm) {
            emit_statement(em, n->else_arm);
            patch_u32(em, patch_else_jump, get_bytecode_pos(em));
        }
    } break;

    case AST_WHILE: {
        Auto n = cast(AstWhile*, stmt);

        U32 continue_block = get_bytecode_pos(em);
        array_push(&em->continue_patches, ((ContinuePatch){ stmt, continue_block }));

        VmRegOp cond = emit_expression(em, n->cond, -1);

        emit_bytes(em, VM_OP_JUMP_IF_FALSE);
        U32 patch_jump = get_bytecode_pos(em);
        emit_bytes(em, 0, 0, 0, 0, cond);

        emit_sequence(em, stmt, &n->statements);

        emit_bytes(em, VM_OP_JUMP, ENCODE_U32(continue_block));

        U32 break_block = get_bytecode_pos(em);
        patch_u32(em, patch_jump, break_block);

        array_pop(&em->continue_patches);
        array_iter (b, &em->break_patches, *) {
            if (b->while_loop != stmt) continue;
            patch_u32(em, b->break_patch, break_block);
            array_remove_fast(&em->break_patches, ARRAY_IDX--);
        }
    } break;

    case AST_CONTINUE: {
        Auto n = cast(AstContinue*, stmt);
        emit_defers(em, n->sem_edge);
        ContinuePatch *patch = array_find_ref(&em->continue_patches, IT->while_loop == n->sem_edge);
        emit_bytes(em, VM_OP_JUMP, ENCODE_U32(patch->continue_block));
    } break;

    case AST_BREAK: {
        Auto n = cast(AstBreak*, stmt);
        emit_defers(em, n->sem_edge);
        emit_bytes(em, VM_OP_JUMP);
        U32 patch = get_bytecode_pos(em);
        emit_bytes(em, 0, 0, 0, 0);
        array_push(&em->break_patches, ((BreakPatch){ n->sem_edge, patch }));
    } break;

    case AST_DEFER: {
        Auto n = cast(AstDefer*, stmt);
        Auto t = n->sem_edge;

        array_iter_back (d, &em->defers, *) {
            if (d->scope_owner == t) {
                array_insert_lit(&em->defers, ARRAY_IDX + 1, .statement=n->stmt, .scope_owner=t);
                break;
            }
        }
    } break;

    default: {
        emit_expression(em, stmt, -1);
        reg_pop(em);
    } break;
    }

    em->debug_node = prev_debug_node;
}

static Void emit_fn_bytecode (Vm *vm, AstFn *ast) {
    tmem_new(tm);
    tmem_pin(tm, 0);

    U32 fn_idx = get_fn_from_ast(vm, ast);
    VmFunction *fn = array_ref(&vm->constants, fn_idx)->fn;
    fn->first_instruction = vm->instructions.count;

    Emitter em = {};
    em.mem = tm;
    em.fn = ast;
    em.vm = vm;
    map_init(&em.binds, tm);
    array_init(&em.defers, tm);
    array_init(&em.break_patches, tm);
    array_init(&em.continue_patches, tm);

    reg_push(&em); // First register contains the return value.
    reg_push(&em); // Second register contains callee fn pointer.
    array_iter (arg, &cast(AstBaseFn*, ast)->inputs) add_reg_bind(&em, arg, reg_push(&em));

    emit_sequence(&em, cast(Ast*, ast), &ast->statements);

    // We emit a return instruction just in case.
    if (! cast(AstBaseFn*, ast)->output) array_push(&vm->instructions, VM_OP_RETURN);

    fn->last_instruction = vm->instructions.count;
}

static Void emit_fn_constant (Vm *vm, AstFn *ast) {
    Auto a = cast(AstBaseFn*, ast);

    Auto fn = mem_new(vm->mem, VmFunction);
    fn->ast = ast;
    fn->n_preallocated_regs = 2 + a->inputs.count;

    VmReg reg = { .tag=VM_REG_FN, .fn=fn };
    array_push(&vm->constants, reg);
}

Void vm_compile_prog (Vm *vm, SemProgram *prog) {
    vm->sem = prog;

    array_iter (global, &vm->sem->globals) {
        VmReg r = sem_get_const_val(vm->sem->sem, (global->tag == AST_VAR_DEF) ? cast(AstVarDef*, global)->init : global);
        array_push(&vm->globals, r);
    }

    assert_dbg(vm->sem->entry->tag == AST_FN);
    emit_fn_constant(vm, cast(AstFn*, vm->sem->entry));
    vm->entry = array_ref(&vm->constants, 0)->fn;
    array_iter (fn, &vm->sem->fns) if (cast(Ast*, fn) != vm->sem->entry) emit_fn_constant(vm, fn);

    array_iter (fn, &vm->sem->fns) emit_fn_bytecode(vm, fn);
}

Void vm_compile_str (Vm *vm, String main_file_path) {
    Interns *interns = interns_new(vm->mem, main_file_path);
    Sem *sem         = sem_new(vm->mem, vm, interns);
    SemProgram *prog = sem_check(sem, main_file_path);
    vm_compile_prog(vm, prog);
}

Void vm_print (Vm *vm, Bool show_source) {
    #define print_binary_op(OP) ({\
        VmRegOp result_reg = cur[1];\
        VmRegOp arg1 = cur[2];\
        VmRegOp arg2 = cur[3];\
        printf("r%u = r%u %s r%u\n", result_reg, arg1, OP, arg2);\
        cur += 4;\
    })

    #define print_unary_op(OP) ({\
        VmRegOp result_reg = cur[1];\
        VmRegOp arg = cur[2];\
        printf("r%u = %s r%u\n", result_reg, OP, arg);\
        cur += 3;\
    })

    array_iter (reg, &vm->constants, *) {
        if (reg->tag != VM_REG_FN) continue;

        VmFunction *fn = reg->fn;

        printf(TERM_CYAN("fn<%.*s>\n"), STR(*fn->ast->name));

        U8 *beg = array_ref(&vm->instructions, 0);
        U8 *cur = array_ref(&vm->instructions, fn->first_instruction);
        U8 *end = array_ref(&vm->instructions, fn->last_instruction - 1) + 1;

        while (cur < end) {
            U32 pc = cur - beg;
            printf("    %u: ", pc);

            switch (cast(VmOp, *cur)) {
            case VM_OP_ADD:           print_binary_op("+"); break;
            case VM_OP_DIV:           print_binary_op("/"); break;
            case VM_OP_LESS:          print_binary_op("<"); break;
            case VM_OP_LESS_EQUAL:    print_binary_op("<="); break;
            case VM_OP_GREATER:       print_binary_op(">"); break;
            case VM_OP_GREATER_EQUAL: print_binary_op(">="); break;
            case VM_OP_EQUAL:         print_binary_op("=="); break;
            case VM_OP_NOT_EQUAL:     print_binary_op("!="); break;
            case VM_OP_SUB:           print_binary_op("-"); break;
            case VM_OP_MUL:           print_binary_op("*"); break;
            case VM_OP_MOD:           print_binary_op("%"); break;
            case VM_OP_NOT:           print_unary_op("-"); break;
            case VM_OP_NEGATE:        print_unary_op("!"); break;
            case VM_OP_CALL:          printf("r%u = call r%i\n", cur[1]-1, cur[1]); cur += 2; break;
            case VM_OP_CALL_FFI:      printf("r%u = call_ffi r%i\n", cur[1]-1, cur[1]); cur += 3; break;
            case VM_OP_NOP:           printf("nop\n"); cur++; break;
            case VM_OP_JUMP:          printf("jump %u\n", read_u32(&cur[1])); cur += 5; break;
            case VM_OP_JUMP_IF_FALSE: printf("jump_if_false %u r%u\n", read_u32(&cur[1]), cur[5]); cur += 6;  break;
            case VM_OP_JUMP_IF_TRUE:  printf("jump_if_true %u r%u\n", read_u32(&cur[1]), cur[5]); cur += 6; break;
            case VM_OP_PRINT:         printf("print r%u\n", cur[1]); cur += 2; break;
            case VM_OP_STACK_TRACE:   printf("r%u = stack_trace\n", cur[1]); cur += 2; break;
            case VM_OP_IS_NIL:        printf("r%u = is_nil r%u\n", cur[2], cur[1]); cur += 3; break;
            case VM_OP_RETURN:        printf("return\n"); cur++; break;
            case VM_OP_MOVE:          printf("r%u = r%u\n", cur[1], cur[2]); cur += 3; break;
            case VM_OP_ARRAY_NEW:     printf("r%u = array_new\n", cur[1]); cur += 2; break;
            case VM_OP_ARRAY_PUSH:    printf("array_push r%u r%u\n", cur[1], cur[2]); cur += 3; break;
            case VM_OP_ARRAY_GET:     printf("r%u = array_get r%u r%u\n", cur[3], cur[1], cur[2]); cur += 4; break;
            case VM_OP_ARRAY_SET:     printf("array_set r%u r%u r%u\n", cur[1], cur[2], cur[3]); cur += 4; break;
            case VM_OP_RECORD_NEW:    printf("r%u = record_new\n", cur[1]); cur += 2; break;
            case VM_OP_RECORD_SET:    printf("record_set r%u r%u r%u\n", cur[1], cur[2], cur[3]); cur += 4; break;
            case VM_OP_RECORD_GET:    printf("r%u = record_get r%u r%u\n", cur[3], cur[1], cur[2]); cur += 4; break;

            case VM_OP_GLOBAL_SET:
            case VM_OP_GLOBAL_GET: {
                VmRegOp reg = cur[1];
                U32 global_idx = read_u32(&cur[2]);
                cur += 6;
                if (*cur == VM_OP_GLOBAL_SET) {
                    printf("global<%u> = r%u\n", global_idx, reg);
                } else {
                    printf("r%i = global<%u>\n", reg, global_idx);
                }
            } break;

            case VM_OP_CONST_GET: {
                VmRegOp result_reg = cur[1];
                U32 val_idx = read_u32(&cur[2]);
                VmReg *val = array_ref(&vm->constants, val_idx);
                cur += 6;
                printf("r%i = const<%u: ", result_reg, val_idx);
                print_reg(vm, val, false, false);
                printf(">\n");
            } break;
            }

            if (show_source) {
                Ast *info = array_get(&vm->debug_info, pc);
                printf("\n");
                sem_print_node_out(vm->sem->sem, info);
            }
        }
    }

    #undef print_unary_op
    #undef print_binary_op
}

static void gc_free (Vm *vm, VmObj *obj) {
    switch (obj->tag) {
    case VM_OBJ_STRING: {
        Auto o = cast(VmObjString*, obj);
        mem_free(mem_root, .old_ptr=o->string.data, .size=o->string.count);
        mem_free(mem_root, .old_ptr=o, .size=sizeof(o));
    } break;

    case VM_OBJ_ARRAY: {
        Auto o = cast(VmObjArray*, obj);
        array_free(&o->array);
        mem_free(mem_root, .old_ptr=o, .size=sizeof(o));
    } break;

    case VM_OBJ_RECORD: {
        Auto o = cast(VmObjRecord*, obj);
        map_free(&o->record);
        mem_free(mem_root, .old_ptr=o, .size=sizeof(o));
    } break;
    }
}

static Void gc_run (Vm *vm) {
    if (vm->call_stack.count == 0) return;

    tmem_new(tm);

    //
    // Mark.
    //
    ArrayVmObj work_set;
    array_init(&work_set, tm);

    { // Collect the roots:
        U64 stop_at = array_ref_last(&vm->call_stack)->reg_base + 256;
        array_iter (reg, &vm->registers, *) {
            if (ARRAY_IDX == stop_at) break;
            if (reg->tag == VM_REG_OBJ) array_push(&work_set, reg->obj);
        }

        array_iter (reg, &vm->globals, *)   if (reg->tag == VM_REG_OBJ) array_push(&work_set, reg->obj);
        array_iter (reg, &vm->constants, *) if (reg->tag == VM_REG_OBJ) array_push(&work_set, reg->obj);
    }

    while (work_set.count) {
        VmObj *obj = array_pop(&work_set);
        obj->gc_visited = true;

        switch (obj->tag) {
        case VM_OBJ_STRING: break;

        case VM_OBJ_ARRAY: {
            array_iter (reg, &cast(VmObjArray*, obj)->array, *) {
                if (reg->tag == VM_REG_OBJ && !reg->obj->gc_visited) array_push(&work_set, reg->obj);
            }
        } break;

        case VM_OBJ_RECORD: {
            map_iter (slot, &cast(VmObjRecord*, obj)->record) {
                if (slot->val.tag == VM_REG_OBJ && !slot->val.obj->gc_visited) array_push(&work_set, slot->val.obj);
            }
        } break;
        }
    }

    //
    // Sweep.
    //
    array_iter (obj, &vm->gc_objects) {
        if (obj->gc_visited) {
            obj->gc_visited = false;
            continue;
        }

        #if BUILD_DEBUG
            printf("Sweeped object: ");
            print_obj(vm, obj, false);
            printf("\n");
        #endif

        gc_free(vm, obj);
        array_remove(&vm->gc_objects, ARRAY_IDX--);
    }
}

// @todo We need to implement a better heuristic here.
static Void gc_maybe_run (Vm *vm) {
    vm->time_to_next_gc++;

    U32 n = 100;

    #if BUILD_DEBUG
        n = 1;
    #endif

    if (vm->time_to_next_gc == n) {
        gc_run(vm);
        vm->time_to_next_gc = 0;
    }

}

static VmObj *gc_new_string (Vm *vm, U64 count) {
    gc_maybe_run(vm);
    Auto obj = mem_new(mem_root, VmObjString);
    obj->base.tag = VM_OBJ_STRING;
    obj->string.data = mem_alloc(mem_root, Char, .size=count);
    obj->string.count = count;
    array_push(&vm->gc_objects, cast(VmObj*, obj));
    return cast(VmObj*, obj);
}

static VmObj *gc_new_array (Vm *vm) {
    gc_maybe_run(vm);
    Auto obj = mem_new(mem_root, VmObjArray);
    obj->base.tag = VM_OBJ_ARRAY;
    array_init(&obj->array, mem_root);
    array_push(&vm->gc_objects, cast(VmObj*, obj));
    return cast(VmObj*, obj);
}

static VmObj *gc_new_record (Vm *vm) {
    gc_maybe_run(vm);
    Auto obj = mem_new(mem_root, VmObjRecord);
    obj->base.tag = VM_OBJ_RECORD;
    map_init(&obj->record, mem_root);
    array_push(&vm->gc_objects, cast(VmObj*, obj));
    return cast(VmObj*, obj);
}

static Void fn_call (Vm *vm, VmFunction *fn, U32 reg_base) {
    CallRecord cr = { fn, fn->first_instruction, reg_base };
    array_push(&vm->call_stack, cr);

    // We must zero out all the register except the first
    // n preallocated ones.
    U64 i = 0;
    U64 from = reg_base + fn->n_preallocated_regs;
    array_iter_from (reg, &vm->registers, from, *) {
        reg->tag = VM_REG_NIL;
        i++;
        if (i == 256) break;
    }
}

static Bool fn_return (Vm *vm) {
    array_pop(&vm->call_stack);
    return vm->call_stack.count == 0;
}

static VmReg *get_reg (Vm *vm, CallRecord *cr, VmRegOp op) {
    return array_ref(&vm->registers, cr->reg_base + op);
}

static String stack_trace (Vm *vm, Mem *mem) {
    AString astr = astr_new(mem);

    array_iter_back (cr, &vm->call_stack, *) {
        Ast *info = array_get(&vm->debug_info, cr->pc);
        AstFile *file = sem_get_file(vm->sem->sem, info);
        astr_push_fmt(&astr, "    %.*s:%lu", STR(*file->path), info->pos.first_line);
    }

    return astr_to_str(&astr);
}

Bool vm_run (Vm *vm) {
    #define runtime_error(...) ({\
        tmem_new(tm);\
        String str = stack_trace(vm, tm);\
        printf(TERM_RED("ERROR(Vm): "));\
        printf(__VA_ARGS__);\
        printf("\n%.*s\n", STR(str));\
        return false;\
    })

    #define assert_reg(REG, TAG) ({\
        if ((REG)->tag != (TAG)) runtime_error("Runtime type mismatch.");\
    })

    #define assert_obj(REG, TAG) ({\
        def1(reg, REG);\
        if (reg->tag != VM_REG_OBJ || reg->obj->tag != (TAG)) runtime_error("Runtime type mismatch.");\
    })

    #define run_binop(OP) ({\
        VmReg *out  = get_reg(vm, cr, pc[1]);\
        VmReg *arg1 = get_reg(vm, cr, pc[2]);\
        VmReg *arg2 = get_reg(vm, cr, pc[3]);\
        switch (arg1->tag) {\
        case VM_REG_NIL:\
        case VM_REG_OBJ:\
        case VM_REG_FN:\
        case VM_REG_CFN:\
        case VM_REG_BOOL:\
            runtime_error("Type mismatch.");\
            \
        case VM_REG_INT:   out->tag = VM_REG_INT;   out->i64 = arg1->i64 OP arg2->i64; break;\
        case VM_REG_FLOAT: out->tag = VM_REG_FLOAT; out->f64 = arg1->f64 OP arg2->f64; break;\
        }\
        cr->pc += 4;\
    })

    #define run_compare(OP) ({\
        VmReg *out  = get_reg(vm, cr, pc[1]);\
        VmReg *arg1 = get_reg(vm, cr, pc[2]);\
        VmReg *arg2 = get_reg(vm, cr, pc[3]);\
        switch (arg1->tag) {\
        case VM_REG_NIL:\
        case VM_REG_OBJ:\
        case VM_REG_FN:\
        case VM_REG_CFN:\
        case VM_REG_BOOL:\
            runtime_error("Type mismatch");\
            \
        case VM_REG_INT:   out->tag = VM_REG_BOOL; out->boolean = arg1->i64 OP arg2->i64; break;\
        case VM_REG_FLOAT: out->tag = VM_REG_BOOL; out->boolean = arg1->f64 OP arg2->f64; break;\
        }\
        cr->pc += 4;\
    })

    fn_call(vm, vm->entry, 0);
    CallRecord *cr = array_ref_last(&vm->call_stack);

    while (true) {
        U8 *pc = array_ref(&vm->instructions, cr->pc);

        switch (cast(VmOp, *pc)) {
        case VM_OP_NOP: cr->pc += 1; break;

        case VM_OP_ADD: run_binop(+); break;
        case VM_OP_SUB: run_binop(-); break;
        case VM_OP_MUL: run_binop(*); break;
        case VM_OP_DIV: run_binop(/); break;

        case VM_OP_NOT_EQUAL:     run_compare(!=); break;
        case VM_OP_EQUAL:         run_compare(==); break;
        case VM_OP_GREATER:       run_compare(>); break;
        case VM_OP_GREATER_EQUAL: run_compare(>=); break;
        case VM_OP_LESS_EQUAL:    run_compare(<=); break;
        case VM_OP_LESS:          run_compare(<); break;

        case VM_OP_MOD: {
            VmReg *out  = get_reg(vm, cr, pc[1]);
            VmReg *arg1 = get_reg(vm, cr, pc[2]);
            VmReg *arg2 = get_reg(vm, cr, pc[3]);

            switch (arg1->tag) {
            case VM_REG_NIL:
            case VM_REG_OBJ:
            case VM_REG_BOOL:
            case VM_REG_FLOAT:
            case VM_REG_FN:
            case VM_REG_CFN:
                runtime_error("Type mismatch");

            case VM_REG_INT: out->tag = VM_REG_INT; out->i64 = arg1->i64 % arg2->i64; break;
            }

            cr->pc += 4;
        } break;

        case VM_OP_NEGATE: {
            VmReg *out = get_reg(vm, cr, pc[1]);
            VmReg *arg = get_reg(vm, cr, pc[2]);

            switch (arg->tag) {
            case VM_REG_NIL:
            case VM_REG_OBJ:
            case VM_REG_BOOL:
            case VM_REG_FN:
            case VM_REG_CFN:
                runtime_error("Type mismatch.");

            case VM_REG_INT:   out->tag = VM_REG_INT; out->i64 = -arg->i64; break;
            case VM_REG_FLOAT: out->tag = VM_REG_FLOAT; out->f64 = -arg->f64; break;
            }

            cr->pc += 3;
        } break;

        case VM_OP_NOT: {
            VmReg *out = get_reg(vm, cr, pc[1]);
            VmReg *arg = get_reg(vm, cr, pc[2]);

            assert_reg(arg, VM_REG_BOOL);
            out->boolean = !arg->boolean;
            out->tag = VM_REG_BOOL;

            cr->pc += 3;
        } break;

        case VM_OP_ARRAY_NEW: {
            VmReg *arr_reg = get_reg(vm, cr, pc[1]);
            arr_reg->obj = gc_new_array(vm);
            arr_reg->tag = VM_REG_OBJ;
            cr->pc += 2;
        } break;

        case VM_OP_ARRAY_GET: {
            VmReg *arr_reg = get_reg(vm, cr, pc[1]);
            VmReg *idx_reg = get_reg(vm, cr, pc[2]);
            VmReg *out_reg = get_reg(vm, cr, pc[3]);

            assert_obj(arr_reg, VM_OBJ_ARRAY);
            assert_reg(idx_reg, VM_REG_INT);

            U64 idx = cast(U64, idx_reg->i64);
            ArrayVmReg *array = &cast(VmObjArray*, arr_reg->obj)->array;

            if (idx >= array->count) runtime_error("Out of bounds index: (idx=%lu len=%lu)", array->count, idx);
            else                     *out_reg = array_get(array, idx);

            cr->pc += 4;
        } break;

        case VM_OP_ARRAY_SET: {
            VmReg *arr_reg = get_reg(vm, cr, pc[1]);
            VmReg *idx_reg = get_reg(vm, cr, pc[2]);
            VmReg *val_reg = get_reg(vm, cr, pc[3]);

            assert_obj(arr_reg, VM_OBJ_ARRAY);
            assert_reg(idx_reg, VM_REG_INT);

            U64 idx = cast(U64, idx_reg->i64);
            ArrayVmReg *array = &cast(VmObjArray*, arr_reg->obj)->array;

            if (idx >= array->count) runtime_error("Out of bounds index: (idx=%lu len=%lu)", array->count, idx);
            else                     array_set(array, idx, *val_reg);

            cr->pc += 4;
        } break;

        case VM_OP_ARRAY_PUSH: {
            VmReg *arr_reg = get_reg(vm, cr, pc[1]);
            VmReg *val_reg = get_reg(vm, cr, pc[2]);
            assert_obj(arr_reg, VM_OBJ_ARRAY);
            array_push(&cast(VmObjArray*, arr_reg->obj)->array, *val_reg);
            cr->pc += 3;
        } break;

        case VM_OP_RECORD_NEW: {
            VmReg *rec_reg = get_reg(vm, cr, pc[1]);
            rec_reg->obj = gc_new_record(vm);
            rec_reg->tag = VM_REG_OBJ;
            cr->pc += 2;
        } break;

        case VM_OP_RECORD_SET: {
            VmReg *rec_reg = get_reg(vm, cr, pc[1]);
            VmReg *key_reg = get_reg(vm, cr, pc[2]);
            VmReg *val_reg = get_reg(vm, cr, pc[3]);

            assert_obj(rec_reg, VM_OBJ_RECORD);
            assert_obj(key_reg, VM_OBJ_STRING);

            map_add(&cast(VmObjRecord*, rec_reg->obj)->record, cast(VmObjString*, key_reg->obj)->string, *val_reg);
            cr->pc += 4;
        } break;

        case VM_OP_RECORD_GET: {
            VmReg *rec_reg = get_reg(vm, cr, pc[1]);
            VmReg *key_reg = get_reg(vm, cr, pc[2]);
            VmReg *val_reg = get_reg(vm, cr, pc[3]);

            assert_obj(rec_reg, VM_OBJ_RECORD);
            assert_obj(key_reg, VM_OBJ_STRING);

            Bool found = map_get(&cast(VmObjRecord*, rec_reg->obj)->record, cast(VmObjString*, key_reg->obj)->string, val_reg);
            if (! found) runtime_error("Invalid record lookup.");

            cr->pc += 4;
        } break;

        case VM_OP_GLOBAL_SET: {
            VmReg *val = get_reg(vm, cr, pc[1]);
            U32 glob_idx = read_u32(&pc[2]);
            array_set(&vm->globals, glob_idx, *val);
            cr->pc += 6;
        } break;

        case VM_OP_GLOBAL_GET: {
            VmReg *out = get_reg(vm, cr, pc[1]);
            U32 glob_idx = read_u32(&pc[2]);
            *out = array_get(&vm->globals, glob_idx);
            cr->pc += 6;
        } break;

        case VM_OP_CONST_GET: {
            VmReg *out  = get_reg(vm, cr, pc[1]);
            U32 val_idx = read_u32(&pc[2]);
            *out = array_get(&vm->constants, val_idx);
            cr->pc += 6;
        } break;

        case VM_OP_PRINT: {
            VmReg *reg = get_reg(vm, cr, pc[1]);
            print_reg(vm, reg, true, true);
            cr->pc += 2;
        } break;

        case VM_OP_STACK_TRACE: {
            VmReg *reg = get_reg(vm, cr, pc[1]);
            tmem_new(tm);
            String trace = stack_trace(vm, tm);
            VmObj *obj = gc_new_string(vm, trace.count);
            memcpy(cast(VmObjString*, obj)->string.data, trace.data, trace.count);
            reg->obj = obj;
            reg->tag = VM_REG_OBJ;
            cr->pc += 2;
        } break;

        case VM_OP_IS_NIL: {
            VmReg *to   = get_reg(vm, cr, pc[1]);
            VmReg *from = get_reg(vm, cr, pc[2]);
            to->boolean = (from->tag == VM_REG_NIL);
            to->tag     = VM_REG_BOOL;
            cr->pc += 3;
        } break;

        case VM_OP_CALL: {
            VmRegOp arg = pc[1];
            VmReg *arg_reg = get_reg(vm, cr, arg);

            assert_reg(arg_reg, VM_REG_FN);

            // Note the program counter will be advanced after
            // the return by the return instruction handling code.
            // This is done so that we get proper stack traces.
            fn_call(vm, arg_reg->fn, cr->reg_base + arg - 1);
            cr = array_ref_last(&vm->call_stack);
        } break;

        case VM_OP_CALL_FFI: {
            VmRegOp arg  = pc[1];
            U8 arg_count = pc[2];
            VmReg *arg_reg = get_reg(vm, cr, arg);

            assert_reg(arg_reg, VM_REG_CFN);

            SliceVmReg arg_slice;
            arg_slice.data = array_ref(&vm->registers, cr->reg_base + arg - 1);
            arg_slice.count = arg_count;

            Auto fn = cast(VmCFunction, arg_reg->cfn);
            Int res = fn(vm, arg_slice);
            if (res < 0) runtime_error("Call to ffi function returned error.");

            cr->pc += 3;
        } break;

        case VM_OP_RETURN: {
            Bool exit_prog = fn_return(vm);
            if (exit_prog) return true;
            cr = array_ref_last(&vm->call_stack);
            cr->pc += 2; // Advance past call instruction. See comment in call handling code.
        } break;

        case VM_OP_MOVE: {
            VmReg *to   = get_reg(vm, cr, pc[1]);
            VmReg *from = get_reg(vm, cr, pc[2]);
            *to = *from;
            cr->pc += 3;
        } break;

        case VM_OP_JUMP: {
            cr->pc = read_u32(&pc[1]);
        } break;

        case VM_OP_JUMP_IF_FALSE: {
            U32 next_pc = read_u32(&pc[1]);
            VmReg *reg = get_reg(vm, cr, pc[5]);
            assert_reg(reg, VM_REG_BOOL);
            if (! reg->boolean) cr->pc = next_pc;
            else                cr->pc += 6;
        } break;

        case VM_OP_JUMP_IF_TRUE: {
            U32 next_pc = read_u32(&pc[1]);
            VmReg *reg = get_reg(vm, cr, pc[5]);
            assert_reg(reg, VM_REG_BOOL);
            if (reg->boolean) cr->pc = next_pc;
            else              cr->pc += 6;
        } break;
        }
    }

    #undef run_binop
    #undef assert_reg
    #undef assert_obj
    #undef run_compare
    #undef runtime_error
}

Vm *vm_new (Mem *mem) {
    Auto vm = mem_new(mem, Vm);
    vm->mem = mem;

    array_init(&vm->ffi, mem);
    array_init(&vm->registers, mem);
    array_init(&vm->debug_info, mem);
    array_init(&vm->globals, mem);
    array_init(&vm->constants, mem);
    array_init(&vm->gc_objects, mem);
    array_init(&vm->call_stack, mem);
    array_init(&vm->instructions, mem);

    // @todo A better way would be for fn_call/fn_return
    // functions to dynamically adjust this array.
    array_ensure_count(&vm->registers, 16*1024, true);

    return vm;
}

Void vm_destroy (Vm *vm) {
    array_iter (obj, &vm->gc_objects) {
        gc_free(vm, obj);
    }
}

static VmObjRecord *get_ffi (Vm *vm, String name) {
    array_iter (it, &vm->ffi, *) {
        if (str_match(it->name, name)) {
            return it->obj;
        }
    }

    return 0;
}

Void vm_ffi_new (Vm *vm, String name) {
    VmObj *obj = gc_new_record(vm);
    array_push_lit(&vm->ffi, .name=name, .obj=cast(VmObjRecord*, obj));
}

Void vm_ffi_add (Vm *vm, String ffi_name, String name, VmCFunction fn) {
    VmObjRecord *obj = get_ffi(vm, ffi_name);

    if (! obj) {
        printf("Ffi module [%.*s] not found.\n", STR(ffi_name));
        return;
    }

    VmReg reg = { .tag=VM_REG_CFN, .cfn=fn };
    map_add(&obj->record, name, reg);
}

#define binop(OP) {\
    VmReg out;\
    switch (r1.tag) {\
    case VM_REG_NIL:   badpath;\
    case VM_REG_OBJ:   badpath;\
    case VM_REG_FN:    badpath;\
    case VM_REG_CFN:   badpath;\
    case VM_REG_BOOL:  badpath;\
    case VM_REG_INT:   out.tag = VM_REG_INT;   out.i64 = r1.i64 OP r2.i64; break;\
    case VM_REG_FLOAT: out.tag = VM_REG_FLOAT; out.f64 = r1.f64 OP r2.f64; break;\
    }\
    return out;\
}

#define compare(OP) {\
    VmReg out;\
    switch (r1.tag) {\
    case VM_REG_NIL:   badpath;\
    case VM_REG_OBJ:   badpath;\
    case VM_REG_FN:    badpath;\
    case VM_REG_CFN:   badpath;\
    case VM_REG_BOOL:  badpath;\
    case VM_REG_INT:   out.tag = VM_REG_BOOL; out.boolean = r1.i64 OP r2.i64; break;\
    case VM_REG_FLOAT: out.tag = VM_REG_BOOL; out.boolean = r1.f64 OP r2.f64; break;\
    }\
    return out;\
}

VmReg vm_reg_add           (VmReg r1, VmReg r2) { binop(+); }
VmReg vm_reg_sub           (VmReg r1, VmReg r2) { binop(-); }
VmReg vm_reg_div           (VmReg r1, VmReg r2) { binop(/); }
VmReg vm_reg_mul           (VmReg r1, VmReg r2) { binop(*); }
VmReg vm_reg_not_equal     (VmReg r1, VmReg r2) { compare(!=); }
VmReg vm_reg_equal         (VmReg r1, VmReg r2) { compare(==); }
VmReg vm_reg_greater       (VmReg r1, VmReg r2) { compare(>); }
VmReg vm_reg_greater_equal (VmReg r1, VmReg r2) { compare(>=); }
VmReg vm_reg_less_equal    (VmReg r1, VmReg r2) { compare(<=); }
VmReg vm_reg_less          (VmReg r1, VmReg r2) { compare(<); }

VmReg vm_reg_mod (VmReg r1, VmReg r2) {
    VmReg out;
    switch (r1.tag) {
    case VM_REG_NIL:   badpath;
    case VM_REG_OBJ:   badpath;
    case VM_REG_FN:    badpath;
    case VM_REG_CFN:   badpath;
    case VM_REG_BOOL:  badpath;
    case VM_REG_FLOAT: badpath;
    case VM_REG_INT:   out.tag = VM_REG_INT; out.i64 = r1.i64 % r2.i64; break;
    }
    return out;
}

VmReg vm_reg_negate (VmReg r) {
    VmReg out;
    switch (r.tag) {
    case VM_REG_NIL:   badpath;
    case VM_REG_OBJ:   badpath;
    case VM_REG_BOOL:  badpath;
    case VM_REG_FN:    badpath;
    case VM_REG_CFN:   badpath;
    case VM_REG_INT:   out.tag = VM_REG_INT;   out.i64 = -r.i64; break;
    case VM_REG_FLOAT: out.tag = VM_REG_FLOAT; out.f64 = -r.f64; break;
    }
    return out;
}

VmReg vm_reg_not (VmReg r) {
    VmReg out;
    assert_always(r.tag == VM_REG_BOOL);
    out.boolean = !r.boolean;
    out.tag = VM_REG_BOOL;
    return out;
}

#undef binop
#undef compare

// The purpose of this function is to take the return value
// of the entry function in the @from VM and transfer it to
// the @to VM.
//
// By 'transfer' we mean that we will copy the value in such
// a way that the returned VmReg can be attached to a global
// var AST node (see sem_get_const_val()) which will be used
// when the @to VM starts running.
//
// The main use case is when compile-time evaling expressions
// inside a VM. There needs to be a way to take the computed
// value and attach it onto the AST expression such that the
// main VM (the one that runs the main program) can use it.
//
// See the eval() function in the sem.c module for usage.
//
// IMPORTANT: This function will do a shallow copy of arrays
// and records! To deal with this the semantic analyser must
// check that the expressions that eval at compile-time must
// have either a primitive type, string type, or array/record
// of primitive types. See the function can_eval() in the
// sem.c module.
VmReg vm_transfer_result (Vm *to, Vm *from) {
    // @todo Right now we assume that the very first register
    // in the vm->registers array is the one with the return
    // value. Although this is true and the gc won't mess with
    // it, it still feels hacky and a more formal interface
    // would be welcome.
    VmReg reg = array_get(&from->registers, 0);

    switch (reg.tag) {
    case VM_REG_NIL:
    case VM_REG_BOOL:
    case VM_REG_FLOAT:
    case VM_REG_CFN:
    case VM_REG_INT:
        // These are easy to transfer since the entire value
        // sits in the registers.
        return reg;

    case VM_REG_FN: {
        reg.tag = VM_REG_NIL;
        return reg;
    }

    case VM_REG_OBJ: {
        switch (reg.obj->tag) {
        case VM_OBJ_ARRAY: {
            Auto o = cast(VmObjArray*, reg.obj);
            Auto new_array = cast(VmObjArray*, gc_new_array(to));
            array_push_many(&new_array->array, &o->array);
            return (VmReg){ .tag=VM_REG_OBJ, .obj=cast(VmObj*, new_array) };
        }

        case VM_OBJ_STRING: {
            Auto o = cast(VmObjString*, reg.obj);
            Auto new_str = cast(VmObjString*, gc_new_string(to, o->string.count));
            memcpy(new_str->string.data, o->string.data, o->string.count);
            return (VmReg){ .tag=VM_REG_OBJ, .obj=cast(VmObj*, new_str) };
        }

        case VM_OBJ_RECORD: {
            Auto o = cast(VmObjRecord*, reg.obj);
            Auto new_rec = cast(VmObjRecord*, gc_new_record(to));
            map_iter (slot, &o->record) map_add(&new_rec->record, slot->key, slot->val);
            return (VmReg){ .tag=VM_REG_OBJ, .obj=cast(VmObj*, new_rec) };
        }
        }
    } break;
    }
}
