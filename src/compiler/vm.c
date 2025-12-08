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

istruct (Emitter) {
    Mem *mem;
    Vm *vm;
    U16 next_reg;
    AstFn *fn;
    Map(AstId, VmRegOp) binds;
    Array(BreakPatch) break_patches;
    Array(ContinuePatch) continue_patches;
};

static VmObjRecord *get_ffi (Vm *vm, String name);
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
        // @todo Make this a better error message.
        printf(TERM_RED("ERROR(Vm): ") "Ran out of registers.\n\n");
        sem_print_node_out(em->vm->sem, cast(Ast*, em->fn));
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

// @todo This is kinda stupid and slow.
static Void print_cfn (Vm *vm, VmCFunction cfn) {
    array_iter (it, &vm->ffi, *) {
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

// This function returns the idx into bc->constants at which
// the VmFunction is.
//
// @todo We should make this function faster with a hash table.
static U32 get_fn_from_ast (Vm *vm, AstFn *ast) {
    assert_always(vm->constants.count <= UINT32_MAX);

    array_iter (r, &vm->constants, *) {
        if (r->tag != VM_REG_FN) continue;
        if (r->fn->ast == ast) return cast(U32, ARRAY_IDX);
    }

    badpath;
}

static Void emit_const (Emitter *em, VmRegOp result, VmReg val) {
    U32 idx = em->vm->constants.count;
    assert_always(idx < UINT32_MAX); // @todo Better error message.
    array_push(&em->vm->constants, val);
    array_push_n(&em->vm->instructions, VM_OP_CONST_GET, result, ENCODE_U32(idx));
}

// @todo We need to deduplicate strings...
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
    array_push_n(&em->vm->instructions, op, result, arg1, arg2);
}

static Void emit_unary_op (Emitter *em, Ast *expr, VmOp op, VmRegOp result) {
    Auto n = cast(AstBaseUnary*, expr);
    VmRegOp arg = emit_expression(em, n->op, -1);
    array_push_n(&em->vm->instructions, op, result, arg);
}

static Void emit_move (Emitter *em, VmRegOp to, VmRegOp from) {
    array_push_n(&em->vm->instructions, VM_OP_MOVE, to, from);
}

// The @pref argument can be either a VmRegOp into which to place
// the resulting register or -1 to indicate that a new register
// should be allocated.
static VmRegOp emit_expression (Emitter *em, Ast *expr, I32 pref) {
    assert_dbg((pref == -1) || (pref >= 0 && pref <= UINT8_MAX));

    VmRegOp result_reg = (pref == -1) ? reg_push(em) : pref;

    switch (expr->tag) {
    case AST_ADD: emit_binary_op(em, expr, VM_OP_ADD, result_reg); break;
    case AST_DIV: emit_binary_op(em, expr, VM_OP_DIV, result_reg); break;
    case AST_MOD: emit_binary_op(em, expr, VM_OP_MOD, result_reg); break;
    case AST_MUL: emit_binary_op(em, expr, VM_OP_MUL, result_reg); break;
    case AST_SUB: emit_binary_op(em, expr, VM_OP_SUB, result_reg); break;

    case AST_EQUAL:         emit_binary_op(em, expr, VM_OP_EQUAL, result_reg); break;
    case AST_NOT_EQUAL:     emit_binary_op(em, expr, VM_OP_NOT_EQUAL, result_reg); break;
    case AST_LESS:          emit_binary_op(em, expr, VM_OP_LESS, result_reg); break;
    case AST_LESS_EQUAL:    emit_binary_op(em, expr, VM_OP_LESS_EQUAL, result_reg); break;
    case AST_GREATER:       emit_binary_op(em, expr, VM_OP_GREATER, result_reg); break;
    case AST_GREATER_EQUAL: emit_binary_op(em, expr, VM_OP_GREATER_EQUAL, result_reg); break;

    case AST_NEGATE: emit_unary_op(em, expr, VM_OP_NEGATE, result_reg); break;
    case AST_NOT:    emit_unary_op(em, expr, VM_OP_NOT, result_reg); break;

    case AST_BOOL_LITERAL: {
        Bool val = cast(AstBoolLiteral*, expr)->val;
        emit_const(em, result_reg, (VmReg){ .tag = VM_REG_BOOL, .boolean = val });
    } break;

    case AST_INT_LITERAL: {
        I64 val = cast(AstIntLiteral*, expr)->val;
        emit_const(em, result_reg, (VmReg){ .tag = VM_REG_INT, .i64 = val });
    } break;

    case AST_FLOAT_LITERAL: {
        I64 val = cast(AstFloatLiteral*, expr)->val;
        emit_const(em, result_reg, (VmReg){ .tag = VM_REG_FLOAT, .f64 = val });
    } break;

    case AST_STRING_LITERAL: {
        Auto n = cast(AstStringLiteral*, expr);
        emit_const_string(em, *n->str, result_reg);
    } break;

    case AST_ARRAY_LITERAL: {
        Auto n = cast(AstArrayLiteral*, expr);

        array_push_n(&em->vm->instructions, VM_OP_ARRAY_NEW, result_reg);

        array_iter (init, &n->inits) {
            VmRegOp init_reg = emit_expression(em, init, -1);
            array_push_n(&em->vm->instructions, VM_OP_ARRAY_PUSH, result_reg, init_reg);
            reg_pop(em);
        }
    } break;

    case AST_RECORD_LITERAL: {
        Auto n = cast(AstRecordLiteral*, expr);

        array_push_n(&em->vm->instructions, VM_OP_RECORD_NEW, result_reg);

        array_iter (init, &n->inits) {
            VmRegOp init_reg = emit_expression(em, init->val, -1);

            VmRegOp key_reg = reg_push(em);
            emit_const_string(em, *init->name, key_reg);

            array_push_n(&em->vm->instructions, VM_OP_RECORD_SET, result_reg, key_reg, init_reg);

            reg_pop(em);
            reg_pop(em);
        }
    } break;

    case AST_INDEX: {
        Auto n = cast(AstIndex*, expr);
        VmRegOp arr_reg = emit_expression(em, n->lhs, -1);
        VmRegOp idx_reg = emit_expression(em, n->idx, -1);
        array_push_n(&em->vm->instructions, VM_OP_ARRAY_GET, arr_reg, idx_reg, result_reg);
        reg_pop(em);
        reg_pop(em);
    } break;

    case AST_DOT: {
        Auto n = cast(AstDot*, expr);
        VmRegOp rec_reg = emit_expression(em, n->lhs, -1);
        VmRegOp key_reg = emit_const_string(em, *n->rhs, reg_push(em));
        array_push_n(&em->vm->instructions, VM_OP_RECORD_GET, rec_reg, key_reg, result_reg);
        reg_pop(em);
        reg_pop(em);
    } break;

    case AST_CALL: {
        Auto n = cast(AstCall*, expr);

        Bool needs_result_move = (result_reg != em->next_reg - 1);
        VmRegOp result = needs_result_move ? reg_push(em) : result_reg;

        VmRegOp fn_reg = emit_expression(em, n->lhs, reg_push(em));
        array_iter (arg, &n->args) emit_expression(em, arg, reg_push(em));

        SemCoreTypes *core_types = sem_get_core_types(em->vm->sem);

        if (sem_get_type(em->vm->sem, n->lhs) == core_types->type_CFn) {
            assert_always(n->args.count <= 254);
            array_push_n(&em->vm->instructions, VM_OP_CALL_FFI, fn_reg, 2 + cast(U8, n->args.count));
        } else {
            array_push_n(&em->vm->instructions, VM_OP_CALL, fn_reg);
        }

        if (needs_result_move) {
            emit_move(em, result_reg, result);
            em->next_reg = result;
        } else {
            em->next_reg = result + 1;
        }

        return result;
    }

    case AST_FN: {
        U32 fn_idx = get_fn_from_ast(em->vm, cast(AstFn*, expr));
        array_push_n(&em->vm->instructions, VM_OP_CONST_GET, result_reg, ENCODE_U32(fn_idx));
    } break;

    case AST_IDENT: {
        Auto n = cast(AstIdent*, expr);
        Ast *def = n->sem_edge;

        if (def->tag == AST_FN) {
            U32 fn_idx = get_fn_from_ast(em->vm, cast(AstFn*, def));
            array_push_n(&em->vm->instructions, VM_OP_CONST_GET, result_reg, ENCODE_U32(fn_idx));
        } else if (def->flags & AST_IS_LOCAL_VAR) {
            VmRegOp reg; Bool found = map_get(&em->binds, def->id, &reg);
            assert_always(found);

            if (pref == -1) {
                em->next_reg = result_reg;
                return reg;
            } else {
                emit_move(em, result_reg, reg);
            }
        } else if (def->flags & AST_IS_GLOBAL_VAR) {
            I64 global_idx = -1;

            array_iter (global, em->vm->sem_prog->globals) {
                if (global == def) {
                    global_idx = ARRAY_IDX;
                    break;
                }
            }

            assert_always(global_idx > -1 && global_idx <= UINT32_MAX);
            array_push_n(&em->vm->instructions, VM_OP_GLOBAL_GET, result_reg, ENCODE_U32(global_idx));
        } else {
            badpath;
        }
    } break;

    case AST_BUILTIN_PRINT: {
        Auto n = cast(AstBaseUnary*, expr);
        VmRegOp result_reg = emit_expression(em, n->op, -1);
        array_push_n(&em->vm->instructions, VM_OP_PRINT, result_reg);
    } break;

    case AST_LOGICAL_AND:
    case AST_LOGICAL_OR: {
        Auto n = cast(AstBaseBinary*, expr);

        emit_expression(em, n->op1, result_reg);

        array_push(&em->vm->instructions, (expr->tag == AST_LOGICAL_AND) ? VM_OP_JUMP_IF_FALSE : VM_OP_JUMP_IF_TRUE);
        U32 patch_jump = get_bytecode_pos(em);
        array_push_n(&em->vm->instructions, 0, 0, 0, 0, result_reg);

        emit_expression(em, n->op2, result_reg);

        patch_u32(em, patch_jump, get_bytecode_pos(em));
    } break;

    default: badpath;
    }

    if (pref == -1) em->next_reg = result_reg + 1;
    return result_reg;
}

static Void emit_statement (Emitter *em, Ast *stmt) {
    switch (stmt->tag) {
    case AST_RECORD: break;

    case AST_BLOCK: {
        U16 r = em->next_reg;
        array_iter (s, &cast(AstBlock*, stmt)->statements) emit_statement(em, s);
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
            if (n->op1->flags & AST_IS_GLOBAL_VAR) {
                badpath; // @todo
            } else {
                Ast *def = cast(AstIdent*, n->op1)->sem_edge;
                VmRegOp result_reg;
                Bool found = map_get(&em->binds, def->id, &result_reg);
                assert_always(found);
                emit_rhs(result_reg);
            }
        } else if (n->op1->tag == AST_INDEX) {
            Auto lhs = cast(AstIndex*, n->op1);
            VmRegOp arr_reg = emit_expression(em, lhs->lhs, -1);
            VmRegOp idx_reg = emit_expression(em, lhs->idx, -1);
            VmRegOp val_reg = emit_rhs(-1);
            array_push_n(&em->vm->instructions, VM_OP_ARRAY_SET, arr_reg, idx_reg, val_reg);
            reg_pop(em);
        } else if (n->op1->tag == AST_DOT) {
            Auto lhs = cast(AstDot*, n->op1);
            VmRegOp rec_reg = emit_expression(em, lhs->lhs, -1);
            VmRegOp key_reg = emit_const_string(em, *lhs->rhs, reg_push(em));
            VmRegOp val_reg = emit_rhs(-1);
            array_push_n(&em->vm->instructions, VM_OP_RECORD_SET, rec_reg, key_reg, val_reg);
            reg_pop(em);
        } else {
            badpath;
        }

        #undef emit_rhs
    } break;

    case AST_RETURN: {
        Auto n = cast(AstReturn*, stmt);
        if (n->result) emit_expression(em, n->result, 0);
        array_push(&em->vm->instructions, VM_OP_RETURN);
    } break;

    case AST_IF: {
        Auto n = cast(AstIf*, stmt);

        VmRegOp cond = emit_expression(em, n->cond, -1);

        array_push(&em->vm->instructions, VM_OP_JUMP_IF_FALSE);
        U32 patch_if_jump = get_bytecode_pos(em);
        array_push_n(&em->vm->instructions, 0, 0, 0, 0, cond);

        emit_statement(em, n->then_arm);

        U32 patch_else_jump = UINT32_MAX;
        if (n->else_arm) {
            array_push(&em->vm->instructions, VM_OP_JUMP);
            patch_else_jump = get_bytecode_pos(em);
            array_push_n(&em->vm->instructions, 0, 0, 0, 0);
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

        array_push(&em->vm->instructions, VM_OP_JUMP_IF_FALSE);
        U32 patch_jump = get_bytecode_pos(em);
        array_push_n(&em->vm->instructions, 0, 0, 0, 0, cond);

        array_iter (s, &n->statements) emit_statement(em, s);

        array_push_n(&em->vm->instructions, VM_OP_JUMP, ENCODE_U32(continue_block));

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
        ContinuePatch *patch = array_find_ref(&em->continue_patches, IT->while_loop == n->sem_edge);
        array_push_n(&em->vm->instructions, VM_OP_JUMP, ENCODE_U32(patch->continue_block));
    } break;

    case AST_BREAK: {
        Auto n = cast(AstBreak*, stmt);
        array_push(&em->vm->instructions, VM_OP_JUMP);
        U32 patch = get_bytecode_pos(em);
        array_push_n(&em->vm->instructions, 0, 0, 0, 0);
        array_push(&em->break_patches, ((BreakPatch){ n->sem_edge, patch }));
    } break;

    default: {
        emit_expression(em, stmt, -1);
        reg_pop(em);
    } break;

    }
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
    array_init(&em.break_patches, tm);
    array_init(&em.continue_patches, tm);

    reg_push(&em); // First register contains the return value.
    reg_push(&em); // Second register contains callee fn pointer.
    array_iter (arg, &cast(AstBaseFn*, ast)->inputs) add_reg_bind(&em, arg, reg_push(&em));

    array_iter (stmt, &ast->statements) emit_statement(&em, stmt);

    // @todo If the function ends without a return (in the ast)
    // then we have to emit a return instruction in order to
    // prevent the program counter from jumping out of bounds
    // in the run loop. Not sure what the the right way is to
    // deal with this. For now, we always emit a return just
    // in case.
    array_push(&vm->instructions, VM_OP_RETURN);

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

Void vm_set_prog (Vm *vm, String main_file_path) {
    Interns *interns = interns_new(vm->mem, main_file_path);
    vm->sem = sem_new(vm->mem, vm, interns);
    vm->sem_prog = sem_check(vm->sem, main_file_path);

    array_iter (global, vm->sem_prog->globals) {
        array_push(&vm->globals, sem_get_const_val(vm->sem, global));
    }

    emit_fn_constant(vm, vm->sem_prog->entry);
    vm->entry = array_ref(&vm->constants, 0)->fn;
    array_iter (fn, vm->sem_prog->fns) if (fn != vm->sem_prog->entry) emit_fn_constant(vm, fn);

    array_iter (fn, vm->sem_prog->fns) emit_fn_bytecode(vm, fn);
}

Void vm_print (Vm *vm) {
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
        U8 *end = array_ref(&vm->instructions, fn->last_instruction - 1);

        while (cur < end) {
            printf("    %lu: ", cur - beg);

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
                printf("r%i = ", result_reg);
                print_reg(vm, val, false, true);
            } break;
            }
        }
    }

    #undef print_unary_op
    #undef print_binary_op
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

        array_iter (reg, &vm->globals, *) {
            if (reg->tag == VM_REG_OBJ) array_push(&work_set, reg->obj);
        }
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

        array_remove(&vm->gc_objects, ARRAY_IDX--);
    }
}

static VmObj *gc_new_string (Vm *vm, U64 count) {
    gc_run(vm); // @todo Don't call the gc everytime...
    Auto obj = mem_new(mem_root, VmObjString);
    obj->base.tag = VM_OBJ_STRING;
    obj->string.data = mem_alloc(mem_root, Char, .size=count);
    obj->string.count = count;
    array_push(&vm->gc_objects, cast(VmObj*, obj));
    return cast(VmObj*, obj);
}

static VmObj *gc_new_array (Vm *vm) {
    gc_run(vm);
    Auto obj = mem_new(mem_root, VmObjArray);
    obj->base.tag = VM_OBJ_ARRAY;
    array_init(&obj->array, mem_root);
    array_push(&vm->gc_objects, cast(VmObj*, obj));
    return cast(VmObj*, obj);
}

static VmObj *gc_new_record (Vm *vm) {
    gc_run(vm);
    Auto obj = mem_new(mem_root, VmObjRecord);
    obj->base.tag = VM_OBJ_RECORD;
    map_init(&obj->record, mem_root);
    array_push(&vm->gc_objects, cast(VmObj*, obj));
    return cast(VmObj*, obj);
}

static Void print_call_stack (Vm *vm) {
    printf("Stack Trace:\n");

    array_iter_back (cr, &vm->call_stack, *) {
        printf("    fn<%.*s> pc=%u\n", STR(*cr->fn->ast->name), cr->pc);
    }
}

// @todo A lot of the assert_always() should be turned into proper
// error messages. Especially the asserts on types.
static Void run_loop (Vm *vm) {
    assert_dbg(vm->call_stack.count);

    #define run_binop(OP) ({\
        cr->pc += 4;\
        VmReg *out  = get_reg(vm, cr, pc[1]);\
        VmReg *arg1 = get_reg(vm, cr, pc[2]);\
        VmReg *arg2 = get_reg(vm, cr, pc[3]);\
        switch (arg1->tag) {\
        case VM_REG_NIL:   badpath;\
        case VM_REG_OBJ:   badpath;\
        case VM_REG_FN:    badpath;\
        case VM_REG_CFN:   badpath;\
        case VM_REG_BOOL:  badpath;\
        case VM_REG_INT:   out->tag = VM_REG_INT;   out->i64 = arg1->i64 OP arg2->i64; break;\
        case VM_REG_FLOAT: out->tag = VM_REG_FLOAT; out->f64 = arg1->f64 OP arg2->f64; break;\
        }\
    })

    #define run_compare(OP) ({\
        cr->pc += 4;\
        VmReg *out  = get_reg(vm, cr, pc[1]);\
        VmReg *arg1 = get_reg(vm, cr, pc[2]);\
        VmReg *arg2 = get_reg(vm, cr, pc[3]);\
        switch (arg1->tag) {\
        case VM_REG_NIL:   badpath;\
        case VM_REG_OBJ:   badpath;\
        case VM_REG_FN:    badpath;\
        case VM_REG_CFN:   badpath;\
        case VM_REG_BOOL:  badpath;\
        case VM_REG_INT:   out->tag = VM_REG_BOOL; out->boolean = arg1->i64 OP arg2->i64; break;\
        case VM_REG_FLOAT: out->tag = VM_REG_BOOL; out->boolean = arg1->f64 OP arg2->f64; break;\
        }\
    })

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
            cr->pc += 4;

            VmReg *out  = get_reg(vm, cr, pc[1]);
            VmReg *arg1 = get_reg(vm, cr, pc[2]);
            VmReg *arg2 = get_reg(vm, cr, pc[3]);

            switch (arg1->tag) {
            case VM_REG_NIL:   badpath;
            case VM_REG_OBJ:   badpath;
            case VM_REG_BOOL:  badpath;
            case VM_REG_FLOAT: badpath;
            case VM_REG_FN:    badpath;
            case VM_REG_CFN:   badpath;
            case VM_REG_INT:   out->tag = VM_REG_INT; out->i64 = arg1->i64 % arg2->i64; break;
            }
        } break;

        case VM_OP_NEGATE: {
            cr->pc += 3;

            VmReg *out = get_reg(vm, cr, pc[1]);
            VmReg *arg = get_reg(vm, cr, pc[2]);

            switch (arg->tag) {
            case VM_REG_NIL:   badpath;
            case VM_REG_OBJ:   badpath;
            case VM_REG_BOOL:  badpath;
            case VM_REG_FN:    badpath;
            case VM_REG_CFN:   badpath;
            case VM_REG_INT:   out->tag = VM_REG_INT; out->i64 = -arg->i64; break;
            case VM_REG_FLOAT: out->tag = VM_REG_FLOAT; out->f64 = -arg->f64; break;
            }
        } break;

        case VM_OP_NOT: {
            cr->pc += 3;

            VmReg *out = get_reg(vm, cr, pc[1]);
            VmReg *arg = get_reg(vm, cr, pc[2]);

            assert_always(arg->tag == VM_REG_BOOL);
            out->boolean = !arg->boolean;
            out->tag = VM_REG_BOOL;
        } break;

        case VM_OP_ARRAY_NEW: {
            cr->pc += 2;
            VmReg *arr_reg = get_reg(vm, cr, pc[1]);
            arr_reg->obj = gc_new_array(vm);
            arr_reg->tag = VM_REG_OBJ;
        } break;

        case VM_OP_ARRAY_GET: {
            cr->pc += 4;

            VmReg *arr_reg = get_reg(vm, cr, pc[1]);
            VmReg *idx_reg = get_reg(vm, cr, pc[2]);
            VmReg *out_reg = get_reg(vm, cr, pc[3]);

            assert_always(arr_reg->tag == VM_REG_OBJ && arr_reg->obj->tag == VM_OBJ_ARRAY);
            assert_always(idx_reg->tag == VM_REG_INT);

            *out_reg = array_get(&cast(VmObjArray*, arr_reg->obj)->array, cast(U64, idx_reg->i64));
        } break;

        case VM_OP_ARRAY_SET: {
            cr->pc += 4;

            VmReg *arr_reg = get_reg(vm, cr, pc[1]);
            VmReg *idx_reg = get_reg(vm, cr, pc[2]);
            VmReg *val_reg = get_reg(vm, cr, pc[3]);

            assert_always(arr_reg->tag == VM_REG_OBJ && arr_reg->obj->tag == VM_OBJ_ARRAY);
            assert_always(idx_reg->tag == VM_REG_INT);

            U64 idx = cast(U64, idx_reg->i64);
            ArrayVmReg *array = &cast(VmObjArray*, arr_reg->obj)->array;

            if (idx >= array->count) {
                printf("Out of bounds index: (idx=%lu, len=%lu)\n", idx, array->count);
                print_call_stack(vm);
                goto done;
            } else {
                array_set(array, idx, *val_reg);
            }
        } break;

        case VM_OP_ARRAY_PUSH: {
            cr->pc += 3;

            VmReg *arr_reg = get_reg(vm, cr, pc[1]);
            VmReg *val_reg = get_reg(vm, cr, pc[2]);

            assert_always(arr_reg->tag == VM_REG_OBJ);
            assert_always(arr_reg->obj->tag == VM_OBJ_ARRAY);

            array_push(&cast(VmObjArray*, arr_reg->obj)->array, *val_reg);
        } break;

        case VM_OP_RECORD_NEW: {
            cr->pc += 2;
            VmReg *rec_reg = get_reg(vm, cr, pc[1]);
            rec_reg->obj = gc_new_record(vm);
            rec_reg->tag = VM_REG_OBJ;
        } break;

        case VM_OP_RECORD_SET: {
            cr->pc += 4;

            VmReg *rec_reg = get_reg(vm, cr, pc[1]);
            VmReg *key_reg = get_reg(vm, cr, pc[2]);
            VmReg *val_reg = get_reg(vm, cr, pc[3]);

            assert_always(rec_reg->tag == VM_REG_OBJ && rec_reg->obj->tag == VM_OBJ_RECORD);
            assert_always(key_reg->tag == VM_REG_OBJ && key_reg->obj->tag == VM_OBJ_STRING);

            map_add(&cast(VmObjRecord*, rec_reg->obj)->record, cast(VmObjString*, key_reg->obj)->string, *val_reg);
        } break;

        case VM_OP_RECORD_GET: {
            cr->pc += 4;

            VmReg *rec_reg = get_reg(vm, cr, pc[1]);
            VmReg *key_reg = get_reg(vm, cr, pc[2]);
            VmReg *val_reg = get_reg(vm, cr, pc[3]);

            assert_always(rec_reg->tag == VM_REG_OBJ && rec_reg->obj->tag == VM_OBJ_RECORD);
            assert_always(key_reg->tag == VM_REG_OBJ && key_reg->obj->tag == VM_OBJ_STRING);

            Bool found = map_get(&cast(VmObjRecord*, rec_reg->obj)->record, cast(VmObjString*, key_reg->obj)->string, val_reg);
            if (! found) rec_reg->tag = VM_REG_NIL;
        } break;

        case VM_OP_GLOBAL_SET: {
            cr->pc += 6;

            VmReg *val = get_reg(vm, cr, pc[1]);
            U32 glob_idx = read_u32(&pc[2]);

            array_set(&vm->globals, glob_idx, *val);
        } break;

        case VM_OP_GLOBAL_GET: {
            cr->pc += 6;

            VmReg *out = get_reg(vm, cr, pc[1]);
            U32 glob_idx = read_u32(&pc[2]);

            *out = array_get(&vm->globals, glob_idx);
        } break;

        case VM_OP_CONST_GET: {
            cr->pc += 6;

            VmReg *out  = get_reg(vm, cr, pc[1]);
            U32 val_idx = read_u32(&pc[2]);

            *out = array_get(&vm->constants, val_idx);
        } break;

        case VM_OP_PRINT: {
            cr->pc += 2;
            VmReg *reg = get_reg(vm, cr, pc[1]);
            print_reg(vm, reg, true, true);
        } break;

        case VM_OP_CALL: {
            cr->pc += 2;

            VmRegOp arg = pc[1];
            VmReg *arg_reg = get_reg(vm, cr, arg);

            assert_always(arg > 0);
            assert_always(arg_reg->tag == VM_REG_FN);

            fn_call(vm, arg_reg->fn, cr->reg_base + arg - 1);
            cr = array_ref_last(&vm->call_stack);
        } break;

        case VM_OP_CALL_FFI: {
            cr->pc += 3;

            VmRegOp arg  = pc[1];
            U8 arg_count = pc[2];
            VmReg *arg_reg = get_reg(vm, cr, arg);

            assert_always(arg > 0);
            assert_always(arg_reg->tag == VM_REG_CFN);

            SliceVmReg arg_slice;
            arg_slice.data = array_ref(&vm->registers, cr->reg_base + arg - 1);
            arg_slice.count = arg_count;

            Auto fn = cast(VmCFunction, arg_reg->cfn);
            fn(vm, arg_slice);
        } break;

        case VM_OP_RETURN: {
            Bool exit_prog = fn_return(vm);
            if (exit_prog) goto done;
            cr = array_ref_last(&vm->call_stack);
        } break;

        case VM_OP_MOVE: {
            cr->pc += 3;
            VmReg *to   = get_reg(vm, cr, pc[1]);
            VmReg *from = get_reg(vm, cr, pc[2]);
            *to = *from;
        } break;

        case VM_OP_JUMP: {
            cr->pc = read_u32(&pc[1]);
        } break;

        case VM_OP_JUMP_IF_FALSE: {
            cr->pc += 6;
            U32 next_pc = read_u32(&pc[1]);
            VmReg *reg = get_reg(vm, cr, pc[5]);
            assert_always(reg->tag == VM_REG_BOOL);
            if (! reg->boolean) cr->pc = next_pc;
        } break;

        case VM_OP_JUMP_IF_TRUE: {
            cr->pc += 6;
            U32 next_pc = read_u32(&pc[1]);
            VmReg *reg = get_reg(vm, cr, pc[5]);
            assert_always(reg->tag == VM_REG_BOOL);
            if (reg->boolean) cr->pc = next_pc;
        } break;
        }
    } done:;

    #undef run_compare
    #undef run_binop
}

Vm *vm_new (Mem *mem) {
    Auto vm = mem_new(mem, Vm);
    vm->mem = mem;

    array_init(&vm->ffi, mem);
    array_init(&vm->registers, mem);
    array_init(&vm->globals, mem);
    array_init(&vm->constants, mem);
    array_init(&vm->gc_objects, mem);
    array_init(&vm->call_stack, mem);
    array_init(&vm->instructions, mem);

    // @todo Perhaps a better way would be for fn_call/fn_return
    // to dynamically adjust this array.
    array_ensure_count(&vm->registers, 1024*1024, true);

    return vm;
}

Void vm_run (Vm *vm) {
    fn_call(vm, vm->entry, 0);
    run_loop(vm);
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
