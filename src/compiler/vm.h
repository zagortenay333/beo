#pragma once

#include "base/core.h"
#include "base/mem.h"
#include "base/map.h"
#include "base/array.h"
#include "base/string.h"

istruct (Sem);
istruct (SemProgram);
istruct (AstFn);
istruct (Ast);
istruct (Vm);
istruct (VmObj);

#define EACH_VM_OP(X)\
    X(VM_OP_ADD)\
    X(VM_OP_ARRAY_GET)\
    X(VM_OP_ARRAY_NEW)\
    X(VM_OP_ARRAY_PUSH)\
    X(VM_OP_ARRAY_SET)\
    X(VM_OP_CALL)\
    X(VM_OP_CALL_FFI)\
    X(VM_OP_CONST_GET)\
    X(VM_OP_DIV)\
    X(VM_OP_EQUAL)\
    X(VM_OP_GLOBAL_GET)\
    X(VM_OP_GLOBAL_SET)\
    X(VM_OP_GREATER)\
    X(VM_OP_GREATER_EQUAL)\
    X(VM_OP_IS_NIL)\
    X(VM_OP_JUMP)\
    X(VM_OP_JUMP_IF_FALSE)\
    X(VM_OP_JUMP_IF_TRUE)\
    X(VM_OP_LESS)\
    X(VM_OP_LESS_EQUAL)\
    X(VM_OP_MOD)\
    X(VM_OP_MOVE)\
    X(VM_OP_MUL)\
    X(VM_OP_NEGATE)\
    X(VM_OP_NOP)\
    X(VM_OP_NOT)\
    X(VM_OP_NOT_EQUAL)\
    X(VM_OP_PRINT)\
    X(VM_OP_RECORD_GET)\
    X(VM_OP_RECORD_NEW)\
    X(VM_OP_RECORD_SET)\
    X(VM_OP_RETURN)\
    X(VM_OP_STACK_TRACE)\
    X(VM_OP_SUB)

ienum (VmOp, U8) {
    #define X(TAG, ...) TAG,
        EACH_VM_OP(X)
    #undef X
};

istruct (VmFunction) {
    AstFn *ast;

    U32 first_instruction; // Offset into bytecode->instructions.
    U32 last_instruction;  // Offset into bytecode->instructions.

    // This is the number of preallocated regs. For example,
    // the function:
    //
    //     fn foo (x: Int, y: Int) -> Int {}
    //
    // will have 4 preallocated registers:
    //
    //     r0 = return value register
    //     r1 = callee fn pointer
    //     r2 = first call arg
    //     r3 = second call arg
    //
    U32 n_preallocated_regs;
};

ienum (VmRegTag, U8) {
    VM_REG_NIL,
    VM_REG_BOOL,
    VM_REG_FLOAT,
    VM_REG_FN,
    VM_REG_CFN,
    VM_REG_INT,
    VM_REG_OBJ,
};

typedef U8 VmRegOp;

istruct (VmReg) {
    VmRegTag tag;

    union {
        I64 i64;
        F64 f64;
        Bool boolean;
        VmFunction *fn;
        AstFn *fn_ast;
        Void *cfn; // Cast to VmCFunction.
        VmObj *obj;
    };
};

array_typedef(VmReg, VmReg);
typedef Int (*VmCFunction)(Vm *, SliceVmReg);

ienum (VmObjTag, U8) {
    VM_OBJ_ARRAY,
    VM_OBJ_STRING,
    VM_OBJ_RECORD,
};

istruct (VmObj)       { VmObjTag tag; Bool gc_visited; };
istruct (VmObjString) { VmObj base; String string; };
istruct (VmObjArray)  { VmObj base; ArrayVmReg array; };
istruct (VmObjRecord) { VmObj base; Map(String, VmReg) record; };

array_typedef(VmObj*, VmObj);

istruct (CallRecord) {
    VmFunction *fn;
    U32 pc;
    U32 reg_base;
};

istruct (Vm) {
    Mem *mem;
    SemProgram *sem;

    VmFunction *entry;
    ArrayU8 instructions;
    ArrayVmReg globals;
    ArrayVmReg constants;
    ArrayVmObj gc_objects;
    Array(struct { String name; VmObjRecord *obj; }) ffi;

    Array(Ast*) debug_info; // Index with pc.

    ArrayVmReg registers;
    Array(CallRecord) call_stack;
    U32 time_to_next_gc;
};

Vm   *vm_new               (Mem *);
Void  vm_destroy           (Vm *);
Void  vm_compile_prog      (Vm *, SemProgram *);
Void  vm_compile_str       (Vm *, String);
VmReg vm_transfer_result   (Vm *, Vm *);
Void  vm_print             (Vm *, Bool);
Bool  vm_run               (Vm *);
Void  vm_ffi_new           (Vm *, String);
Void  vm_ffi_add           (Vm *, String, String, VmCFunction);
VmReg vm_reg_add           (VmReg, VmReg);
VmReg vm_reg_sub           (VmReg, VmReg);
VmReg vm_reg_div           (VmReg, VmReg);
VmReg vm_reg_mul           (VmReg, VmReg);
VmReg vm_reg_not_equal     (VmReg, VmReg);
VmReg vm_reg_equal         (VmReg, VmReg);
VmReg vm_reg_greater       (VmReg, VmReg);
VmReg vm_reg_greater_equal (VmReg, VmReg);
VmReg vm_reg_less_equal    (VmReg, VmReg);
VmReg vm_reg_less          (VmReg, VmReg);
VmReg vm_reg_mod           (VmReg, VmReg);
VmReg vm_reg_negate        (VmReg);
VmReg vm_reg_not           (VmReg);
