#pragma once

#include "base/core.h"
#include "base/mem.h"
#include "base/map.h"
#include "base/array.h"
#include "base/string.h"

istruct (Sem);
istruct (AstFn);
istruct (SemProgram);

#define EACH_VM_OP(X)\
    X(VM_OP_ADD)\
    X(VM_OP_ARRAY_GET)\
    X(VM_OP_ARRAY_NEW)\
    X(VM_OP_ARRAY_PUSH)\
    X(VM_OP_ARRAY_SET)\
    X(VM_OP_CALL)\
    X(VM_OP_CONST)\
    X(VM_OP_DIV)\
    X(VM_OP_EQUAL)\
    X(VM_OP_GREATER)\
    X(VM_OP_GREATER_EQUAL)\
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
    //     fn (x: Int, y: Int) -> Int {}
    //
    // will have 4 preallocated registers:
    //
    //     r0 = return value register
    //     r1 = callee fn pointer
    //     r2 = first call arg
    //     r3 = second call arg
    //
    // @todo The register r0 is reserved for the return value
    // even if the function doesn't actually return a val.
    U32 n_preallocated_regs;
};

ienum (VmRegTag, U8) {
    VM_REG_NIL,
    VM_REG_BOOL,
    VM_REG_FLOAT,
    VM_REG_FN,
    VM_REG_INT,
    VM_REG_OBJ,
};

typedef U8 VmRegOp;
istruct (VmObj);

istruct (VmReg) {
    VmRegTag tag;

    union {
        I64 i64;
        F64 f64;
        Bool boolean;
        VmFunction *fn;
        VmObj *obj;
    };
};

array_typedef(VmReg, VmReg);

ienum (VmObjTag, U8) {
    VM_OBJ_ARRAY,
    VM_OBJ_STRING,
    VM_OBJ_RECORD,
};

istruct (VmObj)       { VmObjTag tag; Bool gc_visited; };
istruct (VmObjString) { VmObj base; String string; };
istruct (VmObjArray)  { VmObj base; ArrayVmReg array; };
istruct (VmObjRecord) { VmObj base; Map(String, VmReg) record; };

istruct (VmBytecode) {
    Mem *mem;

    VmFunction *entry;
    ArrayU8 instructions;
    ArrayVmReg constants;

    Sem *sem;
    SemProgram *sem_prog;
};

array_typedef(VmObj*, VmObj);

VmBytecode *vm_emit  (Mem *, String);
Void        vm_print (VmBytecode *);
VmReg       vm_run   (Mem *, VmBytecode *);
