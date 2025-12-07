#pragma once

#include "base/core.h"
#include "base/mem.h"
#include "compiler/ast.h"
#include "compiler/interns.h"

istruct (Vm);
istruct (Sem);
istruct (VmObjRecord);

// X(TypeTag, typedef, TypeFlags)
#define EACH_TYPE(X)\
    X(TYPE_ARRAY, TypeArray, 0)\
    X(TYPE_BOOL, TypeBool, TYPE_CAN_BE_IN_REG)\
    X(TYPE_FFI, TypeFfi, 0)\
    X(TYPE_FLOAT, TypeFloat, TYPE_CAN_BE_IN_REG)\
    X(TYPE_FN, TypeFn, TYPE_CAN_BE_IN_REG)\
    X(TYPE_INT, TypeInt, TYPE_CAN_BE_IN_REG)\
    X(TYPE_RECORD, TypeRecord, 0)\
    X(TYPE_STRING, TypeString, 0)\
    X(TYPE_TOP, TypeTop, 0)\
    X(TYPE_VOID, TypeVoid, 0)

fenum (TypeFlags, U16) {
    TYPE_CAN_BE_IN_REG = flag(0),
    TYPE_VISITED       = flag(1),
    TYPE_IS_DISTINCT   = flag(2),
};

ienum (TypeTag, U8) {
    #define X(TAG, ...) TAG,
        EACH_TYPE(X)
    #undef X
};

typedef U64 TypeId;

istruct (Type)        { TypeTag tag; TypeFlags flags; TypeId id; };
istruct (TypeArray)   { Type type; Ast *node; Type *element; };
istruct (TypeBool)    { Type type; };
istruct (TypeFfi)     { Type type; String name; VmObjRecord *obj; };
istruct (TypeFloat)   { Type type; };
istruct (TypeFn)      { Type type; AstBaseFn *node; };
istruct (TypeInt)     { Type type; };
istruct (TypeRecord)  { Type type; AstRecord *node; };
istruct (TypeString)  { Type type; };
istruct (TypeTop)     { Type type; };
istruct (TypeVoid)    { Type type; };

array_typedef(Type*, Type);

istruct (SemProgram) {
    Sem *sem;
    AstFn *entry;
    ArrayAstFn *fns;
    ArrayType *types;
    ArrayAstVarDef *globals;
};

istruct (Scope) {
    Scope *parent;
    Map(IString*, Ast*) map;

    // If Scope.parent = 0, it's the autoimport scope which is
    // the parent of all file scopes. Entries in this scope are
    // auto inserted by the compiler and cannot be shadowed.
    Ast *owner;
};

#define sem_get_type(SEM, NODE) ((NODE)->sem_type)

Sem        *sem_new            (Mem *, Vm *, Interns *);
SemProgram *sem_check          (Sem *, String);
Void        sem_print_node     (Sem *, AString *, Ast *);
Void        sem_print_node_out (Sem *, Ast *);
