#pragma once

#include "base/core.h"
#include "base/mem.h"
#include "compiler/ast.h"
#include "compiler/vm.h"
#include "compiler/interns.h"

istruct (Sem);

// X(TypeTag, typedef, TypeFlags)
#define EACH_TYPE(X)\
    X(TYPE_ARRAY, TypeArray, 0)\
    X(TYPE_BOOL, TypeBool, TYPE_IS_PRIMITIVE)\
    X(TYPE_ENUM, TypeEnum, TYPE_IS_PRIMITIVE)\
    X(TYPE_FFI, TypeFfi, TYPE_IS_SPECIAL)\
    X(TYPE_FLOAT, TypeFloat, TYPE_IS_PRIMITIVE)\
    X(TYPE_FN, TypeFn, 0)\
    X(TYPE_INT, TypeInt, TYPE_IS_PRIMITIVE)\
    X(TYPE_MISC, TypeMisc, TYPE_IS_SPECIAL)\
    X(TYPE_OPTION, TypeOption, 0)\
    X(TYPE_RECORD, TypeRecord, 0)\
    X(TYPE_STRING, TypeString, 0)\
    X(TYPE_TOP, TypeTop, TYPE_IS_SPECIAL)\
    X(TYPE_TUPLE, TypeTuple, 0)\
    X(TYPE_VAR, TypeVar, TYPE_IS_SPECIAL)\
    X(TYPE_VOID, TypeVoid, TYPE_IS_SPECIAL)

fenum (TypeFlags, U16) {
    TYPE_VISITED        = flag(0),
    TYPE_IS_DISTINCT    = flag(1),
    TYPE_IS_PRIMITIVE   = flag(2),
    TYPE_IS_TVAR_FN     = flag(3),
    TYPE_IS_SPECIAL     = flag(4),
    TYPE_IS_UNTYPED_LIT = flag(5),
};

ienum (TypeTag, U8) {
    #define X(TAG, ...) TAG,
        EACH_TYPE(X)
    #undef X
};

typedef U32 TypeId;

istruct (Type)        { TypeTag tag; TypeFlags flags; TypeId id; };
istruct (TypeArray)   { Type type; Ast *node; Type *element; };
istruct (TypeBool)    { Type type; };
istruct (TypeEnum)    { Type type; AstEnum *node; };
istruct (TypeFfi)     { Type type; String name; VmObjRecord *obj; };
istruct (TypeFloat)   { Type type; };
istruct (TypeFn)      { Type type; AstBaseFn *node; };
istruct (TypeInt)     { Type type; };
istruct (TypeMisc)    { Type type; Ast *node; };
istruct (TypeOption)  { Type type; Type *underlying; };
istruct (TypeRecord)  { Type type; AstRecord *node; };
istruct (TypeString)  { Type type; };
istruct (TypeTop)     { Type type; };
istruct (TypeTuple)   { Type type; AstTuple *node; };
istruct (TypeVar)     { Type type; Ast *node; };
istruct (TypeVoid)    { Type type; };

array_typedef(Type*, Type);

istruct (SemCoreTypes) {
    Type *type_Top;
    Type *type_CFn;
    Type *type_Int;
    Type *type_Bool;
    Type *type_Void;
    Type *type_Float;
    Type *type_String;
};

istruct (SemProgram) {
    Sem *sem;
    Ast *entry;
    ArrayAstFn fns;
    ArrayType types;
    ArrayAst globals;
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

Sem          *sem_new                (Mem *, Vm *, Interns *);
SemProgram   *sem_check              (Sem *, String);
Void          sem_print_node         (Sem *, AString *, Ast *);
Void          sem_print_node_out     (Sem *, Ast *);
VmReg         sem_get_const_val      (Sem *, Ast *);
SemCoreTypes *sem_get_core_types     (Sem *);
Scope        *sem_scope_get_ancestor (Scope *, AstTag);
AstFile      *sem_get_file           (Sem *, Ast *);
