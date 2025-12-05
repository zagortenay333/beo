#include "compiler/ast.h"
#include "compiler/interns.h"

CString ast_tag_to_cstr [] = {
    #define X(tag, ...) #tag,
        EACH_AST_NODE(X)
    #undef X
};

U64 ast_get_node_size [] = {
    #define X(a, type, ...) sizeof(type),
        EACH_AST_NODE(X)
    #undef X
};

U8 ast_get_node_align [] = {
    #define X(_, T, ...) alignof(T),
        EACH_AST_NODE(X)
    #undef X
};

U64 ast_get_base_flags [] = {
    #define X(a, b, base_flags, ...) (AST | base_flags),
        EACH_AST_NODE(X)
    #undef X
};

U64 ast_get_default_flags [] = {
    #define X(a, b, c, flags) flags,
        EACH_AST_NODE(X)
    #undef X
};

AstId ast_next_id () {
    static AstId next_id = 1;
    assert_dbg(next_id != 0);
    return next_id++;
}

// The returned AST copy will be in the same state that
// it would be in if produced by the parser.
//
// The provided fn will be called twice: before and after
// copying the subtree rooted at the old node. You can tell
// the two calls apart by checking if the "newn" arg is 0.
Ast *ast_deep_copy (Mem *mem, Ast *old_ast, Ast *(*fn)(Ast *old, Ast *newn, Void *ctx), Void *ctx) {
    if (fn) {
        Ast *r = fn(old_ast, 0, ctx);
        if (r) return r;
    }

    U64 size = ast_get_node_size[old_ast->tag];
    Auto new_ast = mem_alloc(mem, Ast, .align=ast_get_node_align[old_ast->tag], .size=size);
    memcpy(new_ast, old_ast, size);

    new_ast->sem_type  = 0;
    new_ast->sem_scope = 0;
    new_ast->id        = ast_next_id();
    new_ast->flags    &= ~AST_SEM_FLAGS;
    new_ast->flags    |= ast_get_default_flags[new_ast->tag]; // In case one of the SEM_FLAGS is a default flag.

    switch (new_ast->tag) {
    #define X(TAG, T, ...) case TAG: cast(T*, new_ast)->sem_edge = 0; break;
        EACH_AST_SELECTOR(X)
    #undef X
    default: break;
    }

    #define INIT_NODE_SUBSTRUCTS(F, T, N) ({\
        array_init(&N->F, mem);\
    });

    #define DEEP_COPY_F(old_child, _, T, F, ...) ({\
        cast(T*, new_ast)->F = ast_deep_copy(mem, old_child, fn, ctx);\
    })

    #define DEEP_COPY_A(old_child, CT, T, F, ...) ({\
        def1(array, &cast(T*, new_ast)->F);\
        CT new_child = cast(CT, ast_deep_copy(mem, old_child, fn, ctx));\
        array_push(array, new_child);\
    })

    AST_APPLY(new_ast, nop, nop, INIT_NODE_SUBSTRUCTS);
    AST_APPLY(old_ast, DEEP_COPY_F, DEEP_COPY_A, nop);

    if (fn) fn(old_ast, new_ast, ctx);
    return new_ast;
}

Ast *ast_alloc_id (Mem *mem, AstTag tag, AstFlags flags, AstId id) {
    Auto node    = mem_alloc(mem, Ast, .zeroed=true, .align=ast_get_node_align[tag], .size=ast_get_node_size[tag]);
    node->id     = id;
    node->tag    = tag;
    node->flags |= ast_get_default_flags[tag] | flags;

    #define INIT_SUBSTRUCTS(F, _, N) array_init(&N->F, mem);
    AST_APPLY(node, nop, nop, INIT_SUBSTRUCTS);

    return node;
}

Ast *ast_alloc (Mem *mem, AstTag tag, AstFlags flags) {
    return ast_alloc_id(mem, tag, flags, ast_next_id());
}

SrcPos ast_trimmed_pos (Interns *interns, Ast *node) {
    SrcPos pos = node->pos;

    #define TRIM(L) { pos.length = (L); pos.last_line = pos.first_line; }

    switch (node->tag) {
    case AST_BLOCK:          TRIM(1); break;
    case AST_FN:             TRIM(interns->FN->count); break;
    case AST_IF:             TRIM(interns->IF->count); break;
    case AST_RETURN:         TRIM(interns->RETURN->count); break;
    case AST_RECORD:         TRIM(interns->RECORD->count); break;
    case AST_WHILE:          TRIM(interns->WHILE->count); break;
    case AST_STRING_LITERAL: TRIM(1); break;
    default:                 break;
    }

    return pos;
}
