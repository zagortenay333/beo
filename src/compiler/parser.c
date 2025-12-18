#include <math.h>
#include "base/mem.h"
#include "base/log.h"
#include "os/fs.h"
#include "compiler/ast.h"
#include "compiler/interns.h"
#include "compiler/lexer.h"
#include "compiler/parser.h"

istruct (ArgContext) {
    ArrayAst args;
    Array(IString*) polyargs;
};

istruct (Parser) {
    Mem *mem;
    AstFile *file;
    Interns *interns;
    Lexer *lexer;
    Bool brace_ends_expression;
    Array(ArgContext*) arg_context_pool;
    Array(ArgContext*) arg_context_stack;
    Map(AstId, ArrayAstNote*) notes;
};

#define lex (par->lexer)

static Ast *parse_block (Parser *par);
static Ast *parse_statement (Parser *par);
static Void pop_arg_context (Parser *par);
static Void parse_block_out (Parser *par, ArrayAst *);
static Ast *parse_expression (Parser *par, U64 left_op);
static Ast *parse_expression_before_brace (Parser *par);
static Ast *try_parse_expression (Parser *par, U64 left_op);
static Void mark_standalone_position (Parser *par, Ast *node);
static Void try_parse_expression_list (Parser *par, ArrayAst *out);
static ArgContext *parse_args (Parser *par, Bool runtime_args_allowed);
static Void mark_poly_arg_position (Parser *par, Ast *parent, Ast *node);
static Ast *parse_var_def (Parser *par, Bool with_semicolon, Bool with_keyword);

Noreturn
static Void par_error_pos2 Fmt(4, 5) (Parser *par, SrcPos p1, SrcPos p2, CString fmt, ...) {
    tmem_new(tm);

    AString msg = astr_new(tm);
    astr_push_cstr(&msg, TERM_RED("ERROR(Parser): "));

    AstFile *f = par->file;
    SrcLog *slog = slog_new(tm, slog_default_config);
    slog_add_src(slog, cast(Ast*, f)->id, *f->path, f->content);
    slog_add_pos(slog, cast(Ast*, f)->id, p1);
    if (p2.first_line) slog_add_pos(slog, cast(Ast*, f)->id, p2);

    astr_push_fmt_vam(&msg, fmt);
    array_push_n(&msg, '\n', '\n');
    slog_flush(slog, &msg);
    astr_println(&msg);
    panic();
}

#define par_error_pos(PAR, POS, ...) par_error_pos2(PAR, POS, (SrcPos){}, __VA_ARGS__);
#define par_error(PAR, ...)          par_error_pos2(PAR, lex_peek(lex)->pos, (SrcPos){}, __VA_ARGS__);

static Ast *complete_node (Parser *par, Void *node) {
    Auto n = cast(Ast*, node);
    SrcPos prev = lex_get_prev_pos(lex);
    n->pos.last_line = prev.last_line;
    n->pos.length = prev.offset + prev.length - n->pos.offset;
    return n;
}

static Void *make_node_by_tag (Parser *par, AstTag tag) {
    Ast *node = ast_alloc(par->mem, tag, 0);
    SrcPos pos = lex_peek(lex)->pos;
    node->pos.offset = pos.offset;
    node->pos.first_line = pos.first_line;
    return node;
}

static Void *make_node_lhs_by_tag (Parser *par, AstTag tag, Ast *lhs) {
    Ast *node = ast_alloc(par->mem, tag, 0);
    node->pos.offset = lhs->pos.offset;
    node->pos.first_line = lhs->pos.first_line;
    return node;
}

#define make_node(PAR, T)        cast(T*, make_node_by_tag(PAR, e##T))
#define make_node_lhs(PAR, T, L) cast(T*, make_node_lhs_by_tag(PAR, e##T, L))

ArrayAstNote *par_get_notes (Parser *par, AstId id) {
    return map_get_ptr(&par->notes, id);
}

static Void attach_note (Parser *par, AstId id, AstNote *note) {
    ArrayAstNote *notes = par_get_notes(par, id);

    if (! notes) {
        notes = mem_new(par->mem, ArrayAstNote);
        array_init(notes, par->mem);
        map_add(&par->notes, id, notes);
    }

    AstNote **prev = array_find_ref(notes, (*IT)->key == note->key);
    if (prev) *prev = note;
    else      array_push(notes, note);
}

static Ast *try_parse_note (Parser *par, AstId id) {
    if (! lex_try_eat(lex, '#')) return 0;
    Auto note = make_node(par, AstNote);
    note->key = lex_eat_this(lex, TOKEN_IDENT)->str;
    if (lex_try_eat(lex, '=')) note->val = parse_expression(par, 0);
    attach_note(par, id, note);
    return complete_node(par, note);
}

#define try_peek_attribute(ATTR) ({\
    Token *token = lex_try_peek(lex, TOKEN_IDENT);\
    (token && token->str == par->interns->attr_##ATTR) ? token : 0;\
})

#define try_eat_attribute(ATTR) ({\
    Token *token = lex_try_peek(lex, TOKEN_IDENT);\
    (token && token->str == par->interns->attr_##ATTR) ? lex_eat(lex) : 0;\
})

#define eat_attribute(ATTR) ({\
    Token *token = lex_eat_this(lex, TOKEN_IDENT);\
    IString *attr = par->interns->attr_##ATTR;\
    if (token->str != attr) par_error_pos(par, token->pos, "Expected attribute '%.*s'.", STR(*attr));\
    token;\
})

#define starts_with_attribute(ATTR) ({\
    Bool result = false;\
    if (lex_try_peek_nth(lex, 2, ':')) {\
        Token *token = lex_peek_nth(lex, 3);\
        if (token->tag == TOKEN_IDENT) {\
            result = (token->str == par->interns->attr_##ATTR);\
        } else if (token->tag == '(') {\
            token = lex_try_peek_nth(lex, 4, TOKEN_IDENT);\
            result = (token && token->str == par->interns->attr_##ATTR);\
        }\
    }\
    result;\
})

#define parse_attributes(NODE_ID, PRE_LOOP, ...) ({\
    def1(id, NODE_ID);\
    lex_eat_this(lex, ':');\
    Bool _(in_parens) = lex_try_eat(lex, '(');\
    U64 _(start) = lex_peek(lex)->pos.offset;\
    PRE_LOOP;\
    lex_try_eat(lex, ',');\
    do {\
        if (! try_parse_note(par, id)) { __VA_ARGS__; }\
    } while (_(in_parens) && lex_try_eat(lex, ','));\
    if (_(in_parens)) {\
        if (!lex_try_eat(lex, ')')) par_error(par, "Invalid attribute.");\
    } else if (_(start) == lex_peek(lex)->pos.offset) {\
        par_error(par, "Invalid attribute.");\
    }\
})

#define try_parse_attributes(NODE_ID, PRE_LOOP, ...) ({\
    if (lex_try_peek(lex, ':')) {\
        parse_attributes(NODE_ID, PRE_LOOP, __VA_ARGS__);\
    }\
})

#define is_left_associative(token_tag) true
#define prefix(token_tag) (token_tag + TOKEN_TAG_COUNT)

// If it's a prefix operator, do precedence_of(prefix(token_tag)).
static U64 precedence_of (TokenTag token_tag) {
    switch (token_tag) {
    case '.':
    case '(':
    case '[':
    case '{':
        return 9;

    case prefix('?'):
    case prefix('-'):
    case prefix('.'):
    case prefix('!'):
    case prefix('['):
        return 8;

    case '*':
    case '/':
    case '%':
        return 6;

    case '+':
    case '-':
        return 5;

    case '<':
    case '>':
    case TOKEN_LESS_EQUAL:
    case TOKEN_GREATER_EQUAL:
        return 4;

    case TOKEN_2EQUAL:
    case TOKEN_NOT_EQUAL:
        return 3;

    case TOKEN_AND:
        return 2;

    case TOKEN_OR:
        return 1;
    }

    return 0;
}

static Ast *parse_record_member (Parser *par) {
    switch (lex_peek(lex)->tag) {
    case TOKEN_IDENT: {
        Ast *r = parse_var_def(par, true, false);
        if (cast(AstVarDef*, r)->init) cast(AstVarDef*, r)->init->flags |= AST_MUST_EVAL;
        return r;
    }
    default: return 0;
    }
}

static Ast *parse_record_poly (Parser *par) {
    Auto node = make_node(par, AstRecordPoly);

    lex_eat_this(lex, TOKEN_RECORD);
    try_parse_attributes(cast(Ast*, node)->id,);
    node->name = lex_eat_this(lex, TOKEN_IDENT)->str;

    ArgContext *ctx = parse_args(par, false);
    swap(node->args, ctx->args);
    array_iter (arg, &node->args) mark_poly_arg_position(par, cast(Ast*, node), arg);
    cast(Ast*, node)->flags &= ~AST_HAS_POLY_ARGS;
    pop_arg_context(par);

    lex_eat_this(lex, '{');

    while (! lex_try_peek(lex, '}')) {
        Ast *member = parse_record_member(par);
        if (! member) break;
        array_push(&node->members, member);
    }

    lex_eat_this(lex, '}');
    return complete_node(par, node);
}

static Ast *parse_record (Parser *par) {
    Auto node = make_node(par, AstRecord);

    lex_eat_this(lex, TOKEN_RECORD);
    try_parse_attributes(cast(Ast*, node)->id,);
    Token *name = lex_try_eat(lex, TOKEN_IDENT);
    if (name) node->name = name->str;
    lex_eat_this(lex, '{');

    while (! lex_try_peek(lex, '}')) {
        Ast *member = parse_record_member(par);
        if (! member) break;
        array_push(&node->members, member);
    }

    lex_eat_this(lex, '}');
    return complete_node(par, node);
}

static Ast *parse_enum_field (Parser *par) {
    Auto node = make_node(par, AstEnumField);
    node->name = lex_eat_this(lex, TOKEN_IDENT)->str;

    if (lex_try_eat(lex, '=')) {
        node->init = try_parse_expression(par, 0);
        node->init->flags |= AST_MUST_EVAL;
    }

    return complete_node(par, node);
}

static Ast *parse_enum (Parser *par) {
    Auto node = make_node(par, AstEnum);
    lex_eat_this(lex, TOKEN_ENUM);
    try_parse_attributes(cast(Ast*, node)->id,);
    node->name = lex_eat_this(lex, TOKEN_IDENT)->str;
    lex_eat_this(lex, '{');

    while (! lex_try_peek(lex, '}')) {
        Ast *member = parse_enum_field(par);
        if (! member) break;
        array_push(&node->members, member);
        if (! lex_try_eat(lex, ',')) break;
    }

    lex_eat_this(lex, '}');
    return complete_node(par, node);
}

static Ast *parse_interface (Parser *par) {
    Auto node = make_node(par, AstInterface);
    lex_eat_this(lex, '/');
    node->name = lex_eat_this(lex, TOKEN_IDENT)->str;
    return complete_node(par, node);
}

static Ast *parse_ident (Parser *par) {
    Auto node = make_node(par, AstIdent);
    node->name = lex_eat_this(lex, TOKEN_IDENT)->str;
    return complete_node(par, node);
}

static Ast *parse_string_literal (Parser *par) {
    Auto node = make_node(par, AstStringLiteral);
    node->str = lex_eat_this(lex, TOKEN_STRING_LITERAL)->str;
    return complete_node(par, node);
}

static Ast *parse_var_def (Parser *par, Bool with_semicolon, Bool with_keyword) {
    Auto node = make_node(par, AstVarDef);

    if (with_keyword) {
        lex_eat_this(lex, TOKEN_VAR);
        try_parse_attributes(cast(Ast*, node)->id,);
    }

    node->name = lex_eat_this(lex, TOKEN_IDENT)->str;
    if (lex_try_eat(lex, ':')) node->constraint = parse_expression(par, 0);
    if (lex_try_eat(lex, '=')) node->init = parse_expression(par, 0);
    if (!node->constraint && !node->init) lex_eat_this(lex, ':');
    if (with_semicolon) lex_eat_this(lex, ';');
    if (! node->constraint) mark_standalone_position(par, node->init);

    return complete_node(par, node);
}

static ArgContext *push_arg_context (Parser *par) {
    ArgContext *ctx;

    if (par->arg_context_pool.count) {
        ctx = array_pop(&par->arg_context_pool);
        ctx->args.count = 0;
        ctx->polyargs.count = 0;
    } else {
        ctx = mem_new(par->mem, ArgContext);
        array_init(&ctx->args, par->mem);
        array_init(&ctx->polyargs, par->mem);
    }

    array_push(&par->arg_context_stack, ctx);
    return ctx;
}

static Void pop_arg_context (Parser *par) {
    ArgContext *ctx = array_pop(&par->arg_context_stack);
    array_push(&par->arg_context_pool, ctx);
}

static IString *make_anon_fn_name (Parser *par, U64 file_byte_offset) {
    IString *f = par->file->path;
    String s   = astr_fmt(par->mem, "fn:%.*s:0x%lx", STR(*f), file_byte_offset);
    return intern_str(par->interns, s);
}

static Ast *make_poly_type_arg (Parser *par, Ast *parent, IString *name) {
    Auto node = cast(Ast*, make_node(par, AstArgPolyType));
    node->pos = ast_trimmed_pos(par->interns, parent);
    String n = astr_fmt(par->mem, "Type(%.*s)", STR(*name));
    cast(AstArgPolyType*, node)->name = intern_str(par->interns, n);
    mark_poly_arg_position(par, parent, node);
    ArgContext *ctx = array_try_get_last(&par->arg_context_stack);
    if (ctx) array_push(&ctx->polyargs, cast(AstArgPolyType*, node)->name);
    return node;
}

static Ast *parse_poly_type (Parser *par, Bool init_allowed) {
    Auto node = make_node(par, AstArgPolyType);

    lex_eat_this(lex, '$');
    node->name = lex_eat_this(lex, TOKEN_IDENT)->str;

    if      (lex_try_eat(lex, ':'))  node->constraint = parse_expression(par, 0);
    else if (lex_try_peek(lex, '/')) node->constraint = parse_interface(par);

    if (init_allowed && lex_try_eat(lex, '=')) {
        node->init = parse_expression(par, 0);
        node->init->flags |= AST_MUST_EVAL;
    }

    ArgContext *ctx = array_try_get_last(&par->arg_context_stack);
    if (ctx) array_push(&ctx->polyargs, node->name);
    return complete_node(par, node);
}

static Ast *parse_poly_value (Parser *par, ArgContext *ctx) {
    Auto node = make_node(par, AstArgPolyValue);
    node->name = lex_eat_this(lex, TOKEN_IDENT)->str;
    lex_eat_this(lex, '$');
    if (lex_try_eat(lex, ':')) node->constraint = parse_expression(par, 0);
    if (lex_try_eat(lex, '=')) { node->init = parse_expression(par, 0); node->init->flags |= AST_MUST_EVAL; }
    if (!node->constraint && !node->init) node->constraint = make_poly_type_arg(par, cast(Ast*, node), node->name);
    array_push(&ctx->polyargs, node->name);
    return complete_node(par, node);
}

// An AST in standalone position is an expression that won't
// be matched against other types during semantic analysis:
//
//     var x = foo;
//             ^^^--------- standalone position
//     var x: Foo = foo;
//                  ^^^---- not standalone; matched with Foo
//
// This info is mainly used to handle untyped literals which
// can or must infer their type from the expression they are
// matched against. For example, an anonymous struct literal
// in standalone position is an error. An array literal in
// standalone position will infer the array element type
// from it's first initializer.
static Void mark_standalone_position (Parser *par, Ast *node) {
    node->flags |= AST_IN_STANDALONE_POSITION;

    switch (node->tag) {
    case AST_ARRAY_LITERAL: {
        AstArrayLiteral *n = cast(AstArrayLiteral*, node);
        if (! n->lhs) mark_standalone_position(par, array_get(&n->inits, 0));
    } break;
    case AST_TUPLE: {
        ArrayAst *members = &cast(AstTuple*, node)->members;
        array_iter (f, members) mark_standalone_position(par, f);
    } break;
    case AST_OPTION_TYPE: {
        mark_standalone_position(par, cast(AstBaseUnary*, node)->op);
    } break;
    default: break;
    }
}

// Recurse down a fn arg constraint and mark positions where
// it's legal to put a reference or definition to a polyarg
// with the AST_IN_POLY_ARG_POSITION flag. For example:
//
//     fn a ($T, y: Type($R)) {}
//           ^^----------^^---------- Ok.
//     fn b { var x: $T; }
//                   ^^-------------- Error.
//
// We also mark trees with the AST_HAS_POLY_ARGS flag if they
// contain definitions or references of polyargs.
static Void mark_poly_arg_position (Parser *par, Ast *parent, Ast *node) {
    if (! node) return;

    switch (node->tag) {
    case AST_IDENT: {
        ArgContext *ctx = array_get_last(&par->arg_context_stack);
        IString *name = cast(AstIdent*, node)->name;

        node->flags |= AST_IN_POLY_ARG_POSITION;
        if (array_has(&ctx->polyargs, name)) { node->flags |= AST_HAS_POLY_ARGS; break; }

        array_iter (arg, &ctx->args) {
            Bool found = false;

            switch (arg->tag) {
            #define X(TAG, TYPE) case TAG: found = (name == cast(TYPE*, arg)->name); break;
                EACH_STATIC_NAME_GENERATOR(X)
            #undef X
            default: badpath;
            }

            if (found && (arg->flags & AST_HAS_POLY_ARGS)) { node->flags |= AST_HAS_POLY_ARGS; break; }
        }
    } break;
    case AST_VAR_DEF: {
        AstVarDef *n = cast(AstVarDef*, node);
        node->flags |= AST_IN_POLY_ARG_POSITION;
        mark_poly_arg_position(par, node, n->constraint);

        if (n->init && n->constraint && (n->constraint->flags & AST_HAS_POLY_ARGS)) {
            // :NoCheckPolyArgInit
            //
            // Since the constraint contains polyargs we don't want to typecheck
            // the initializer at all, since it could be something that is also
            // polymorphic like an anon struct literal, in which case we would be
            // matching a polymorph with a polymorph... Instead, we will simply
            // make copies of the init node for each call site.
            n->init->flags &= ~AST_MUST_EVAL;
            n->init->flags |= AST_ADDED_TO_CHECK_LIST;
        }
    } break;
    case AST_ARG_POLY_VALUE: {
        AstArgPolyValue *n = cast(AstArgPolyValue*, node);
        node->flags |= (AST_IN_POLY_ARG_POSITION | AST_HAS_POLY_ARGS);
        mark_poly_arg_position(par, node, n->constraint);

        if (n->init && n->constraint && (n->constraint->flags & AST_HAS_POLY_ARGS)) {
            // :NoCheckPolyArgInit
            n->init->flags &= ~AST_MUST_EVAL;
            n->init->flags |= AST_ADDED_TO_CHECK_LIST;
        }
    } break;
    case AST_ARG_POLY_TYPE:
        node->flags |= (AST_IN_POLY_ARG_POSITION | AST_HAS_POLY_ARGS);
        break;
    case AST_OPTION_TYPE:
        node->flags |= AST_IN_POLY_ARG_POSITION;
        mark_poly_arg_position(par, node, cast(AstBaseUnary*, node)->op);
        break;
    case AST_ARRAY_TYPE:
        node->flags |= AST_IN_POLY_ARG_POSITION;
        mark_poly_arg_position(par, node, cast(AstArrayType*, node)->element);
        break;
    case AST_DOT:
        node->flags |= AST_IN_POLY_ARG_POSITION;
        mark_poly_arg_position(par, node, cast(AstDot*, node)->lhs);
        break;
    case AST_TUPLE:
        node->flags |= AST_IN_POLY_ARG_POSITION;
        array_iter (f, &cast(AstTuple*, node)->members) mark_poly_arg_position(par, node, cast(Ast*, f));
        break;
    case AST_CALL:
        node->flags |= AST_IN_POLY_ARG_POSITION;
        array_iter (a, &cast(AstCall*, node)->args) mark_poly_arg_position(par, node, a);
        break;
    case AST_FN_TYPE: {
        node->flags |= AST_IN_POLY_ARG_POSITION;
        AstBaseFn *n = cast(AstBaseFn*, node);
        array_iter (i, &n->inputs) mark_poly_arg_position(par, node, i);
        mark_poly_arg_position(par, node, n->output);
    } break;
    case AST_TYPEOF:
        node->flags |= AST_IN_POLY_ARG_POSITION;
        mark_poly_arg_position(par, node, cast(AstBaseUnary*, node)->op);
        break;
    default: break;
    }

    parent->flags |= (node->flags & AST_HAS_POLY_ARGS);
}

static ArgContext *parse_args (Parser *par, Bool runtime_args_allowed) {
    ArgContext *ctx = push_arg_context(par);
    if (! lex_try_eat(lex, '(')) return ctx;

    while (true) {
        Ast *arg = 0;
        TokenTag tok = lex_peek(lex)->tag;

        if (tok == '$') {
            arg = parse_poly_type(par, true);
        } else if (tok != TOKEN_IDENT) {
            break;
        } else if (lex_try_peek_nth(lex, 2, '$')) {
            arg = parse_poly_value(par, ctx);
        } else {
            arg = parse_var_def(par, false, false);
            arg->flags |= (AST_IS_LOCAL_VAR | AST_IS_FN_ARG);
            if (cast(AstVarDef*, arg)->init) cast(AstVarDef*, arg)->init->flags |= AST_MUST_EVAL;
            if (! runtime_args_allowed) par_error_pos(par, arg->pos, "Runtime arguments not allowed here.");
        }

        array_push(&ctx->args, arg);
        if (! lex_try_eat(lex, ',')) break;
    }

    lex_eat_this(lex, ')');
    return ctx;
}

static Ast *parse_fn (Parser *par, Bool as_expression) {
    AstId id = ast_next_id();
    SrcPos start = lex_peek(lex)->pos;
    AstFlags is_macro = (lex_eat(lex)->tag == TOKEN_MACRO) ? AST_IS_MACRO : 0;

    try_parse_attributes(id,);

    IString *name = as_expression ? 0 : lex_eat_this(lex, TOKEN_IDENT)->str;
    if (! name) name = make_anon_fn_name(par, start.offset);

    ArgContext *ctx = parse_args(par, true);

    Auto node = cast(AstBaseFn*, ast_alloc_id(par->mem, (ctx->polyargs.count ? AST_FN_POLY : AST_FN), is_macro, id));
    cast(Ast*, node)->pos = start;
    if (lex_try_eat(lex, TOKEN_ARROW)) node->output = parse_expression_before_brace(par);

    if (ctx->polyargs.count) {
        AstFnPoly *n = cast(AstFnPoly*, node);
        n->name = name;
        parse_block_out(par, &n->statements);
        array_iter (arg, &ctx->args) mark_poly_arg_position(par, cast(Ast*, node), arg);
    } else {
        AstFn *n = cast(AstFn*, node);
        n->name = name;
        parse_block_out(par, &n->statements);
    }

    swap(node->inputs, ctx->args);
    pop_arg_context(par);
    return complete_node(par, node);
}

static Ast *parse_fn_type (Parser *par) {
    Auto node = cast(AstBaseFn*, make_node(par, AstFnType));
    lex_eat_this(lex, TOKEN_FN_TYPE);

    if (lex_try_eat(lex, '(')) {
        while (! lex_try_peek(lex, ')')) {
            if (lex_try_peek(lex, TOKEN_IDENT) && lex_try_peek_nth(lex, 2, ':')) { lex_eat(lex); lex_eat(lex); }
            array_push(&node->inputs, parse_expression(par, 0));
            if (! lex_try_eat(lex, ',')) break;
        }

        lex_eat_this(lex, ')');
    }

    if (lex_try_eat(lex, TOKEN_ARROW)) node->output = parse_expression(par, 0);
    return complete_node(par, node);
}

static Ast *parse_array_literal_or_type (Parser *par) {
    SrcPos start = lex_peek(lex)->pos;
    lex_eat_this(lex, '[');
    Ast *expr = try_parse_expression(par, 0);

    if (expr) {
        Auto node = make_node(par, AstArrayLiteral);
        cast(Ast*, node)->pos = start;
        array_push(&node->inits, expr);
        if (lex_try_eat(lex, ',')) try_parse_expression_list(par, &node->inits);
        lex_eat_this(lex, ']');
        return complete_node(par, node);
    } else {
        lex_eat_this(lex, ']');
        expr = try_parse_expression(par, prefix('['));

        if (expr) {
            Auto node = make_node(par, AstArrayType);
            cast(Ast*, node)->pos = start;
            node->element = expr;
            return complete_node(par, node);
        } else {
            par_error_pos(par, start, "Array literals must either have at least 1 member or a lhs type spec.");
        }
    }
}

static Ast *parse_array_literal_or_index (Parser *par, Ast *lhs) {
    SrcPos start = lhs->pos;
    lex_eat_this(lex, '[');
    Ast *expr = try_parse_expression(par, 0);
    Bool has_comma = lex_try_eat(lex, ',');

    if (!expr || has_comma) {
        Auto node = make_node_lhs(par, AstArrayLiteral, lhs);
        cast(Ast*, node)->pos = start;
        node->lhs = lhs;
        if (expr) array_push(&node->inits, expr);
        try_parse_expression_list(par, &node->inits);
        lex_eat_this(lex, ']');
        return complete_node(par, node);
    } else {
        Auto node = make_node_lhs(par, AstIndex, lhs);
        cast(Ast*, node)->pos = start;
        node->lhs = lhs;
        node->idx = expr;
        mark_standalone_position(par, lhs);
        lex_eat_this(lex, ']');
        return complete_node(par, node);
    }
}

static Ast *parse_tuple_or_parens (Parser *par) {
    SrcPos p1 = lex_eat_this(lex, '(')->pos;
    Ast *node = parse_expression(par, 0);

    if (lex_try_eat(lex, ',')) {
        Auto n = make_node(par, AstTuple);
        array_push(&n->members, node);
        try_parse_expression_list(par, &n->members);
        node = cast(Ast*, n);
    }

    SrcPos p2 = lex_eat_this(lex, ')')->pos;

    node->pos = (SrcPos){
        .offset     = p1.offset,
        .length     = p2.offset - p1.offset + 1,
        .first_line = p1.first_line,
        .last_line  = p2.last_line,
    };

    return node;
}

static Ast *parse_bool_literal (Parser *par, TokenTag tag) {
    Auto node = make_node(par, AstBoolLiteral);
    lex_eat_this(lex, tag);
    node->val = (tag == TOKEN_TRUE);
    return complete_node(par, node);
}

static Ast *parse_int_literal (Parser *par) {
    Auto node = make_node(par, AstIntLiteral);
    U64 val = lex_peek(lex)->u64;
    if (val > INT64_MAX) par_error(par, "Number too big to fit into an I64.");
    node->val = cast(I64, lex_eat(lex)->u64);
    return complete_node(par, node);
}

static Ast *parse_float_literal (Parser *par) {
    Auto node = make_node(par, AstFloatLiteral);
    node->val = lex_eat(lex)->f64;
    return complete_node(par, node);
}

static Ast *parse_negate (Parser *par) {
    Ast *node = 0;
    SrcPos pos = lex_eat_this(lex, '-')->pos;
    Ast *op = parse_expression(par, prefix('-'));

    switch (op->tag) {
    case AST_INT_LITERAL: {
        node = op;
        cast(AstIntLiteral*, op)->val = -cast(AstIntLiteral*, op)->val;
    } break;

    case AST_FLOAT_LITERAL: {
        node = op;
        cast(AstFloatLiteral*, op)->val = -cast(AstFloatLiteral*, op)->val;
    } break;

    default: {
        node = cast(Ast*, make_node(par, AstNegate));
        cast(AstBaseUnary*, node)->op = op;
    } break;
    }

    node->pos = pos;
    return complete_node(par, node);
}

static Ast *parse_record_lit_init (Parser *par) {
    Auto node = make_node(par, AstRecordLitInit);
    node->name = lex_eat_this(lex, TOKEN_IDENT)->str;
    lex_eat_this(lex, '=');
    node->val = parse_expression(par, 0);
    return complete_node(par, node);
}

static Ast *parse_record_literal (Parser *par, Ast *lhs) {
    Auto node = make_node_lhs(par, AstRecordLiteral, lhs);
    node->lhs = lhs;

    lex_eat_this(lex, '{');

    while (! lex_try_peek(lex, '}')) {
        Auto init = cast(AstRecordLitInit*, parse_record_lit_init(par));
        array_push(&node->inits, init);
        if (! lex_try_eat(lex, ',')) break;
    }

    lex_eat_this(lex, '}');
    return complete_node(par, node);
}

static Ast *parse_call (Parser *par, Ast *lhs) {
    Auto node = make_node_lhs(par, AstCall, lhs);
    node->lhs = lhs;
    lex_eat_this(lex, '(');

    while (true) {
        if (lex_try_peek(lex, ')')) {
            break;
        } else if (lex_try_peek(lex, TOKEN_IDENT) && lex_try_peek_nth(lex, 2, '=')) {
            Auto arg = make_node(par, AstCallNamedArg);
            arg->name = lex_eat(lex)->str;
            lex_eat(lex);
            arg->arg = parse_expression(par, 0);
            array_push(&node->args, complete_node(par, arg));
        } else {
            array_push(&node->args, parse_expression(par, 0));
        }

        if (! lex_try_eat(lex, ',')) break;
    }

    lex_eat_this(lex, ')');
    return complete_node(par, node);
}

static Ast *parse_prefix_op (Parser *par, AstTag tag) {
    Auto node = cast(AstBaseUnary*, make_node_by_tag(par, tag));
    TokenTag op = lex_eat(lex)->tag;
    node->op = parse_expression(par, prefix(op));
    return complete_node(par, node);
}

static Ast *parse_binary_op (Parser *par, AstTag tag, Ast *lhs) {
    Auto node = cast(AstBaseBinary*, make_node_lhs_by_tag(par, tag, lhs));
    node->op1 = lhs;
    TokenTag op = lex_eat(lex)->tag;
    node->op2 = parse_expression(par, op);
    return complete_node(par, node);
}

static Ast *parse_dot (Parser *par, Ast *lhs) {
    Auto node = make_node_lhs(par, AstDot, lhs);
    node->lhs = lhs;
    lex_eat_this(lex, '.');
    node->rhs = lex_eat_this(lex, TOKEN_IDENT)->str;
    mark_standalone_position(par, lhs);
    return complete_node(par, node);
}

static Ast *parse_builtin_print (Parser *par) {
    Auto node = make_node(par, AstBuiltinPrint);
    lex_eat_this(lex, '.');
    lex_eat_this(lex, TOKEN_IDENT);
    lex_eat_this(lex, '(');
    cast(AstBaseUnary*, node)->op = parse_expression(par, 0);
    lex_eat_this(lex, ')');
    return complete_node(par, node);
}

static Ast *parse_builtin_is_nil (Parser *par) {
    Auto node = make_node(par, AstBuiltinIsNil);
    lex_eat_this(lex, '.');
    lex_eat_this(lex, TOKEN_IDENT);
    lex_eat_this(lex, '(');
    cast(AstBaseUnary*, node)->op = parse_expression(par, 0);
    lex_eat_this(lex, ')');
    return complete_node(par, node);
}

static Ast *parse_builtin_val (Parser *par) {
    Auto node = make_node(par, AstBuiltinVal);
    lex_eat_this(lex, '.');
    lex_eat_this(lex, TOKEN_IDENT);
    lex_eat_this(lex, '(');
    cast(AstBaseUnary*, node)->op = parse_expression(par, 0);
    lex_eat_this(lex, ')');
    return complete_node(par, node);
}

static Ast *parse_special_float (Parser *par, F64 val) {
    Auto node = make_node(par, AstFloatLiteral);
    lex_eat_this(lex, '.');
    lex_eat_this(lex, TOKEN_IDENT);
    lex_eat_this(lex, '(');
    lex_eat_this(lex, ')');
    node->val = val;
    return complete_node(par, node);
}

static Ast *parse_builtin_fn_name (Parser *par) {
    Auto node = make_node(par, AstBuiltinFnName);
    lex_eat_this(lex, '.');
    lex_eat_this(lex, TOKEN_IDENT);
    lex_eat_this(lex, '(');
    lex_eat_this(lex, ')');
    return complete_node(par, node);
}

static Ast *parse_builtin_line (Parser *par) {
    Auto node = make_node(par, AstBuiltinLine);
    lex_eat_this(lex, '.');
    lex_eat_this(lex, TOKEN_IDENT);
    lex_eat_this(lex, '(');
    lex_eat_this(lex, ')');
    return complete_node(par, node);
}

static Ast *parse_builtin_file (Parser *par) {
    Auto node = make_node(par, AstBuiltinFile);
    lex_eat_this(lex, '.');
    lex_eat_this(lex, TOKEN_IDENT);
    lex_eat_this(lex, '(');
    lex_eat_this(lex, ')');
    return complete_node(par, node);
}

static Ast *parse_builtin_stack_trace (Parser *par) {
    Auto node = make_node(par, AstBuiltinStackTrace);
    lex_eat_this(lex, '.');
    lex_eat_this(lex, TOKEN_IDENT);
    lex_eat_this(lex, '(');
    lex_eat_this(lex, ')');
    return complete_node(par, node);
}

static Ast *parse_builtin_call (Parser *par) {
    Token *token = lex_peek_nth(lex, 2);

    if (token->tag != TOKEN_IDENT) par_error_pos(par, token->pos, "Expected identifier.");
    if (token->str == par->interns->builtin_print) return parse_builtin_print(par);
    if (token->str == par->interns->builtin_is_nil) return parse_builtin_is_nil(par);
    if (token->str == par->interns->builtin_val) return parse_builtin_val(par);
    if (token->str == par->interns->builtin_nan) return parse_special_float(par, NAN);
    if (token->str == par->interns->builtin_inf) return parse_special_float(par, INFINITY);
    if (token->str == par->interns->builtin_fn_name) return parse_builtin_fn_name(par);
    if (token->str == par->interns->builtin_file) return parse_builtin_file(par);
    if (token->str == par->interns->builtin_line) return parse_builtin_line(par);
    if (token->str == par->interns->builtin_stack_trace) return parse_builtin_stack_trace(par);

    par_error(par, "Unknown builtin.");
}

static Ast *parse_option_type (Parser *par) {
    Auto node = make_node(par, AstOptionType);
    lex_eat_this(lex, '?');
    cast(AstBaseUnary*, node)->op = parse_expression(par, prefix('?'));
    return complete_node(par, node);
}

static Ast *parse_nil (Parser *par) {
    Auto node = make_node(par, AstNil);
    lex_eat_this(lex, TOKEN_NIL);
    return complete_node(par, node);
}

static Ast *parse_typeof (Parser *par) {
    Auto node = make_node(par, AstTypeof);
    lex_eat_this(lex, TOKEN_TYPEOF);
    lex_eat_this(lex, '(');
    cast(AstBaseUnary*, node)->op = parse_expression(par, 0);
    lex_eat_this(lex, ')');
    mark_standalone_position(par, cast(AstBaseUnary*, node)->op);
    return complete_node(par, node);
}

static Ast *parse_expression_with_lhs (Parser *par, Ast *lhs) {
    switch (lex_peek(lex)->tag) {
    case '.':                 return parse_dot(par, lhs);
    case '(':                 return parse_call(par, lhs);
    case '{':                 return parse_record_literal(par, lhs);
    case '[':                 return parse_array_literal_or_index(par, lhs);
    case '+':                 return parse_binary_op(par, AST_ADD, lhs);
    case '-':                 return parse_binary_op(par, AST_SUB, lhs);
    case '*':                 return parse_binary_op(par, AST_MUL, lhs);
    case '/':                 return parse_binary_op(par, AST_DIV, lhs);
    case '%':                 return parse_binary_op(par, AST_MOD, lhs);
    case '<':                 return parse_binary_op(par, AST_LESS, lhs);
    case '>':                 return parse_binary_op(par, AST_GREATER, lhs);
    case TOKEN_OR:            return parse_binary_op(par, AST_LOGICAL_OR, lhs);
    case TOKEN_AND:           return parse_binary_op(par, AST_LOGICAL_AND, lhs);
    case TOKEN_2EQUAL:        return parse_binary_op(par, AST_EQUAL, lhs);
    case TOKEN_NOT_EQUAL:     return parse_binary_op(par, AST_NOT_EQUAL, lhs);
    case TOKEN_LESS_EQUAL:    return parse_binary_op(par, AST_LESS_EQUAL, lhs);
    case TOKEN_GREATER_EQUAL: return parse_binary_op(par, AST_GREATER_EQUAL, lhs);
    default:                  badpath;
    }
}

static Ast *parse_expression_without_lhs (Parser *par) {
    switch (lex_peek(lex)->tag) {
    case '?':                  return parse_option_type(par);
    case '-':                  return parse_negate(par);
    case '$':                  return parse_poly_type(par, false);
    case '(':                  return parse_tuple_or_parens(par);
    case '[':                  return parse_array_literal_or_type(par);
    case '!':                  return parse_prefix_op(par, AST_NOT);
    case '.':                  return parse_builtin_call(par);
    case TOKEN_TYPEOF:         return parse_typeof(par);
    case TOKEN_NIL:            return parse_nil(par);
    case TOKEN_F64_LITERAL:    return parse_float_literal(par);
    case TOKEN_FALSE:          return parse_bool_literal(par, TOKEN_FALSE);
    case TOKEN_FN:             return parse_fn(par, true);
    case TOKEN_FN_TYPE:        return parse_fn_type(par);
    case TOKEN_STRING_LITERAL: return parse_string_literal(par);
    case TOKEN_TRUE:           return parse_bool_literal(par, TOKEN_TRUE);
    case TOKEN_U64_LITERAL:    return parse_int_literal(par);
    case TOKEN_IDENT:          return parse_ident(par);
    default:                   return 0;
    }
}

// The argument "left_op" can be one of the following:
//
//     1. A TokenTag representing the operator to the left of the expresion.
//     2. A value given by prefix() representing a prefix op to the left.
//     3. The value 0 indicating that there is no operator to the left.
//     4. The value 1 indicating that there is no operator to the left,
//        and that we should stop parsing when we see a '{'.
//
static Ast *try_parse_expression (Parser *par, U64 left_op) {
    Ast *result = parse_expression_without_lhs(par);
    if (! result) return 0;

    U64 left_prec = precedence_of(left_op);

    Bool brace_ends_expression = par->brace_ends_expression;
    if (left_op == 0) par->brace_ends_expression = false;

    while (true) {
        TokenTag right_op = lex_peek(lex)->tag;
        U64 p = precedence_of(right_op);
        if ((right_op == '{') && par->brace_ends_expression) break;
        if (p < left_prec || (p == left_prec && is_left_associative(right_op))) break;
        result = parse_expression_with_lhs(par, result);
    }

    par->brace_ends_expression = brace_ends_expression;
    return result;
}

static Ast *parse_expression (Parser *par, U64 left_op) {
    Ast *e = try_parse_expression(par, left_op);
    if (! e) par_error(par, "Expected expression.");
    return e;
}

// Use this function when parsing an expression that could be
// terminated by an opening brace. This fixes an ambiguity in
// which the opening brace is interpreted as a struct literal
// rather than a construct that appears after the expression.
//
// For example, the following code:
//
//     if 1 < Foo {}
//
// would get parsed as:
//
//     if (1 < Foo{}) [expecting if body here]
//
// instead of:
//
//     if (1 < Foo) {}
//
// This function disables the struct literal operator '{', and
// whenever try_parse_expression() is called with left_op == 0
// it will temporarily re-enable this operator. For example,
// this happens when we start parsing an expression in parens.
// Thus you can still put struct literals in places like an if
// condition by wrapping it in parens:
//
//     if 1 < Foo{ x = 42 }.x   {} // Doesn't work.
//     if (1 < Foo{ x = 42 }.x) {} // Ok.
//
static Ast *try_parse_expression_before_brace (Parser *par) {
    Bool prev = par->brace_ends_expression;
    par->brace_ends_expression = true;
    Ast *e = try_parse_expression(par, 1);
    par->brace_ends_expression = prev;
    return e;
}

static Ast *parse_expression_before_brace (Parser *par) {
    Ast *e = try_parse_expression_before_brace(par);
    if (! e) par_error(par, "Expected expression.");
    return e;
}

static Void try_parse_expression_list (Parser *par, ArrayAst *out) {
    while (true) {
        Ast *e = try_parse_expression(par, 0);
        if (! e) break;
        array_push(out, e);
        if (! lex_try_eat(lex, ',')) break;
    }
}

static Ast *parse_return (Parser *par) {
    Auto node = make_node(par, AstReturn);
    lex_eat_this(lex, TOKEN_RETURN);
    node->result = try_parse_expression(par, 0);
    lex_eat_this(lex, ';');
    return complete_node(par, node);
}

static Ast *parse_break (Parser *par) {
    Auto node = make_node(par, AstBreak);
    lex_eat_this(lex, TOKEN_BREAK);
    try_parse_attributes(cast(Ast*, node)->id,);
    Token *token = lex_try_eat(lex, TOKEN_IDENT);
    if (token) node->label = token->str;
    lex_eat_this(lex, ';');
    return complete_node(par, node);
}

static Ast *parse_continue (Parser *par) {
    Auto node = make_node(par, AstContinue);
    lex_eat_this(lex, TOKEN_CONTINUE);
    try_parse_attributes(cast(Ast*, node)->id,);
    Token *token = lex_try_eat(lex, TOKEN_IDENT);
    if (token) node->label = token->str;
    lex_eat_this(lex, ';');
    return complete_node(par, node);
}

static Ast *parse_while (Parser *par) {
    Auto node = make_node(par, AstWhile);
    lex_eat_this(lex, TOKEN_WHILE);

    try_parse_attributes(cast(Ast*, node)->id, {
        if (lex_try_peek(lex, TOKEN_IDENT)) node->label = lex_eat(lex)->str;
    });

    node->cond = parse_expression_before_brace(par);
    parse_block_out(par, &node->statements);
    return complete_node(par, node);
}

static Ast *parse_if (Parser *par) {
    Auto node = make_node(par, AstIf);
    lex_eat_this(lex, TOKEN_IF);
    try_parse_attributes(cast(Ast*, node)->id,);
    node->cond = parse_expression_before_brace(par);
    node->then_arm = parse_block(par);
    if (lex_try_eat(lex, TOKEN_ELSE)) node->else_arm = lex_try_peek(lex, TOKEN_IF) ? parse_if(par) : parse_block(par);
    return complete_node(par, node);
}

static Ast *parse_assign (Parser *par, Ast *lhs, AstTag fused_op) {
    Auto result = cast(AstBaseBinary*, make_node_lhs(par, AstAssign, lhs));
    lex_eat(lex);
    result->op1 = lhs;
    result->op2 = parse_expression(par, 0);
    cast(AstAssign*, result)->fused_op = fused_op;
    return complete_node(par, result);
}

static Void parse_block_out (Parser *par, ArrayAst *out) {
    if (lex_try_eat(lex, '{')) {
        while (true) {
            Ast *stmt = parse_statement(par);
            if (! stmt) break;
            array_push(out, stmt);
        }

        lex_eat_this(lex, '}');
    } else {
        lex_eat_this(lex, TOKEN_DO);
        Ast *stmt = parse_statement(par);
        if (! stmt) par_error(par, "Expected statement.");
        array_push(out, stmt);
    }
}

static Ast *parse_block (Parser *par) {
    Auto node = make_node(par, AstBlock);
    parse_block_out(par, &node->statements);
    return complete_node(par, node);
}

static Ast *parse_defer (Parser *par) {
    Auto node = make_node(par, AstDefer);
    lex_eat_this(lex, TOKEN_DEFER);
    try_parse_attributes(cast(Ast*, node)->id,);

    if (lex_try_peek(lex, TOKEN_DO)) {
        node->stmt = parse_block(par);
    } else if (lex_try_peek(lex, '{')) {
        node->stmt = parse_block(par);
    } else {
        node->stmt = try_parse_expression(par, 0);
        if (! node->stmt) par_error(par, "Expected block or expression.");
        lex_eat_this(lex, ';');
    }

    return complete_node(par, node);
}

static Ast *parse_type_alias (Parser *par) {
    Auto node = make_node(par, AstTypeAlias);
    lex_eat_this(lex, TOKEN_TYPE);
    parse_attributes(cast(Ast*, node)->id, eat_attribute(alias));
    node->name = lex_eat_this(lex, TOKEN_IDENT)->str;
    lex_eat_this(lex, '=');
    node->val = parse_expression(par, 0);
    lex_eat_this(lex, ';');
    return complete_node(par, node);
}

static Ast *parse_type_distinct (Parser *par) {
    Auto node = make_node(par, AstTypeDistinct);
    lex_eat_this(lex, TOKEN_TYPE);
    try_parse_attributes(cast(Ast*, node)->id,);
    node->name = lex_eat_this(lex, TOKEN_IDENT)->str;
    lex_eat_this(lex, '=');
    node->val = parse_expression(par, 0);
    lex_eat_this(lex, ';');
    return complete_node(par, node);
}

static Ast *parse_statement (Parser *par) {
    Ast *result = 0;

    switch (lex_peek(lex)->tag) {
    case TOKEN_EOF: return 0;
    case ';':            while (lex_try_eat(lex, ';')); return parse_statement(par);
    case '{':            result = parse_block(par); break;
    case TOKEN_DO:       result = parse_block(par); break;
    case TOKEN_BREAK:    result = parse_break(par); break;
    case TOKEN_CONTINUE: result = parse_continue(par); break;
    case TOKEN_DEFER:    result = parse_defer(par); break;
    case TOKEN_FN:       result = parse_fn(par, false); break;
    case TOKEN_RETURN:   result = parse_return(par); break;
    case TOKEN_ENUM:     result = parse_enum(par); break;
    case TOKEN_RECORD:   result = lex_try_peek_nth(lex, 3, '(') ? parse_record_poly(par) : parse_record(par); break;
    case TOKEN_VAR:      result = parse_var_def(par, true, true); result->flags |= AST_IS_LOCAL_VAR; break;
    case TOKEN_WHILE:    result = parse_while(par); break;
    case TOKEN_TYPE:     result = starts_with_attribute(alias) ? parse_type_alias(par) : parse_type_distinct(par); break;
    case TOKEN_IF:       result = parse_if(par); break;
    default: {
        Ast *n = try_parse_expression(par, 0);
        if (! n) return 0;

        switch (lex_peek(lex)->tag) {
        case '=':                   result = parse_assign(par, n, AST_ASSIGN); break;
        case TOKEN_ASTERISK_EQUAL:  result = parse_assign(par, n, AST_MUL); break;
        case TOKEN_MINUS_EQUAL:     result = parse_assign(par, n, AST_SUB); break;
        case TOKEN_PERCENT_EQUAL:   result = parse_assign(par, n, AST_MOD); break;
        case TOKEN_PLUS_EQUAL:      result = parse_assign(par, n, AST_ADD); break;
        case TOKEN_SLASH_EQUAL:     result = parse_assign(par, n, AST_DIV); break;
        default:                    result = n; break;
        }

        lex_eat_this(lex, ';');
    } break;
    }

    mark_standalone_position(par, result);
    return result;
}

static Ast *parse_top_statement (Parser *par) {
    Ast *result = 0;

    switch (lex_peek(lex)->tag) {
    case ';':          while (lex_try_eat(lex, ';')); result = parse_top_statement(par); break;
    case TOKEN_ENUM:   result = parse_enum(par); break;
    case TOKEN_RECORD: result = lex_try_peek_nth(lex, 3, '(') ? parse_record_poly(par) : parse_record(par); break;
    case TOKEN_FN:     result = parse_fn(par, false); break;
    case TOKEN_TYPE:   result = starts_with_attribute(alias) ? parse_type_alias(par) : parse_type_distinct(par); break;
    case TOKEN_VAR: {
       result = parse_var_def(par, true, true);
       result->flags |= AST_IS_GLOBAL_VAR;
       cast(AstVarDef*, result)->init->flags |= AST_MUST_EVAL;
    } break;
    default: return 0;
    }

    mark_standalone_position(par, result);
    return result;
}

AstFile *par_parse_file (Parser *par, IString *filepath) {
    String content = fs_read_entire_file(par->mem, *filepath, 0);
    if (! content.data) return 0;

    par->file = cast(AstFile*, ast_alloc(par->mem, AST_FILE, 0));
    par->file->path = filepath;
    par->file->content = content;
    lex_reset(lex, par->file, 0);

    while (true) {
        Ast *stmt = parse_top_statement(par);
        if (! stmt) break;
        array_push(&par->file->statements, stmt);
    }

    if (! lex_try_peek(lex, TOKEN_EOF)) par_error(par, "Invalid file level statement.");
    return cast(AstFile*, complete_node(par, par->file));
}

Parser *par_new (Mem *mem, Interns *interns) {
    Auto par = mem_new(mem, Parser);
    par->mem = mem;
    par->interns = interns;
    par->lexer = lex_new(interns, mem);
    array_init(&par->arg_context_pool, mem);
    array_init(&par->arg_context_stack, mem);
    map_init(&par->notes, mem);
    return par;
}
