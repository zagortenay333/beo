#include "base/mem.h"
#include "base/log.h"
#include "os/fs.h"
#include "compiler/ast.h"
#include "compiler/interns.h"
#include "compiler/lexer.h"
#include "compiler/parser.h"

istruct (Parser) {
    Mem *mem;
    AstFile *file;
    Interns *interns;
    Lexer *lexer;
    Bool brace_ends_expression;
};

#define lex (par->lexer)

static Ast *parse_block (Parser *par);
static Void parse_block_out (Parser *par, ArrayAst *);
static Ast *parse_statement (Parser *par);
static Ast *parse_expression (Parser *par, U64 left_op);
static Ast *try_parse_expression (Parser *par, U64 left_op);
static Ast *parse_expression_before_brace (Parser *par);
static Void try_parse_expression_list (Parser *par, ArrayAst *out);
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
    case TOKEN_IDENT: return parse_var_def(par, true, false);
    default:          return 0;
    }
}

static Ast *parse_record (Parser *par) {
    Auto node = make_node(par, AstRecord);

    lex_eat_this(lex, TOKEN_RECORD);
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
    }

    node->name = lex_eat_this(lex, TOKEN_IDENT)->str;
    if (lex_try_eat(lex, ':')) node->constraint = parse_expression(par, 0);
    if (lex_try_eat(lex, '=')) node->init = parse_expression(par, 0);
    if (!node->constraint && !node->init) lex_eat_this(lex, ':');
    if (with_semicolon) lex_eat_this(lex, ';');

    return complete_node(par, node);
}

static Ast *parse_fn (Parser *par) {
    Auto node = make_node(par, AstFn);
    lex_eat_this(lex, TOKEN_FN);
    node->name = lex_eat_this(lex, TOKEN_IDENT)->str;

    if (lex_try_eat(lex, '(')) {
        while (true) {
            if (! lex_try_peek(lex, TOKEN_IDENT)) break;
            Ast *arg = parse_var_def(par, false, false);
            arg->flags |= AST_IS_FN_ARG | AST_IS_LOCAL_VAR;
            array_push(&cast(AstBaseFn*, node)->inputs, arg);
            if (! lex_try_eat(lex, ',')) break;
        }

        lex_eat_this(lex, ')');
    }

    if (lex_try_eat(lex, TOKEN_ARROW)) {
        cast(AstBaseFn*, node)->output = parse_expression_before_brace(par);
    }

    parse_block_out(par, &node->statements);

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
        lex_eat_this(lex, ']');
        return complete_node(par, node);
    }
}

static Ast *parse_parens (Parser *par) {
    SrcPos p1 = lex_eat_this(lex, '(')->pos;
    Ast *node = parse_expression(par, 0);
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

static Ast *parse_builtin_call (Parser *par) {
    Token *token = lex_peek_nth(lex, 2);

    if (token->tag != TOKEN_IDENT) par_error_pos(par, token->pos, "Expected identifier.");

    if (token->str == par->interns->builtin_print) return parse_builtin_print(par);

    par_error(par, "Unknown builtin.");
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
    case '-':                  return parse_negate(par);
    case '(':                  return parse_parens(par);
    case '[':                  return parse_array_literal_or_type(par);
    case '!':                  return parse_prefix_op(par, AST_NOT);
    case '.':                  return parse_builtin_call(par);
    case TOKEN_F64_LITERAL:    return parse_float_literal(par);
    case TOKEN_FALSE:          return parse_bool_literal(par, TOKEN_FALSE);
    case TOKEN_FN:             return parse_fn(par);
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
    Token *token = lex_try_eat(lex, TOKEN_IDENT);
    if (token) node->label = token->str;
    lex_eat_this(lex, ';');
    return complete_node(par, node);
}

static Ast *parse_continue (Parser *par) {
    Auto node = make_node(par, AstContinue);
    lex_eat_this(lex, TOKEN_CONTINUE);
    Token *token = lex_try_eat(lex, TOKEN_IDENT);
    if (token) node->label = token->str;
    lex_eat_this(lex, ';');
    return complete_node(par, node);
}

static Ast *parse_while (Parser *par) {
    Auto node = make_node(par, AstWhile);
    lex_eat_this(lex, TOKEN_WHILE);
    node->cond = parse_expression_before_brace(par);
    parse_block_out(par, &node->statements);
    return complete_node(par, node);
}

static Ast *parse_if (Parser *par) {
    Auto node = make_node(par, AstIf);
    lex_eat_this(lex, TOKEN_IF);
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

static Ast *parse_block (Parser *par) {
    Auto node = make_node(par, AstBlock);
    parse_block_out(par, &node->statements);
    return complete_node(par, node);
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

static Ast *parse_statement (Parser *par) {
    Ast *result = 0;

    switch (lex_peek(lex)->tag) {
    case TOKEN_EOF: return 0;
    case ';':            while (lex_try_eat(lex, ';')); return parse_statement(par);
    case '{':            result = parse_block(par); break;
    case TOKEN_BREAK:    result = parse_break(par); break;
    case TOKEN_CONTINUE: result = parse_continue(par); break;
    case TOKEN_FN:       result = parse_fn(par); break;
    case TOKEN_RETURN:   result = parse_return(par); break;
    case TOKEN_RECORD:   result = parse_record(par); break;
    case TOKEN_VAR:      result = parse_var_def(par, true, true); result->flags |= AST_IS_LOCAL_VAR; break;
    case TOKEN_WHILE:    result = parse_while(par); break;
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

    return result;
}

static Ast *parse_top_statement (Parser *par) {
    switch (lex_peek(lex)->tag) {
    case ';':          while (lex_try_eat(lex, ';')); return parse_top_statement(par);
    case TOKEN_RECORD: return parse_record(par); break;
    case TOKEN_FN:     return parse_fn(par); break;
    case TOKEN_VAR: {
       Ast *result = parse_var_def(par, true, true);
       result->flags |= AST_IS_GLOBAL_VAR;
       if (cast(AstVarDef*, result)->init) cast(AstVarDef*, result)->init->flags |= AST_MUST_EVAL;
       return result;
    }
    default: return 0;
    }
}

AstFile *par_parse_file (Parser *par, IString *filepath) {
    String content = fs_read_entire_file(mem_base(par->mem), *filepath, 0);
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
    return par;
}
