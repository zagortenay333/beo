#pragma once

#include "base/log.h"
#include "base/core.h"
#include "base/string.h"

istruct (Ast);
istruct (AstFile);
istruct (Interns);

// X(keyword, uppercase_keyword)
//
// To add a new keyword just add a new entry into this list.
// After that whenever the lexer encounters this keyword it
// emits a token with tag TOKEN_##uppercase_keyword.
#define EACH_KEYWORD(X)\
    X(Fn, FN_TYPE)\
    X(break, BREAK)\
    X(continue, CONTINUE)\
    X(do, DO)\
    X(else, ELSE)\
    X(enum, ENUM)\
    X(false, FALSE)\
    X(fn, FN)\
    X(if, IF)\
    X(nil, NIL)\
    X(record, RECORD)\
    X(return, RETURN)\
    X(true, TRUE)\
    X(var, VAR)\
    X(while, WHILE)

// X(tag value, TokenTag, stringified tag)
//
// This is a list of mostly sigil tokens and other special
// kinds of tokens. For ASCII sigils the tag value matches
// the ASCII value so that char literals like '!' can be
// used instead of TOKEN_EXCLAMATION.
#define EACH_CORE_TOKEN(X)\
    X(0,    TOKEN_EOF, "EOF")\
    X('!',  TOKEN_EXCLAMATION, "!")\
    X('"',  TOKEN_DOUBLE_QUOTE, "\"")\
    X('#',  TOKEN_HASH, "#")\
    X('$',  TOKEN_DOLLAR, "$")\
    X('%',  TOKEN_PERCENT, "%")\
    X('&',  TOKEN_AMPERSAND, "&")\
    X('\'', TOKEN_SINGLE_QUOTE, "'")\
    X('(',  TOKEN_OPEN_PAREN, "(")\
    X(')',  TOKEN_CLOSED_PAREN, ")")\
    X('*',  TOKEN_ASTERISK, "*")\
    X('+',  TOKEN_PLUS, "+")\
    X(',',  TOKEN_COMMA, ",")\
    X('-',  TOKEN_MINUS, "-")\
    X('.',  TOKEN_DOT, ".")\
    X('/',  TOKEN_SLASH, "/")\
    X(':',  TOKEN_COLON, ":")\
    X(';',  TOKEN_SEMICOLON, ";")\
    X('<',  TOKEN_LESS, "<")\
    X('=',  TOKEN_EQUAL, "=")\
    X('>',  TOKEN_GREATER, ">")\
    X('?',  TOKEN_QUESTION_MARK, "?")\
    X('@',  TOKEN_AT, "@")\
    X('[',  TOKEN_OPEN_BRACKET, "[")\
    X('\\', TOKEN_BACKSLASH, "\\")\
    X(']',  TOKEN_CLOSED_BRACKET, "]")\
    X('^',  TOKEN_CARET, "^")\
    X('_',  TOKEN_UNDERSCORE, "_")\
    X('`',  TOKEN_BACKTICK, "`")\
    X('{',  TOKEN_OPEN_BRACE, "{")\
    X('|',  TOKEN_VBAR, "|")\
    X('}',  TOKEN_CLOSED_BRACE, "}")\
    X('~',  TOKEN_TILDE, "~")\
    X(256,  TOKEN_IDENT, "identifier")\
    X(257,  TOKEN_U64_LITERAL, "U64 literal")\
    X(258,  TOKEN_F64_LITERAL, "F64 literal")\
    X(259,  TOKEN_STRING_LITERAL, "String literal")\
    X(260,  TOKEN_2EQUAL, "==")\
    X(261,  TOKEN_NOT_EQUAL, "!=")\
    X(262,  TOKEN_LESS_EQUAL, "<=")\
    X(263,  TOKEN_GREATER_EQUAL, ">=")\
    X(266,  TOKEN_AND, "&&")\
    X(267,  TOKEN_OR, "||")\
    X(268,  TOKEN_PLUS_EQUAL, "+=")\
    X(269,  TOKEN_MINUS_EQUAL, "-=")\
    X(270,  TOKEN_ASTERISK_EQUAL, "*=")\
    X(271,  TOKEN_SLASH_EQUAL, "/=")\
    X(272,  TOKEN_PERCENT_EQUAL, "%=")\
    X(278,  TOKEN_ARROW, "->")\
    X(279,  TOKEN_FAT_ARROW, "=>")

// These are builtin functions that can be invoked via
// the prefix dot operator like .sizeof().
#define EACH_BUILTIN(X)\
    X(file)\
    X(fn_name)\
    X(inf)\
    X(is_nil)\
    X(line)\
    X(nan)\
    X(print)\
    X(stack_trace)\
    X(val)

fenum (TokenTag, U64) {
    #define X(VAL, TAG, ...) TAG = VAL,
        EACH_CORE_TOKEN(X)
    #undef X

    #define X(_, K) TOKEN_##K,
        EACH_KEYWORD(X)
    #undef X

    TOKEN_TAG_COUNT
};

istruct (Token) {
    TokenTag tag;
    SrcPos pos;
    String txt; // Slice into source code.

    union {
        U64 u64;     // For TOKEN_U64_LITERAL.
        F64 f64;     // For TOKEN_F64_LITERAL.
        IString *str; // Escaped string of TOKEN_STRING_LITERAL.
    };
};

istruct (Lexer);

// Instead of a giant array of tokens, we maintain
// a small ring buffer of size MAX_TOKEN_LOOKAHEAD.
// This means that all token structs get eventually
// overwritten, so don't hold them for long or copy.
#define MAX_TOKEN_LOOKAHEAD 8u

extern CString lex_tag_to_str [TOKEN_TAG_COUNT];

#define lex_is_dec_digit(c)  (c >= '0' && c <= '9')
#define lex_is_whitespace(c) (c == ' ' || c == '\t' || c == '\r' || c == '\n')
#define lex_is_alpha(c)      ((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_' || cast(I32, c) > 127)

Lexer *lex_new          (Interns *, Mem *);
Void   lex_reset        (Lexer *, AstFile *, SrcPos *);
Token *lex_peek         (Lexer *);
Token *lex_peek_this    (Lexer *, TokenTag);
Token *lex_peek_nth     (Lexer *, U64 nth); // 1-indexed
Token *lex_try_peek     (Lexer *, TokenTag);
Token *lex_try_peek_nth (Lexer *, U64 nth, TokenTag); // 1-indexed
Token *lex_eat          (Lexer *);
Token *lex_eat_this     (Lexer *, TokenTag);
Token *lex_try_eat      (Lexer *, TokenTag);
String lex_escape_str   (Lexer *, SrcPos *, String, Bool just_indent);
SrcPos lex_get_prev_pos (Lexer *);
