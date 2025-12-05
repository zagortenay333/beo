#include "base/mem.h"
#include "compiler/ast.h"
#include "compiler/lexer.h"
#include "compiler/interns.h"

istruct (Lexer) {
    Mem *mem;
    Interns *interns;
    AstFile *file;

    U64 line;
    Char *eof;
    Char *cursor;
    SrcPos prev_pos; // Pos of last eaten token.

    U64   ring_count;
    U64   ring_cursor;
    Token ring[MAX_TOKEN_LOOKAHEAD];

    AString scratch;
};

CString lex_tag_to_str [TOKEN_TAG_COUNT] = {
    #define X(_, tag, name) [tag] = name,
        EACH_CORE_TOKEN(X)
    #undef X

    #define X(key, KEY) [TOKEN_##KEY] = #key,
        EACH_KEYWORD(X)
    #undef X
};

Noreturn
static Void lex_error Fmt(3, 4) (Lexer *lex, SrcPos pos, CString fmt, ...) {
    tmem_new(tm);

    AString msg = astr_new(tm);
    astr_push_cstr(&msg, TERM_RED("ERROR(Lexer): "));

    AstFile *f = lex->file;
    SrcLog *slog = slog_new(tm, slog_default_config);
    slog_add_src(slog, cast(Ast*, f)->id, *f->path, f->content);
    slog_add_pos(slog, cast(Ast*, f)->id, pos);

    astr_push_fmt_vam(&msg, fmt);
    array_push_n(&msg, '\n', '\n');\
    slog_flush(slog, &msg);
    astr_println(&msg);
    panic();
}

// This is 0-indexed.
static I8 peek_nth_char (Lexer *lex, U64 lookahead) {
    U64 left_in_buf = (U64)(lex->eof - lex->cursor);
    return (lookahead < left_in_buf) ? lex->cursor[lookahead] : -1;
}

static I8 peek_char (Lexer *lex) {
    return (lex->cursor < lex->eof) ? *lex->cursor : 0;
}

static I8 eat_char (Lexer *lex) {
    if (lex->cursor == lex->eof) return 0;
    I8 result = *lex->cursor++;
    if (result == '\n') lex->line++;
    return result;
}

static U64 eat_char_greedy (Lexer *lex) {
    if (lex->cursor == lex->eof) return 0;
    U64 n_eaten = 1;
    I8 c = eat_char(lex);
    while (peek_char(lex) == c) { eat_char(lex); n_eaten++; }
    return n_eaten;
}

static Void eat_multi_line_comment (Lexer *lex) {
    SrcPos pos = {
        .offset     = lex->cursor - lex->file->content.data,
        .length     = 1,
        .first_line = lex->line,
        .last_line  = lex->line,
    };

    eat_char(lex); // Eat the '/'.

    U64 n_open_comments = 1;
    U64 n_asterisks = eat_char_greedy(lex);

    while (n_open_comments) {
        switch (peek_char(lex)) {
        case '*':
            if (eat_char_greedy(lex) == n_asterisks && eat_char(lex) == '/') n_open_comments--;
            break;
        case '/':
            eat_char(lex);
            if (peek_char(lex) == '*' && eat_char_greedy(lex) == n_asterisks) n_open_comments++;
            break;
        case 0:
            lex_error(lex, pos, "Unterminated comment. " TERM_CYAN("(Note that asterisks must match: /* */ /** **/ ..."));
            return;
        default:
            eat_char(lex);
            break;
        }
    }
}

static Void eat_whitespace (Lexer *lex) {
    while (true) {
        I8 c = peek_char(lex);

        if (lex_is_whitespace(c)) {
            eat_char(lex);
        } else if (c == '/') {
            I8 c = peek_nth_char(lex, 1);
            if (c == '/')      while (true) { c = eat_char(lex); if (c == '\n' || c == 0) break; }
            else if (c == '*') eat_multi_line_comment(lex);
            else               break;
        } else {
            break;
        }
    }
}

String lex_escape_str (Lexer *lex, SrcPos *error_pos, String str, Bool just_indent) {
    AString astr     = astr_new_cap(lex->mem, str.count);
    Char *cursor     = str.data;
    Char *end_cursor = str.data + str.count;
    Bool eat_indent  = (cursor[0] == '\\' && cursor[1] == '|');

    if (eat_indent) {
        cursor += 2;
        if (*cursor == ' ') cursor++;
    }

    Char *prev_pos = cursor;

    #define flush(LEN) {\
        U64 c = cast(U64, LEN);\
        if (c) astr_push_str(&astr, (String){ .data=prev_pos, .count=c });\
    }

    while (cursor < end_cursor) {
        switch (*cursor++) {
        case '\\': {
            if (just_indent) break;

            flush(cursor - prev_pos - 1);
            prev_pos = cursor;

            switch (*cursor++) {
            case 't': astr_push_byte(&astr, '\t'); prev_pos++; break;
            case 'n': astr_push_byte(&astr, '\n'); prev_pos++; break;
            case 'r': astr_push_byte(&astr, '\r'); prev_pos++; break;
            case '"': astr_push_byte(&astr, '"');  prev_pos++; break;
            }
        } break;

        case '\n': {
            if (! eat_indent) break;

            flush(cursor - prev_pos);
            while (*cursor == ' ' || *cursor == '\t') cursor++;
            if (*cursor == '"') { prev_pos = cursor; break; }

            if (*cursor++ != '|') {
                error_pos->length = 1;
                error_pos->last_line = error_pos->first_line;
                lex_error(lex, *error_pos, "Each line of the string literal must start with a '|' character.");
            }

            if (*cursor == ' ' || *cursor == '\t') cursor++;
            prev_pos = cursor;
        } break;
        }
    }

    flush(cursor - prev_pos);
    #undef flush
    return astr_to_str(&astr);
}

static Void build_string_token (Lexer *lex, Token *token) {
    token->tag = TOKEN_STRING_LITERAL;

    Bool escaped = false;

    while (true) {
        switch (eat_char(lex)) {
        case '"':  goto brk;
        case '\\': escaped = true; eat_char(lex); break;
        case 0:
            token->pos.length = 1;
            token->pos.last_line = token->pos.first_line;
            lex_error(lex, token->pos, "Unterminated string literal.");
        }
    } brk:;

    token->txt.count = lex->cursor - token->txt.data;
    String str = { .data = (token->txt.data + 1), .count = (token->txt.count - 2) };
    token->str = intern_str(lex->interns, escaped ? lex_escape_str(lex, &token->pos, str, false) : str);
}

static Void build_raw_string_token (Lexer *lex, Token *token) {
    token->tag = TOKEN_STRING_LITERAL;

    eat_char(lex); // Backslash.

    U64 n_stars   = eat_char_greedy(lex);
    Bool indented = (peek_char(lex) == '\\') && (peek_nth_char(lex, 1) == '|');
    String str    = { .data = lex->cursor };

    while (true) {
        I8 c = eat_char(lex);

        if ((c == '\\') &&
            (peek_char(lex) == '*') &&
            (eat_char_greedy(lex) == n_stars) &&
            (peek_char(lex) == '"')
        ) {
            eat_char(lex);
            break;
        } else if (c == 0) {
            token->pos.length = 1;
            token->pos.last_line = token->pos.first_line;
            lex_error(lex, token->pos, "Unterminated raw string literal.\n\n"
                                       TERM_CYAN("NOTE: ") "It must start and end with same star count: " TERM_GREEN("\"\\**My string\\**\""));
        }
    }

    str.count = lex->cursor - str.data - n_stars - 2;
    token->txt.count = lex->cursor - token->txt.data;
    token->str = intern_str(lex->interns, indented ? lex_escape_str(lex, &token->pos, str, true) : str);
}

static Void eat_identifier (Lexer *lex, Token *token) {
    while (true) {
        U64 c = peek_char(lex);
        if (!lex_is_alpha(c) && !lex_is_dec_digit(c)) break;
        eat_char(lex);
        token->txt.count++;
    }
}

static Void build_identifier_token (Lexer *lex, Token *token) {
    eat_identifier(lex, token);
    token->str = intern_str(lex->interns, token->txt);

    #define X(_, K) else if (token->str == lex->interns->K) token->tag = TOKEN_##K;
        if (0); EACH_KEYWORD(X) else token->tag = TOKEN_IDENT;
    #undef X
}

static Void build_char_token (Lexer *lex, Token *token) {
    token->tag = TOKEN_U64_LITERAL;

    if (peek_char(lex) == '\\') {
        eat_char(lex);
        int c = eat_char(lex);

        switch (c) {
        case '0': token->u64 = 0;    break;
        case 't': token->u64 = '\t'; break;
        case 'n': token->u64 = '\n'; break;
        case 'r': token->u64 = '\r'; break;
        default:  token->u64 = c;    break;
        }
    } else {
        token->u64 = eat_char(lex);
    }

    if (eat_char(lex) != '\'') {
        token->pos.last_line = lex->line;
        token->pos.length = lex->cursor - token->txt.data - 1;
        lex_error(lex, token->pos, "Character literal missing closing quote.");
    }

    token->txt.count = lex->cursor - token->txt.data;
}

static U64 digit_to_val (U64 d) {
    if (d >= 'a' && d <= 'z') return d - 87;
    if (d >= 'A' && d <= 'Z') return d - 55;
    if (d >= '0' && d <= '9') return d - 48;
    return UINT32_MAX;
}

static Void eat_digits (Lexer *lex, U64 base) {
    while (true) {
        I8 c = peek_char(lex);

        if (c == '_') {
            eat_char(lex);
        } else if (digit_to_val(c) >= base) {
            break;
        } else {
            astr_push_byte(&lex->scratch, eat_char(lex));
        }
    }
}

static Void build_int_token (Lexer *lex, Token *token, U64 base) {
    lex->scratch.count = 0;
    eat_digits(lex, base);

    if (peek_char(lex) == '.' && base == 10 && lex_is_dec_digit(peek_nth_char(lex, 1))) {
        token->tag = TOKEN_F64_LITERAL;
        astr_push_byte(&lex->scratch, eat_char(lex));
        eat_digits(lex, base);

        I8 c = peek_char(lex);
        if (c == 'e' || c == 'E') {
            I8 c2 = peek_nth_char(lex, 1);

            if (lex_is_dec_digit(c2)) {
                astr_push_byte(&lex->scratch, eat_char(lex));
                eat_digits(lex, base);
            } else if (c2 == '-' && lex_is_dec_digit(peek_nth_char(lex, 2))) {
                astr_push_byte(&lex->scratch, eat_char(lex));
                astr_push_byte(&lex->scratch, eat_char(lex));
                eat_digits(lex, base);
            }
        }

        astr_push_byte(&lex->scratch, 0);
        if (! str_to_f64(lex->scratch.data, &token->f64)) goto error;
    } else {
        token->tag = TOKEN_U64_LITERAL;
        astr_push_byte(&lex->scratch, 0);
        if (! str_to_u64(lex->scratch.data, &token->u64, base)) goto error;
    }

    token->txt.count = lex->cursor - token->txt.data;
    return;

    error: {
        token->pos.last_line = lex->line;
        token->pos.length = lex->cursor - token->txt.data;
        lex_error(lex, token->pos, "Invalid integer literal.");
    }
}

static Void build_token (Lexer *lex) {
    eat_whitespace(lex);

    U64 idx               = (lex->ring_cursor + lex->ring_count++) & (MAX_TOKEN_LOOKAHEAD - 1);
    Token *token          = &lex->ring[idx];
    token->txt.data       = lex->cursor;
    token->txt.count      = 1;
    token->tag            = cast(TokenTag, eat_char(lex));
    token->pos.offset     = token->txt.data - lex->file->content.data;
    token->pos.first_line = lex->line;

    #define MOD(TAG) ({\
        eat_char(lex);\
        token->txt.count++;\
        token->tag = TAG;\
    })

    switch (token->tag) {
    case 0:    token->txt.count = 0; break;
    case '\'': build_char_token(lex, token); break;
    case '|':  if (peek_char(lex) == '|') { MOD(TOKEN_OR); } break;
    case '!':  if (peek_char(lex) == '=') { MOD(TOKEN_NOT_EQUAL); } break;
    case '+':  if (peek_char(lex) == '=') { MOD(TOKEN_PLUS_EQUAL); } break;
    case '&':  if (peek_char(lex) == '&') { MOD(TOKEN_AND); } break;
    case '/':  if (peek_char(lex) == '=') { MOD(TOKEN_SLASH_EQUAL); } break;
    case '<': if (peek_char(lex) == '=') { MOD(TOKEN_LESS_EQUAL); } break;
    case '>': if (peek_char(lex) == '=') { MOD(TOKEN_GREATER_EQUAL); } break;
    case '%':  if (peek_char(lex) == '=') { MOD(TOKEN_PERCENT_EQUAL); } break;
    case '*':  if (peek_char(lex) == '=') { MOD(TOKEN_ASTERISK_EQUAL); } break;
    case '"':
        if (peek_char(lex) == '\\' && peek_nth_char(lex, 1) == '*') {
            build_raw_string_token(lex, token);
        } else {
            build_string_token(lex, token);
        }
        break;
    case '=':
        if      (peek_char(lex) == '=') MOD(TOKEN_2EQUAL);
        else if (peek_char(lex) == '>') MOD(TOKEN_FAT_ARROW);
        break;
    case '-':
        if      (peek_char(lex) == '=') MOD(TOKEN_MINUS_EQUAL);
        else if (peek_char(lex) == '>') MOD(TOKEN_ARROW);
        break;
    default:
        if (lex_is_dec_digit(token->tag)) {
            switch (peek_char(lex)) {
            case 'x': MOD(token->tag); build_int_token(lex, token, 16); break;
            case 'b': MOD(token->tag); build_int_token(lex, token, 2); break;
            default:  lex->cursor--;   build_int_token(lex, token, 10); break;
            }
        } else if (lex_is_alpha(token->tag)) {
            build_identifier_token(lex, token);
        }
        break;
    }

    token->pos.last_line = lex->line;
    token->pos.length = token->txt.count;
}

Lexer *lex_new (Interns *interns, Mem *mem) {
    assert_dbg(MAX_TOKEN_LOOKAHEAD > 1);
    assert_dbg(is_pow2(MAX_TOKEN_LOOKAHEAD));
    Lexer *lex   = mem_new(mem, Lexer);
    lex->mem     = mem;
    lex->interns = interns,
    lex->scratch = astr_new(mem);
    return lex;
}

Void lex_reset (Lexer *lex, AstFile *file, SrcPos *adjust) {
    lex->scratch.count       = 0;
    lex->file                = file;
    lex->line                = adjust ? adjust->first_line : 1;
    lex->prev_pos.first_line = lex->line;
    lex->prev_pos.last_line  = lex->line;
    lex->ring_count          = 0;
    lex->ring_cursor         = 0;

    if (adjust) {
        assert_dbg(adjust->offset < file->content.count);
        assert_dbg(adjust->length <= (file->content.count - adjust->offset));
        lex->cursor = file->content.data + adjust->offset;
        lex->eof    = lex->cursor + adjust->length;
    } else {
        lex->cursor = file->content.data;
        lex->eof    = file->content.data + file->content.count;
    }
}

Token *lex_peek_nth (Lexer *lex, U64 n) {
    assert_dbg(n > 0 && n <= MAX_TOKEN_LOOKAHEAD);
    while (lex->ring_count < n) build_token(lex);
    U64 idx = (lex->ring_cursor + n - 1) & (MAX_TOKEN_LOOKAHEAD - 1);
    return &lex->ring[idx];
}

Token *lex_peek (Lexer *lex) {
    return lex_peek_nth(lex, 1);
}

Token *lex_peek_this (Lexer *lex, TokenTag tag) {
    Token *token = lex_peek_nth(lex, 1);
    if (token->tag != tag) lex_error(lex, token->pos, "Expected '" TERM_CYAN("%s")"'.", lex_tag_to_str[tag]);
    return token;
}

Token *lex_try_peek (Lexer *lex, TokenTag tag) {
    Token *token = lex_peek(lex);
    return (token->tag == tag) ? token : 0;
}

Token *lex_try_peek_nth (Lexer *lex, U64 nth, TokenTag tag) {
    Token *token = lex_peek_nth(lex, nth);
    return (token->tag == tag) ? token : 0;
}

Token *lex_eat (Lexer *lex) {
    Token *token     = lex_peek(lex);
    lex->ring_count -= 1;
    lex->ring_cursor = (lex->ring_cursor + 1) & (MAX_TOKEN_LOOKAHEAD - 1);
    lex->prev_pos    = token->pos;
    return token;
}

Token *lex_try_eat (Lexer *lex, TokenTag tag) {
    return (lex_peek(lex)->tag == tag) ? lex_eat(lex) : 0;
}

Token *lex_eat_this (Lexer *lex, TokenTag tag) {
    Token *token = lex_eat(lex);
    if (token->tag != tag) lex_error(lex, token->pos, "Expected '" TERM_CYAN("%s")"'.", lex_tag_to_str[tag]);
    return token;
}

SrcPos lex_get_prev_pos (Lexer *lex) {
    return lex->prev_pos;
}
