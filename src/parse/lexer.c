/**
 * 
*/
#include <stdbool.h>
#include <string.h>
#include <ctype.h>
#include <assert.h>

#include "parse/token.h"
#include "parse/lexer.h"
#include "parse/hash_token.h"

/**
 * Returns `true` if `c` is a tab (`\t`), space (` `), line break (`\n`), or carriage return (`\r`).
*/
bool is_whitespace(char c) 
{
    switch (c)
    {
    case '\t':
    case ' ':
    case '\n':
    case '\r':
        return true;
    
    default:
        return false;
    }
}


/**
 * Returns `true` if `c` is a valid symbol character in the SMT-LIB2 lexicon.
*/
bool is_simple_char(char c)
{
    if (isalnum(c)) {
        return true;
    }
    
    switch (c) {
    case '~':
    case '!':
    case '@':
    case '$':
    case '%':
    case '^':
    case '&':
    case '*':
    case '_':
    case '-':
    case '+':
    case '=':
    case '<':
    case '>':
    case '.':
    case '?':
    case '/':
        return true;    
    default:
        return false;
    }
}


/**
 * 
*/
void init_lexer(lexer_t *lex)
{
    lex->tok_pos = 0;
    lex->loc = (loc_t) {0, 0};

    lex->tok_type = TOK_ERROR;
    
    char_buffer_t *buffer = &lex->buffer;
    init_char_buffer(buffer, BUFFER_MIN);
}


/**
 * Initialize `lex` to use `filename` as input. 
 * 
 * Returns 0 on success, the result of `init_file_reader` otherwise.
*/
int init_file_lexer(lexer_t *lex, const char *filename)
{
    int status;
    file_reader_t *reader = &lex->reader;
    status = init_file_reader(reader, filename);

    if (status) {
        return status;
    }

    init_lexer(lex);
    return 0;
}


/**
 * 
*/
void delete_lexer(lexer_t *lex)
{   
    close_file_reader(&lex->reader);
    delete_char_buffer(&lex->buffer);
}


/**
 * 
*/
token_type_t read_decimal(lexer_t *lex)
{
    char_buffer_t *buffer;
    file_reader_t *reader;
    char ch;

    buffer = &lex->buffer;
    reader = &lex->reader;
    ch = reader->cur;

    assert(ch == '.');

    char_buffer_append_char(buffer, ch);
    ch = file_reader_next_char(&lex->reader);

    // Cannot allow the token `123.`
    if (!isdigit(ch)) {
        return TOK_INVALID_NUMERAL_ZERO;
    }

    do {
        char_buffer_append_char(buffer, ch);
        ch = file_reader_next_char(&lex->reader);
    } while(isdigit(ch));

    return TOK_DECIMAL;
}


/**
 * Returns token type corresponding to the numeral in `lex`'s reader. 
 * 
 * When called, the first char in `lex`'s buffer must be a digit.
*/
token_type_t read_numeral(lexer_t *lex)
{
    char_buffer_t *buffer;
    file_reader_t *reader;
    char ch;

    buffer = &lex->buffer;
    reader = &lex->reader;
    ch = reader->cur;

    assert(isdigit(ch));

    // Numerals that start with `0` must be either:
    //   - only `0` or 
    //   - `0.<numeral>`
    if (ch == '0') {
        char_buffer_append_char(buffer, ch);
        ch = file_reader_next_char(&lex->reader);

        // Any numeral that starts with `0` and followed by another digit is an error.
        // We consume all the digits for better error messaging.
        if (isdigit(ch)) {
            do {
                char_buffer_append_char(buffer, ch);
                ch = file_reader_next_char(&lex->reader);
            } while(isdigit(ch));

            return TOK_INVALID_NUMERAL_ZERO;
        }

        if (ch != '.') {
            return TOK_NUMERAL;
        }

        return read_decimal(lex);
    }

    do {
        char_buffer_append_char(buffer, ch);
        ch = file_reader_next_char(&lex->reader);
    } while(isdigit(ch));

    if (ch == '.') {
        return read_decimal(lex);
    }
    
    return TOK_NUMERAL;
}


/**
 * Returns token type corresponding to the constant symbol in `lex`'s reader. 
 * 
 * When called, the first char in `lex`'s buffer must be `#`.
*/
token_type_t read_constant(lexer_t *lex)
{
    char_buffer_t *buffer;
    file_reader_t *reader;
    char ch;

    buffer = &lex->buffer;
    reader = &lex->reader;
    ch = reader->cur; // must be `#`

    assert(ch == '#');

    char_buffer_append_char(buffer, ch);
    ch = file_reader_next_char(&lex->reader);

    switch (ch)
    {
    case 'b':
        char_buffer_append_char(buffer, ch);
        ch = file_reader_next_char(&lex->reader);

        while(ch == '0' || ch == '1') {
            char_buffer_append_char(buffer, ch);
            ch = file_reader_next_char(&lex->reader);
        }

        return TOK_BINARY;
    case 'x':
        char_buffer_append_char(buffer, ch);
        ch = file_reader_next_char(&lex->reader);

        while(isxdigit(ch)) {
            char_buffer_append_char(buffer, ch);
            ch = file_reader_next_char(&lex->reader);
        }

        return TOK_HEX;
    default:
        return TOK_INVALID_CONSTANT;
    }
}


/**
 * Returns `TOK_STRING` if `lex`'s reader currently has a valid string. 
 *
 * A valid string is a sequence of printable chars that are not `\` encased by `"`.
 * When called, the first char in `lex`'s buffer must be `"`.
 * 
 * FIXME: Cannot handle escaped `"` yet, escaped quotes are double (`""`)
*/
token_type_t read_string(lexer_t *lex)
{
    char_buffer_t *buffer;
    file_reader_t *reader;
    char ch;

    buffer = &lex->buffer;
    reader = &lex->reader;
    ch = reader->cur;

    assert(ch == '"');
    char_buffer_append_char(buffer, ch);
    ch = file_reader_next_char(&lex->reader);

keep_going:
    while(ch != '"' && isprint(ch) && ch != '\\') {
        char_buffer_append_char(buffer, ch);
        ch = file_reader_next_char(&lex->reader);
    }

    if (ch == '"') {
        // Then this is a valid symbol, consume `"`
        char_buffer_append_char(buffer, ch);
        ch = file_reader_next_char(&lex->reader);

        if (ch == '"') {
            // Then we have an escaped quote `""`
            char_buffer_append_char(buffer, ch);
            ch = file_reader_next_char(&lex->reader);
            goto keep_going;
        }

        return TOK_STRING;
    }

    // In error state, so consume until we find another `"` or EOF
    while(ch != '"' && ch != EOF) {
        char_buffer_append_char(buffer, ch);
        ch = file_reader_next_char(&lex->reader);
    }

    if (ch == EOF) {
        return TOK_INVALID_STRING_EOF;
    }

    file_reader_next_char(&lex->reader);
    return TOK_INVALID_STRING_CHAR;
}


/**
 * Returns `TOK_SYMBOL` if `lex`'s reader currently has a valid quoted symbol. 
 * 
 * A valid quoted symbol is a sequence of printable chars that are not `\` encased by `|`.
 * When called, the first char in `lex`'s buffer must be `|`.
*/
token_type_t read_quoted_symbol(lexer_t *lex)
{
    char_buffer_t *buffer;
    file_reader_t *reader;
    char ch;

    buffer = &lex->buffer;
    reader = &lex->reader;
    ch = reader->cur;

    assert(ch == '|');
    char_buffer_append_char(buffer, ch);
    ch = file_reader_next_char(&lex->reader);

    while(ch != '|' && isprint(ch) && ch != '\\') {
        char_buffer_append_char(buffer, ch);
        ch = file_reader_next_char(&lex->reader);
    }

    if (ch == '|') {
        // Then this is a valid symbol, consume `|`
        char_buffer_append_char(buffer, ch);
        ch = file_reader_next_char(&lex->reader);

        // Could also be primed symbol
        if (ch == '\'') {
            char_buffer_append_char(buffer, ch);
            file_reader_next_char(&lex->reader);
        }

        return TOK_SYMBOL;
    }

    // In error state, so consume until we find another `|` or EOF
    while(ch != '|' && ch != EOF) {
        char_buffer_append_char(buffer, ch);
        ch = file_reader_next_char(&lex->reader);
    }

    if (ch == EOF) {
        return TOK_INVALID_QUOTED_SYMBOL_EOF;
    }

    file_reader_next_char(&lex->reader);
    return TOK_INVALID_QUOTED_SYMBOL_CHAR;
}


/**
 * Returns token corresponding to symbol in `lex`'s reader. 
 * 
 * When called, the first char of the symbol is in `lex`'s buffer and is the current char of `lex`'s
 * reader.
 * 
 * Symbols can be primed (ex: `x'`)
*/
token_type_t read_symbol(lexer_t *lex)
{
    char_buffer_t *buffer;
    file_reader_t *reader;
    const token_t *tok;
    char ch;

    buffer = &lex->buffer;
    reader = &lex->reader;
    ch = reader->cur;

    do {
        char_buffer_append_char(buffer, ch);
        ch = file_reader_next_char(&lex->reader);
    } while(is_simple_char(ch));

    if (buffer->data[0] == ':') {
        if (buffer->len == 1) {
            return TOK_INVALID_KEYWORD;
        }
        tok = find_moxi_tok(buffer->data, buffer->len);
        if (tok != NULL) {
            return tok->type;
        }
        return TOK_KW_UNKNOWN;
    }

    // Prime symbol (') allowed at the end of a non-zero length symbol
    if (ch == '\'') {
        char_buffer_append_char(buffer, ch);
        file_reader_next_char(&lex->reader);
    }

    tok = find_moxi_tok(buffer->data, buffer->len);
    if (tok != NULL) {
        return tok->type;
    } 

    return TOK_SYMBOL;
}


/**
 * Returns token corresponding to a keyword in `lex`'s reader. 
 *
 * When called, the first char of `lex`'s buffer should be `:` and is the current char of `lex`'s
 * reader.
*/
token_type_t read_keyword(lexer_t *lex)
{
    char_buffer_t *buffer;
    file_reader_t *reader;
    const token_t *tok;
    char ch;

    buffer = &lex->buffer;
    reader = &lex->reader;
    ch = reader->cur;

    assert(ch == ':');
    ch = file_reader_next_char(&lex->reader);

    do {
        char_buffer_append_char(buffer, ch);
        ch = file_reader_next_char(&lex->reader);
    } while(is_simple_char(ch));

    if (char_buffer_get_length(buffer) <= 1) {
        return TOK_INVALID_KEYWORD;
    }

    tok = find_moxi_tok(buffer->data, buffer->len);
    if (tok != NULL) {
        return tok->type;
    } 

    return TOK_INVALID_KEYWORD;
}


/**
 * 
*/
void lexer_next_token(lexer_t *lex)
{
    int ch;
    file_reader_t *reader = &lex->reader;
    ch = reader->cur;

    char_buffer_t *buffer = &lex->buffer;
    char_buffer_reset(buffer);

    token_type_t tok_type = TOK_ERROR;

    // skip whitespace: if next non-whitespace char is a ';' then skip until newline and repeat
    while(1) {
        while(is_whitespace(ch)) {
            ch = file_reader_next_char(reader);
        }

        if (ch != ';') break;
        
        do {
            ch = file_reader_next_char(reader);
        } while(ch != '\n' && ch != '\r' && ch != EOF);
    }

    lex->tok_pos = reader->pos;
    lex->loc = reader->loc;

    switch (ch) {
    case EOF:
        tok_type = TOK_EOF;
        break;
    case '(':
        tok_type = TOK_LP;
        file_reader_next_char(reader);
        break;
    case ')':
        tok_type = TOK_RP;
        file_reader_next_char(reader);
        break;
    case '#':
        tok_type = read_constant(lex);
        break;
    case '"':
        tok_type = read_string(lex);
        break;
    case '|':
        tok_type = read_quoted_symbol(lex);
        break;
    case '0':
    case '1':
    case '2':
    case '3':
    case '4':
    case '5':
    case '6':
    case '7':
    case '8':
    case '9':
        tok_type = read_numeral(lex);
        break;
    default:
        if (is_simple_char(ch) || ch == ':') {
            tok_type = read_symbol(lex);
            break;
        } 
        file_reader_next_char(reader);
        tok_type = TOK_INVALID_SYMBOL;
    }
    lex->tok_type = tok_type;
}
