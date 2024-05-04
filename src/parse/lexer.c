/**
 * 
*/
#include <stdbool.h>
#include <string.h>
#include <ctype.h>

#include "parse/hash_reserved.h"
#include "parse/hash_symbol.h"
#include "parse/hash_keyword.h"
#include "parse/token.h"
#include "parse/lexer.h"


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
void init_lexer(lexer_t *lex, const char *filename)
{
    file_reader_t *reader = &lex->reader;
    init_file_reader(reader, filename);

    lex->tok_pos = 0;
    lex->tok_col = 0;
    lex->tok_lineno = 0;

    lex->tok_type = MOXI_TOK_ERROR;
    
    string_buffer_t *buffer = &lex->buffer;
    init_string_buffer(buffer, BUFFER_MIN);
}


/**
 * 
*/
void delete_lexer(lexer_t *lex)
{   
    close_file_reader(&lex->reader);
    delete_string_buffer(&lex->buffer);
}


/**
 * 
*/
token_type_t read_constant(lexer_t *lex)
{

}


/**
 * 
*/
token_type_t read_string(lexer_t *lex)
{

}


/**
 * 
*/
token_type_t read_quoted_symbol(lexer_t *lex)
{

}


/**
 * Returns token corresponding to symbol in `lex`'s reader. When called, the first char of the
 * symbol is in `lex`'s buffer and is the current char of `lex`'s reader.
*/
token_type_t read_symbol(lexer_t *lex)
{
    file_reader_t *reader;
    string_buffer_t *buffer;
    token_t *tok;
    token_type_t tok_type;
    char ch;

    reader = &lex->reader;
    buffer = &lex->buffer;

    while(is_simple_char(ch)) {
        ch = file_reader_next_char(&lex->reader);
        string_buffer_append_char(buffer, ch);
    }

    tok = in_moxi_kw(buffer->data, buffer->idx);
    if (tok != NULL) {
        return tok->type;
    }

    tok = in_moxi_rw(buffer->data, buffer->idx);
    if (tok != NULL) {
        return tok->type;
    }

    return MOXI_TOK_SYMBOL;
}


/**
 * 
*/
token_type_t lexer_next_token(lexer_t *lex)
{
    int ch;
    file_reader_t *reader = &lex->reader;
    ch = file_reader_next_char(reader);

    string_buffer_t *buffer = &lex->buffer;
    string_buffer_reset(buffer);

    token_type_t tok_type = MOXI_TOK_ERROR;

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

    switch (ch) {
    case EOF:
        tok_type = MOXI_TOK_EOF;
        break;

    case '(':
        tok_type = MOXI_TOK_LP;
        file_reader_next_char(reader);
        break;

    case ')':
        tok_type = MOXI_TOK_RP;
        file_reader_next_char(reader);
        break;

    case '#':
        string_buffer_append_char(buffer, ch);
        tok_type = read_constant(lex);
        break;

    case '"':
        string_buffer_append_char(buffer, ch);
        tok_type = read_string(lex);
        break;

    case '|':
        string_buffer_append_char(buffer, ch);
        tok_type = read_quoted_symbol(lex);
        break;

    default:
        if (is_simple_char(ch)) {
            string_buffer_append_char(buffer, ch);
            tok_type = read_symbol(lex);
            break;
        } 
        
        tok_type = MOXI_TOK_ERROR;
    }

    return tok_type;
}
