/**
 * 
*/
#ifndef __LEXER_H__
#define __LEXER_H__

#include <stdint.h>

#include "util/char_buffer.h"
#include "io/file_reader.h"
#include "parse/token.h"

// Starting size of lexer string buffer
#define BUFFER_MIN 1024


typedef struct lexer {
    file_reader_t reader;

    // Position of current token's first char
    uint64_t tok_pos;
    loc_t loc;

    token_type_t tok_type;
    char_buffer_t buffer;
} lexer_t;


void init_lexer(lexer_t *lex);
int init_file_lexer(lexer_t *lex, const char *filename);
void delete_lexer(lexer_t *lex);
void lexer_next_token(lexer_t *lex);


#endif