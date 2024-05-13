/**
 * 
*/
#ifndef __LEXER_H__
#define __LEXER_H__

#include <stdint.h>

#include "util/string_buffer.h"
#include "io/file_reader.h"
#include "parse/token.h"


// Starting size of lexer string buffer
#define BUFFER_MIN 1024

typedef struct loc {
    uint32_t lineno;
    uint32_t col;
} loc_t;


typedef struct lexer {
    file_reader_t reader;
    uint64_t tok_pos;
    loc_t loc;
    token_type_t tok_type;
    string_buffer_t buffer;
} lexer_t;


void init_lexer(lexer_t *lex, const char *filename);
void delete_lexer(lexer_t *lex);
token_type_t lexer_next_token(lexer_t *lex);


#endif