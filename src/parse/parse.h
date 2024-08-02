/**
 * 
*/
#ifndef __PARSER_H__
#define __PARSER_H__

#include "util/string_hash_set.h"
#include "util/symbol_table.h"
#include "util/int_stack.h"

#include "parse/token.h"
#include "parse/lexer.h"


/**
 * Each parser uses a lexer to iteratively parse an input file. 
*/
typedef struct parser {
    const char *filename;
    lexer_t lex;
    
    // parse_stack_t parse_stack;
    int_stack_t state_stack;
} parser_t;


int init_parser(parser_t *parser, const char *filename);
void delete_parser(parser_t *parser);
int parse_moxi(parser_t *parser);


#endif