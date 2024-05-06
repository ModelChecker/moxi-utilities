/**
 * 
*/
#ifndef __PARSER_H__
#define __PARSER_H__

#include "parse/token.h"
#include "parse/parse_error.h"
#include "parse/lexer.h"
#include "util/symbol_table.h"


typedef struct parser {
    lexer_t lex;
    parse_error_stack_t error_stack;
    symbol_table_t symbol_table;
} parser_t;


void init_parser(parser_t *parser, const char *filename);
int parse_moxi(parser_t *parser);


#endif