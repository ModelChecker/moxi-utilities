/**
 * 
*/
#ifndef __PARSER_H__
#define __PARSER_H__

#include "parse/token.h"
#include "parse/parse_error.h"
#include "parse/lexer.h"


typedef struct symbol_table {

} symbol_table_t;



typedef struct parser {
    lexer_t lex;
    parse_error_t *error_stack;
} parser_t;


void init_parser(parser_t *parser, const char *filename);
void parse_moxi(parser_t *parser);


#endif