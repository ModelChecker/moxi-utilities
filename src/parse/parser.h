/**
 * 
*/
#ifndef __PARSER_H__
#define __PARSER_H__

#include "parse/token.h"
#include "parse/parse_error.h"
#include "parse/lexer.h"
#include "util/string_set.h"
#include "util/symbol_table.h"

/**
 * Each parser uses a lexer to iteratively parse an input file. 
 *
 * The error_stack is used to store errors: if it's non-empty then we know that some error occurred
 * since we last emptied the stack. In practice we empty the stack after parsing a single command.
 *
 * The symbol table stores all the 
 *
 * ctx_symbols acts as a stack to track context-sensitive symbols. For example, a sorted variable
 * that's an argument to a define-fun command or a quantified variable. 
*/

typedef struct parser {
    lexer_t lex;
    parse_error_stack_t error_stack;
    symbol_table_t symbol_table;
    symbol_table_t sort_table;
    symbol_table_t function_table;

    uint32_t num_open_parens;

    // Context-sensitive symbols
    string_set_t *ctx_symbols;
    uint32_t depth;
} parser_t;


void init_parser(parser_t *parser, const char *filename);
void delete_parser(parser_t *parser);
int parse_moxi(parser_t *parser);


#endif