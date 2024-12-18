/**
 * 
*/
#ifndef __PARSER_H__
#define __PARSER_H__

#include "util/int_stack.h"
#include "parse/token.h"
#include "parse/lexer.h"
#include "parse/pstack.h"
#include "moxi/context.h"

/**
 * Each parser uses a lexer to iteratively parse an input file. 
*/
typedef struct parser {
    const char *filename;
    lexer_t lex;
    
    pstack_t pstack;
    int_stack_t sstack;
    moxi_context_t ctx;
} parser_t;


int init_parser(parser_t *parser, const char *filename);
void delete_parser(parser_t *parser);

/**
 * Parse a single command from the input file.
 * 
 * Returns:
 * - -1 if an error occurs during parsing
 * - 1 if the last token is EOF
 * - 0 otherwise 
 */
int parse_moxi(parser_t *parser);


#endif