/**
 * 
*/
#ifndef __PARSER_H__
#define __PARSER_H__

#include "util/string_hash_set.h"
#include "util/symbol_table.h"
#include "util/int_stack.h"

#include "parse/token.h"
#include "parse/parse_error.h"
// #include "parse/term_stack.h"
#include "parse/lexer.h"


/**
 * Each parser uses a lexer to iteratively parse an input file. 
 *
 * `error_stack` is used to store errors: if it's non-empty then we know that some error occurred
 * since we last emptied the stack. In practice we empty the stack after parsing each command.
 *
 * `context` 
 *
 * `ctx_symbols` acts as a stack to track context-sensitive symbols. For example, a sorted variable
 * that's an argument to a define-fun command or a quantified variable. 
*/
typedef struct parser {
    lexer_t lex;
    
    // context_t context;
    // moxi_command_t command;

    // term_stack_t tstack;
    int_stack_t pstack;
    error_stack_t error_stack;

    // Context-sensitive symbols
    string_set_t ctx_symbols;
    uint32_t depth;
    char *top_context_symbol;

} parser_t;


void init_parser(parser_t *parser, const char *filename);
void delete_parser(parser_t *parser);
int parse_moxi(parser_t *parser);


#endif