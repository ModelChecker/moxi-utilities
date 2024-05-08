#include <stdlib.h>
#include <stdbool.h>
#include <assert.h>

#include "io/print.h"
#include "parse/parser.h"



/**
 * 
*/
void init_parser(parser_t *parser, const char *filename)
{
    init_lexer(&parser->lex, filename);
    init_parse_error_stack(&parser->error_stack);

    parser->num_open_parens = 0;
    parser->depth = 0;
}


/**
 * 
*/
void delete_parser(parser_t *parser)
{
    delete_lexer(&parser->lex);
    delete_parse_error_stack(&parser->error_stack);
}


/**
 * Returns the contents of the next token's string buffer if the next token is both a symbol and is
 * not present in the symbol table. Otherwise returns NULL.
*/
char *parse_fresh_symbol(parser_t *parser)
{
    lexer_t *lex;
    string_buffer_t *buffer;
    parse_error_stack_t *error_stack;
    symbol_table_t *symbol_table;
    token_type_t token_type;

    lex = &parser->lex;
    buffer = &parser->lex.buffer;
    error_stack = &parser->error_stack;

    token_type = lexer_next_token(lex);

    if (token_type != MOXI_TOK_SYMBOL) {
        push_parse_error(&parser->error_stack, PARSE_ERROR_EXPECTED_SYMBOL, 
            lex->tok_lineno, lex->tok_col, "expected symbol");
        return NULL;
    } else if(symbol_table_find(symbol_table, buffer->data) >= 0) {
        push_parse_error(&parser->error_stack, PARSE_ERROR_SYMBOL_ALREADY_IN_USE, 
            lex->tok_lineno, lex->tok_col, "symbol already in use");
        return NULL;
    } 

    return buffer->data;
}


/**
 * 
*/
token_type_t parse_left_paren(parser_t *parser)
{
    lexer_t *lex;
    parse_error_stack_t *error_stack;
    token_type_t token_type;

    lex = &parser->lex;
    error_stack = &parser->error_stack;

    token_type = lexer_next_token(lex);

    if (token_type != MOXI_TOK_LP) {
        push_parse_error(error_stack, PARSE_ERROR_EXPECTED_RP, 
            lex->tok_lineno, lex->tok_col, "expected '('");
    }

    return token_type;
}


/**
 * 
*/
token_type_t parse_right_paren(parser_t *parser)
{
    lexer_t *lex;
    parse_error_stack_t *error_stack;
    token_type_t token_type;

    lex = &parser->lex;
    error_stack = &parser->error_stack;

    token_type = lexer_next_token(lex);

    if (token_type != MOXI_TOK_RP) {
        push_parse_error(error_stack, PARSE_ERROR_EXPECTED_RP, 
            lex->tok_lineno, lex->tok_col, "expected ')'");
    }

    return token_type;
}


/**
 * 
 * `<symbol>`
 * `(_ <symbol> <symbol-or-int-list>)`
*/
char *parse_identifier(parser_t *parser)
{

}


/**
 * 
 * `<sort-symbol>`
*/
char *parse_sort(parser_t *parser)
{
    lexer_t *lex;
    parse_error_stack_t *error_stack;
    char *sort_symbol;

    lex = &parser->lex;
    error_stack = &parser->error_stack;

    sort_symbol = parse_identifier(parser);

    if(symbol_table_find(symbol_table, sort_symbol) < 0) {
        push_parse_error(&parser->error_stack, PARSE_ERROR_SYMBOL_NOT_SORT, 
            lex->tok_lineno, lex->tok_col, "expected a sort symbol");
        return NULL;
    } 

    return sort_symbol;
}


/**
 * 
 * `<var-symbol> <sort-symbol>`
*/
void parse_sorted_var(parser_t *parser)
{
    string_buffer_t *buffer;
    parse_error_stack_t *error_stack;
    symbol_table_t *symbol_table;
    char *var_symbol;
    char *sort_symbol;

    buffer = &parser->lex.buffer;
    error_stack = &parser->error_stack;

    var_symbol = parse_fresh_symbol(parser);
    sort_symbol = parse_sort(parser);

    if (error_stack->num_errors == 0) {
        assert(var_symbol != NULL);
        assert(sort_symbol != NULL);

        symbol_table_add(symbol_table, var_symbol);
        // add to variable table
    }
}


/**
 * 
 * `( <sorted-var>* )`
*/
string_pair_list_t *parse_sorted_var_list(parser_t *parser)
{
    lexer_t *lex;
    token_type_t token_type;

    lex = &parser->lex;

    token_type = parse_left_paren(parser);
    token_type = lexer_next_token(lex);

    while(token_type == MOXI_TOK_LP) {  
        parse_sorted_var(parser);
        parse_right_paren(parser);
        token_type = lexer_next_token(lex);
    }

    parse_right_paren(parser);
}


/**
 * 
*/
term_t *parse_term(parser_t *parser)
{

}


/**
 * Parse a `define-fun` MoXI command. The current token should be `define-fun`. We associate a new
 * context starting at <term> and close it once we're done.
 *
 * `define-fun <fresh-symbol> <sorted-var-list> <sort-symbol> <term>`
*/
void parse_define_fun(parser_t *parser) 
{
    lexer_t *lex;
    string_buffer_t *buffer;
    parse_error_stack_t *error_stack;
    context_t *context;
    token_type_t token_type;

    char *function_symbol;
    string_pair_list_t *rank;
    term_t *term;

    lex = &parser->lex;
    buffer = &parser->lex.buffer;
    error_stack = &parser->error_stack;
    context = &parser->context;

    function_symbol = parse_fresh_symbol(parser);
    rank = parse_sorted_var_list(parser);
    parse_sort(parser);

    // open context


    term = parse_term(parser);

    if (error_stack->num_errors == 0) {
        context_add_function_symbol(context, buffer->data);
        // add to function table
    }
} 


/**
 * Parse a `define-sort` MoXI command. The current token should be `define-sort`. 
 * 
 * FIXME: Consider adding some "alias" table, since that's what these really are -- but how does
 * this relate to defined functions?
 * 
 * Examples: 
 * - `(define-sort BV8 () (_ BitVec 8))`
 * - `(define-sort BV8IdxArray (ElemSort) (Array BV8 ElemSort))`
 *
 * `define-sort <fresh-symbol> <sort-symbol-list> <sort-symbol>`
*/
void parse_define_sort(parser_t *parser) 
{
    
} 



int parse_moxi(parser_t *parser)
{
    lexer_t *lex;
    parse_error_stack_t *error_stack;
    token_type_t token_type;

    lex = &parser->lex;
    error_stack = &parser->error_stack;

    do {
        parse_left_paren(parser);

        token_type = lexer_next_token(lex);

        switch (token_type)
        {
        case MOXI_TOK_RW_DEFINE_SYS:
        case MOXI_TOK_RW_CHECK_SYS:
        case MOXI_TOK_RW_DECLARE_SORT:
        case MOXI_TOK_RW_DECLARE_ENUM_SORT:
        case MOXI_TOK_RW_DECLARE_CONST:
        case MOXI_TOK_RW_DECLARE_FUN:
        case MOXI_TOK_RW_DEFINE_SORT:
        case MOXI_TOK_RW_DEFINE_CONST:
        case MOXI_TOK_RW_DEFINE_FUN:
            parse_define_fun(parser);
            break;

        case MOXI_TOK_RW_EXIT:
        case MOXI_TOK_RW_SET_LOGIC:
        case MOXI_TOK_RW_ECHO:
        default:
            break;
        }

        parse_right_paren(parser);

    } while(token_type != MOXI_TOK_EOF);

    if (error_stack->num_errors == 0) {
        return 0;
    }

    parse_error_t error;
    while (error_stack->num_errors > 0) {
        error = pop_parse_error(error_stack);
        print_error(MOD_PARSE, "%d:%d: %s", error.lineno, error.col, error.msg);
    }

    return -1;
}

