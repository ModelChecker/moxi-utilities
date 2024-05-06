#include <stdlib.h>
#include <stdbool.h>

#include "io/print.h"
#include "parse/parser.h"



/**
 * 
*/
void init_parser(parser_t *parser, const char *filename)
{
    init_lexer(&parser->lex, filename);
    init_parse_error_stack(&parser->error_stack);
    init_symbol_table(&parser->symbol_table, 0);
}


/**
 * 
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
    symbol_table = &parser->symbol_table;

    token_type = lexer_next_token(lex);

    if (token_type != MOXI_TOK_SYMBOL) {
        push_parse_error(&parser->error_stack, PARSE_ERROR_EXPECTED_SYMBOL, 
            lex->tok_lineno, lex->tok_col, "expected symbol");
    } else if(symbol_table_find(symbol_table, buffer->data) >= 0) {
        push_parse_error(&parser->error_stack, PARSE_ERROR_SYMBOL_ALREADY_IN_USE, 
            lex->tok_lineno, lex->tok_col, "symbol in use");
    } 

    return buffer->data;
}


/**
 * 
 * `<symbol>`
 * `(_ <symbol> <symbol-or-int-list>)`
*/
void parse_identifier(parser_t *parser)
{

}


/**
 * 
 * `<sort-symbol>`
*/
void parse_sort(parser_t *parser)
{
    lexer_t *lex;
    string_buffer_t *buffer;
    parse_error_stack_t *error_stack;
    symbol_table_t *symbol_table;
    token_type_t token_type;

    lex = &parser->lex;
    buffer = &parser->lex.buffer;
    error_stack = &parser->error_stack;
    symbol_table = &parser->symbol_table;

    token_type = lexer_next_token(lex);

}


/**
 * 
 * `(<fresh-symbol> <sort-symbol>)`
*/
void parse_sorted_var(parser_t *parser)
{
    lexer_t *lex;
    string_buffer_t *buffer;
    parse_error_stack_t *error_stack;
    symbol_table_t *symbol_table;
    token_type_t token_type;

    lex = &parser->lex;
    buffer = &parser->lex.buffer;
    error_stack = &parser->error_stack;
    symbol_table = &parser->symbol_table;

    parse_sort(parser);

    if (error_stack->num_errors == 0) {
        symbol_table_add(symbol_table, buffer->data);
        // add to variable table?
    }
}


/**
 * 
 * `( <sorted-var>* )`
*/
void parse_sorted_var_list(parser_t *parser)
{
    lexer_t *lex;
    string_buffer_t *buffer;
    parse_error_stack_t *error_stack;
    symbol_table_t *symbol_table;
    token_type_t token_type;

    lex = &parser->lex;
    buffer = &parser->lex.buffer;
    error_stack = &parser->error_stack;
    symbol_table = &parser->symbol_table;

    token_type = lexer_next_token(lex);
    if (token_type != MOXI_TOK_LP) {
        push_parse_error(&parser->error_stack, PARSE_ERROR_EXPECTED_RP, 
            lex->tok_lineno, lex->tok_col, "expected '('");
    }

    token_type = lexer_next_token(lex);
    while(token_type == MOXI_TOK_LP) {  
        parse_sorted_var(parser);

        token_type = lexer_next_token(lex);
        if (token_type != MOXI_TOK_RP) {
            push_parse_error(&parser->error_stack, PARSE_ERROR_EXPECTED_RP, 
                lex->tok_lineno, lex->tok_col, "expected ')'");
        }
    }

    token_type = lexer_next_token(lex);
    if (token_type != MOXI_TOK_RP) {
        push_parse_error(&parser->error_stack, PARSE_ERROR_EXPECTED_RP, 
            lex->tok_lineno, lex->tok_col, "expected ')'");
    }
}


/**
 * 
*/
void parse_term(parser_t *parser)
{

}


/**
 * Parse a `define-fun` MoXI command. The current token should be `define-fun`.
 * 
 * `define-fun <fresh-symbol> <sorted-var-list> <sort-symbol> <term>`
*/
void parse_define_fun(parser_t *parser) 
{
    lexer_t *lex;
    string_buffer_t *buffer;
    parse_error_stack_t *error_stack;
    symbol_table_t *symbol_table;
    token_type_t token_type;

    lex = &parser->lex;
    buffer = &parser->lex.buffer;
    error_stack = &parser->error_stack;
    symbol_table = &parser->symbol_table;

    parse_fresh_symbol(parser);

    parse_sorted_var_list(parser);
    parse_sort(parser);
    parse_term(parser);

    if (error_stack->num_errors == 0) {
        symbol_table_add(symbol_table, buffer->data);
        // add to function table
    }
} 



int parse_moxi(parser_t *parser)
{
    lexer_t *lex;
    parse_error_stack_t *error_stack;
    token_type_t token_type;

    lex = &parser->lex;
    error_stack = &parser->error_stack;

    do {
        token_type = lexer_next_token(lex);
        if (token_type != MOXI_TOK_LP) {
            push_parse_error(&parser->error_stack, PARSE_ERROR_EXPECTED_RP, 
                lex->tok_lineno, lex->tok_col, "expected '('");
        }

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

        token_type = lexer_next_token(lex);
        if (token_type != MOXI_TOK_RP) {
            push_parse_error(&parser->error_stack, PARSE_ERROR_EXPECTED_RP, 
                lex->tok_lineno, lex->tok_col, "expected ')'");
        }

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

