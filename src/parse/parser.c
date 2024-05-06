#include <stdlib.h>

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
void parse_term(parser_t *parser)
{

}



/**
 * Parse a `define`fun` MoXI command. The current token should be `define-fun`.
 * 
 * `(define-fun <symbol> <sort-symbol> <sorted-var-list> <term>)`
*/
void parse_define_fun(parser_t *parser) 
{
    lexer_t *lex;
    string_buffer_t *buffer;
    symbol_table_t *symbol_table;
    token_type_t token_type;

    lex = &parser->lex;
    buffer = &parser->lex.buffer;
    symbol_table = &parser->symbol_table;

    token_type = lexer_next_token(lex);

    switch (token_type)
    {
    case MOXI_SYM:
        if(symbol_table_find(symbol_table, buffer->data) >= 0) {
            push_parse_error(&parser->error_stack, PARSE_ERROR_SYMBOL_ALREADY_IN_USE, 
                lex->tok_lineno, lex->tok_col, "");
            break;
        }
        symbol_table_add(symbol_table, buffer->data);
        
        break;
    
    default:
        push_parse_error(&parser->error_stack, PARSE_ERROR_EXPECTED_SYMBOL, 
            lex->tok_lineno, lex->tok_col, "");
        break;
    }

    parse_sort(parser);
    parse_sorted_var_list(parser);
    parse_term(parser);
} 



int parse_moxi(parser_t *parser)
{
    lexer_t *lex = &parser->lex;
    token_type_t token_type;

    do {
        token_type = lexer_next_token(lex);

        if (token_type != MOXI_TOK_LP) {
            // error
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
    } while(token_type != MOXI_TOK_EOF);

    if (parser->error_stack.idx > 0) {
        // report the errors and return -1
        return -1;
    }

    return 0;
}

