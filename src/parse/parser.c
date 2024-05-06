#include <stdlib.h>

#include "parse/parser.h"



/**
 * 
*/
void init_parser(parser_t *parser, const char *filename)
{
    init_lexer(&parser->lex, filename);
    init_parse_error_stack(&parser->error_stack);
}


/**
 * 
*/
void parse_term(parser_t *parser)
{

}




void parse_define_fun(parser_t *parser) 
{
    
} 



void parse_moxi(parser_t *parser)
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
}

