/**
 * 
*/
#include <stdio.h>

#include "io/print.h"
#include "parse/token.h"
#include "parse/lexer.h"
#include "parse/parser.h"

const char *usage = "Usage: moxi filename\n";

int main(int argc, char *argv[])
{
    if (argc != 2) {
        fprintf(stderr, "%s", usage);
        return 1;
    }

    char *filename = argv[1];
    int status;

    parser_t parser;
    status = init_parser(&parser, filename);

    if (status) {
        fprintf(stderr, "error: failed to open file %s\n", filename);
        return status;
    }

    token_type_t last_token = TOK_ERROR;
    while (!status && last_token != TOK_EOF) {
        status = parse_moxi(&parser);
        last_token = parser.lex.tok_type;
    }
    
    delete_parser(&parser);
    
    return status;

    // fprintf(stdout, "starting up\n");

    // lexer_t lex;
    // init_lexer(&lex, filename);

    // token_type_t token_type;

    // fprintf(stdout, "initialized lexer\n");

    // int status = 0;
    // do {
    //     token_type = lexer_next_token(&lex);
    //     print_debug(MOD_LEX, 0, "%-13s \"%s\"", token_type_str[token_type], lex.buffer.data);

    //     if (token_type >= TOK_ERROR) {
    //         status = 1;
    //     }
    // } while (token_type != TOK_EOF);

    // return status;
}