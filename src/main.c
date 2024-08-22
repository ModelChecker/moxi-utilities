/**
 * 
*/
#include <stdio.h>

#include "io/print.h"
#include "parse/token.h"
#include "parse/lexer.h"
#include "parse/parse.h"

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
        print_error("failed to open file %s", filename);
        return status;
    }

    while (status == 0) {
        status = parse_moxi(&parser);
    }
    
    delete_parser(&parser);
    
    return status < 0;

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