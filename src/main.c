/**
 * 
*/
#include <stdio.h>

#include "io/print.h"
#include "parse/token.h"
#include "parse/lexer.h"

const char *usage = "Usage: moxi filename\n";

int main(int argc, char *argv[])
{
    if (argc != 2) {
        fprintf(stderr, usage);
        return 1;
    }

    char *filename = argv[1];

    fprintf(stdout, "starting up\n");

    lexer_t lex;
    init_lexer(&lex, filename);

    token_type_t token_type;

    fprintf(stdout, "initialized lexer\n");

    int status = 0;
    do {
        token_type = lexer_next_token(&lex);
        print_debug(MOD_LEX, 0, "%-13s \"%s\"", token_type_str[token_type], lex.buffer.data);

        if (token_type >= MOXI_TOK_ERROR) {
            status = 1;
        }
    } while (token_type != MOXI_TOK_EOF);

    return status;
}