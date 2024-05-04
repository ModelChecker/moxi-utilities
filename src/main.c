/**
 * 
*/
#include <stdio.h>

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

    do {
        token_type = lexer_next_token(&lex);

        if (token_type == MOXI_TOK_ERROR) {
            fprintf(stderr, "error\n");
            return 1;
        }

        fprintf(stdout, "%s\n", lex.buffer.data);

    } while (token_type != MOXI_TOK_EOF);

    return 0;
}