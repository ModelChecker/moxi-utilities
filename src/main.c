/**
 * 
*/
#include <stdio.h>
#include <yices.h>

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
        PRINT_ERROR("failed to open file %s", filename);
        return status;
    }

    yices_init();

    while (status == 0) {
        status = parse_moxi(&parser);
    }
    
    delete_parser(&parser);
    yices_exit();
    
    return status < 0;
}
