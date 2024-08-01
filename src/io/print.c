#include <stdio.h>
#include <stdarg.h>
#include <stdint.h>

#include "print.h"

const char *module_code_str[NUM_MODULES] = {
    "lex",
    "parse",
    "type-check"
};


void print_error_with_loc(
    const char *filename,
    module_code_t code, 
    uint64_t lineno, 
    uint64_t col, 
    const char *format, 
    ...
)
{
    va_list args;
    va_start(args, format);

    fprintf(stderr, "%s: %s error: %s:%ld:%ld: ", EXECUTABLE_NAME, module_code_str[code], filename, lineno, col);
    vfprintf(stderr, format, args);
    fprintf(stderr, "\n");
}


void print_error(module_code_t code, const char *format, ...)
{
    va_list args;
    va_start(args, format);

    fprintf(stderr, "%s: %s error:", EXECUTABLE_NAME, module_code_str[code]);
    vfprintf(stderr, format, args);
    fprintf(stderr, "\n");
}

