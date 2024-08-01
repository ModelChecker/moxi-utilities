#include <stdio.h>
#include <stdarg.h>
#include <stdint.h>

#include "print.h"


void print_error_with_loc(
    const char *filename,
    uint64_t lineno, 
    uint64_t col, 
    const char *format, 
    ...
)
{
    va_list args;
    va_start(args, format);

    fprintf(stderr, "%s:%ld:%ld: error: ", filename, lineno, col);
    vfprintf(stderr, format, args);
    fprintf(stderr, "\n");
}


void print_error(const char *format, ...)
{
    va_list args;
    va_start(args, format);

    fprintf(stderr, "error: ");
    vfprintf(stderr, format, args);
    fprintf(stderr, "\n");
}

