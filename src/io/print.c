#include <stdio.h>
#include <stdarg.h>

#include "print.h"

const char *module_code_str[MOD_PARSE+1] = {
    "LEX",
    "PARSE"
};

int debug_level = 0;

void set_debug_level(int level)
{
    debug_level = level;
}


void print_error(module_code_t code, int level, const char *format, ...)
{
    va_list args;
    va_start(args, format);

    if (level <= debug_level) {
        fprintf(stderr, "[ERR-%s] ", module_code_str[code]);
        vfprintf(stderr, format, args);
        fprintf(stderr, "\n");
    }
}


void print_debug(module_code_t code, int level, const char *format, ...)
{
    va_list args;
    va_start(args, format);

    if (level <= debug_level) {
        fprintf(stdout, "[DBG-%s] ", module_code_str[code]);
        vfprintf(stdout, format, args);
        fprintf(stdout, "\n");
    }
}

