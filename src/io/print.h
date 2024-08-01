/**
 * 
*/
#ifndef __PRINT_H__
#define __PRINT_H__

#include <stdint.h>

#ifndef EXECUTABLE_NAME 
#define EXECUTABLE_NAME ""
#endif

typedef enum module_code {
    MOD_LEX,
    MOD_PARSE,
    MOD_TYPE_CHECK,
} module_code_t;

#define NUM_MODULES (MOD_TYPE_CHECK+1)

extern const char *module_code_str[NUM_MODULES];

void print_error_with_loc(
    const char *filename,
    module_code_t code, 
    uint64_t lineno, 
    uint64_t col, 
    const char *format, 
    ...
);
void print_error(module_code_t code, const char *format, ...);


#endif