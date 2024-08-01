/**
 * 
*/
#ifndef __PRINT_H__
#define __PRINT_H__

#include <stdint.h>

#ifndef EXECUTABLE_NAME 
#define EXECUTABLE_NAME ""
#endif

void print_error_with_loc(
    const char *filename,
    uint64_t lineno, 
    uint64_t col, 
    const char *format, 
    ...
);
void print_error(const char *format, ...);


#endif