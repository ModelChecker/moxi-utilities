#ifndef __PARSE_ERROR_H__
#define __PARSE_ERROR_H__

#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>

#define PARSE_ERROR_STACK_MIN 16

typedef enum error_code {
    PARSE_ERROR_EXPECTED_LP,
    PARSE_ERROR_EXPECTED_RP,
    PARSE_ERROR_SYMBOL_NOT_SORT,
    PARSE_ERROR_SYMBOL_ALREADY_IN_USE,
    PARSE_ERROR_EXPECTED_SYMBOL,
    PARSE_ERROR_NONE
} error_code_t;


typedef struct error {
    error_code_t code;
    uint64_t lineno;
    uint64_t col;
    char *msg;
} error_t;

#define EMPTY_PARSE_ERROR (error_t) { PARSE_ERROR_NONE, 0, 0, "" }


typedef struct error_stack {
    size_t size;
    size_t num_errors;
    error_t *data;
} error_stack_t;


void init_error_stack(error_stack_t *stack);
void delete_error_stack(error_stack_t *stack);
void extend_error_stack(error_stack_t *stack, size_t size);
void push_error(error_stack_t *stack, error_code_t code, 
    uint64_t lineno, uint64_t col, const char *format, ...);
error_t pop_error(error_stack_t *stack);
static inline bool error_stack_is_empty(error_stack_t *stack) { return stack->num_errors == 0; }; 

#endif