#ifndef __PARSE_ERROR_H__
#define __PARSE_ERROR_H__

#include <stdint.h>
#include <stddef.h>

#define PARSE_ERROR_STACK_MIN 16

typedef enum parse_error_code {
    PARSE_ERROR_EXPECTED_LP,
    PARSE_ERROR_EXPECTED_RP,
    PARSE_ERROR_SYMBOL_ALREADY_IN_USE,
    PARSE_ERROR_EXPECTED_SYMBOL,
    PARSE_ERROR_NONE
} parse_error_code_t;


typedef struct parse_error {
    parse_error_code_t code;
    uint64_t lineno;
    uint64_t col;
    char *msg;
} parse_error_t;

#define EMPTY_PARSE_ERROR (parse_error_t) { PARSE_ERROR_NONE, 0, 0, "" }


typedef struct parse_error_stack {
    size_t size;
    size_t num_errors;
    parse_error_t *data;
} parse_error_stack_t;


void init_parse_error_stack(parse_error_stack_t *stack);
void delete_parse_error_stack(parse_error_stack_t *stack);
void extend_parse_error_stack(parse_error_stack_t *stack, size_t size);
void push_parse_error(parse_error_stack_t *stack, parse_error_code_t code, 
    uint64_t lineno, uint64_t col, const char *format, ...);
parse_error_t pop_parse_error(parse_error_stack_t *stack);

#endif