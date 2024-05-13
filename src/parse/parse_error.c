#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>

#include "parse/parse_error.h"


void init_error_stack(error_stack_t *stack)
{
    stack->size = PARSE_ERROR_STACK_MIN;
    stack->num_errors = 0;
    stack->data = malloc(sizeof(error_t) * PARSE_ERROR_STACK_MIN);
}


void delete_error_stack(error_stack_t *stack)
{
    free(stack->data);
}


void extend_error_stack(error_stack_t *stack, size_t size)
{
    size_t new_size = stack->size + size;
    stack->size = new_size;
    stack->data = realloc(stack->data, sizeof(error_t) * new_size);
}


void push_error(error_stack_t *stack, error_code_t code, 
    uint64_t lineno, uint64_t col, const char *format, ...)
{
    if (stack->num_errors == stack->size) {
        extend_error_stack(stack, (int) stack->size / 2);
    }

    va_list sizing_args;
    va_start(sizing_args, format);
    va_list actual_args;
    va_copy(actual_args, sizing_args);

    // Calculate number of bytes needed for message
    char msg[1 + vsnprintf(NULL, 0, format, sizing_args)];
    va_end(sizing_args);

    vsnprintf(msg, sizeof(msg), format, actual_args);
    va_end(actual_args);

    stack->data[stack->num_errors] = (error_t) { 
        .code = code,
        .lineno = lineno,
        .col = col,
        .msg = msg 
    };
}


error_t pop_error(error_stack_t *stack)
{
    error_t error = stack->data[stack->num_errors];
    stack->num_errors--;
    return error;
}
