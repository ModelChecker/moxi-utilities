#include "parse/parse_error.h"


void init_parse_error_stack(parse_error_stack_t *stack)
{
    stack->size = PARSE_ERROR_STACK_MIN;
    stack->idx = 0;
    stack->data = malloc(sizeof(parse_error_t) * PARSE_ERROR_STACK_MIN);
}


void delete_parse_error_stack(parse_error_stack_t *stack)
{
    free(stack->data);
}


void extend_parse_error_stack(parse_error_stack_t *stack, size_t size)
{
    size_t new_size = stack->size + size;
    stack->size = new_size;
    stack->data = realloc(stack->data, sizeof(parse_error_t) * new_size);
}


void push_parse_error(parse_error_stack_t *stack, parse_error_code_t code, 
    uint64_t lineno, uint64_t col, char *msg)
{
    if (stack->idx == stack->size) {
        extend_parse_error_stack(stack, (int) stack->size / 2);
    }

    stack->data[stack->idx] = (parse_error_t) { 
        .code = code,
        .lineno = lineno,
        .col = col,
        .msg = msg 
    };
}


parse_error_t pop_parse_error(parse_error_stack_t *stack)
{
    parse_error_t error = stack->data[stack->idx];
    stack->idx--;
    return error;
}
