/**
 *
 */
#ifndef __INT_STACK_H__
#define __INT_STACK_H__

#include <stdint.h>

typedef struct int_stack {
    uint32_t size;
    uint32_t top;
    int *data;
} int_stack_t;

#define INT_STACK_MIN_SIZE 256
#define INT_STACK_MAX_SIZE 65536

void init_int_stack(int_stack_t *stack);
void delete_int_stack(int_stack_t *stack);

int int_stack_top(int_stack_t *stack);
void int_stack_push(int_stack_t *stack, int i);
int int_stack_pop(int_stack_t *stack);

#endif