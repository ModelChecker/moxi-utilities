/**
 * 
*/
#ifndef __INT_STACK_H__
#define __INT_STACK_H__

#include <stdint.h>


typedef struct int_stack {
    uint32_t size;
    uint32_t top;
    uint32_t *data;
} int_stack_t;

#define INT_STACK_MIN 256
#define INT_STACK_MAX 4098

void init_int_stack(int_stack_t *stack);
void delete_int_stack(int_stack_t *stack);

uint32_t int_stack_top(int_stack_t *stack);
void int_stack_extend(int_stack_t *stack, uint32_t size);
void int_stack_push(int_stack_t *stack, uint32_t state);
uint32_t int_stack_pop(int_stack_t *stack);

#endif