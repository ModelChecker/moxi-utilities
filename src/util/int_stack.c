/**
 *
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

#include "int_stack.h"


void init_int_stack(int_stack_t *stack)
{
    stack->capacity = INT_STACK_MIN_SIZE;
    stack->size = 0;
    stack->data = malloc(sizeof(int) * INT_STACK_MIN_SIZE);
}


void delete_int_stack(int_stack_t *stack)
{
    free(stack->data);
}


int int_stack_top(int_stack_t *stack)
{
    assert(stack->size > 0);
    return stack->data[stack->size-1];
}


void int_stack_extend(int_stack_t *stack, uint32_t size)
{
    assert(stack->capacity < INT_STACK_MAX_SIZE);
    size_t new_size = stack->capacity + size;
    stack->capacity = new_size;
    stack->data = realloc(stack->data, sizeof(uint32_t) * new_size);
}


void int_stack_push(int_stack_t *stack, int i)
{
    stack->data[stack->size] = i;
    stack->size++;
    if (stack->size == stack->capacity) {
        int_stack_extend(stack, stack->capacity / 2);
    }
}


int int_stack_pop(int_stack_t *stack)
{
    assert(stack->size != 0);
    int i = stack->data[stack->size - 1];
    stack->size--;
    return i;
}
