/**
 *
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

#include "stack.h"


void init_stack(vstack_t *stack, void (*delete_elem)(void *))
{
    stack->capacity = STACK_MIN_SIZE;
    stack->size = 0;
    stack->data = malloc(sizeof(void*) * STACK_MIN_SIZE);
    stack->delete_elem = delete_elem;
}

void delete_stack(vstack_t *stack)
{
    uint32_t i;
    for (i = 0; i < stack->size; ++i) {
        stack->delete_elem(stack->data[i]);
    }
    free(stack->data);
}

void *stack_top(vstack_t *stack)
{
    assert(stack->size > 0);
    return stack->data[stack->size-1];
}

void stack_extend(vstack_t *stack, uint32_t size)
{
    assert(stack->capacity < STACK_MAX_SIZE);
    uint32_t new_size = stack->capacity + size;
    stack->capacity = new_size;
    stack->data = realloc(stack->data, sizeof(uint32_t) * new_size);
}

void stack_push(vstack_t *stack, void *elem)
{
    if (stack->size == stack->capacity) {
        stack_extend(stack, stack->capacity / 2);
    }
    stack->data[stack->size] = elem;
    stack->size++;
}

void *stack_pop(vstack_t *stack)
{
    assert(stack->size != 0);
    void *elem = stack->data[stack->size - 1];
    stack->size--;
    return elem;
}
