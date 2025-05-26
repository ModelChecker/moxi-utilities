/**
 *
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

#include "ptr_stack.h"


void init_ptr_stack(ptr_stack_t *stack, void (*delete_elem)(void *))
{
    stack->capacity = PTR_STACK_MIN_SIZE;
    stack->size = 0;
    stack->data = malloc(sizeof(void*) * PTR_STACK_MIN_SIZE);
    stack->delete_elem = delete_elem;
}

void delete_ptr_stack(ptr_stack_t *stack)
{
    uint32_t i;
    for (i = 0; i < stack->size; ++i) {
        stack->delete_elem(stack->data[i]);
    }
    free(stack->data);
}

void *ptr_stack_top(ptr_stack_t *stack)
{
    assert(stack->size > 0);
    assert(stack->size <= stack->capacity);
    return stack->data[stack->size-1];
}

void ptr_stack_extend(ptr_stack_t *stack, uint32_t size)
{
    assert(stack->capacity < PTR_STACK_MAX_SIZE);
    size_t new_size = stack->capacity + size;
    stack->capacity = new_size;
    stack->data = realloc(stack->data, sizeof(void*) * new_size);
}

void ptr_stack_push(ptr_stack_t *stack, void *elem)
{
    stack->data[stack->size] = elem;
    stack->size++;
    if (stack->size == stack->capacity - 1) {
        ptr_stack_extend(stack, stack->capacity);
    }
}

void *ptr_stack_pop(ptr_stack_t *stack)
{
    assert(stack->size != 0);
    void *elem = stack->data[stack->size - 1];
    stack->size--;
    return elem;
}
