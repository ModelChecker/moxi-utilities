/**
 *
 */
#ifndef __STACK_H__
#define __STACK_H__

#include <stdint.h>

typedef struct stack {
    uint32_t capacity;
    uint32_t size;
    void **data;
    void (*delete_elem)(void *);
} vstack_t;

#define STACK_MIN_SIZE 256
#define STACK_MAX_SIZE 65536

void init_stack(vstack_t *stack, void (*delete_elem)(void *));
void delete_stack(vstack_t *stack);
void *stack_top(vstack_t *stack);
void stack_push(vstack_t *stack, void *elem);
void *stack_pop(vstack_t *stack);

#endif