/**
 *
 */
#ifndef __STACK_H__
#define __STACK_H__

#include <stdint.h>

typedef struct ptr_stack {
    uint32_t capacity;
    uint32_t size;
    void **data;
    void (*delete_elem)(void *);
} ptr_stack_t;

#define PTR_STACK_MIN_SIZE 256
#define PTR_STACK_MAX_SIZE 65536

void init_ptr_stack(ptr_stack_t *stack, void (*delete_elem)(void *));
void delete_ptr_stack(ptr_stack_t *stack);
void *ptr_stack_top(ptr_stack_t *stack);
void ptr_stack_push(ptr_stack_t *stack, void *elem);
void *ptr_stack_pop(ptr_stack_t *stack);

#endif
