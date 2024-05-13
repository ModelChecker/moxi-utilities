/**
 * 
*/
#ifndef __CHECK_H__
#define __CHECK_H__

#include <stdint.h>
#include <stdbool.h>
#include <string.h>

#include "parse/parse_stack.h"


inline bool check_bool_sort(parse_stack_t *stack, uint32_t elem) {
    return stack->data[elem].tag == TAG_SORT && 
           !strcmp(stack->data[elem].value.ident.symbol, "Bool");
}

bool check_real_sort(parse_stack_t *stack, uint32_t elem);
bool check_bitvec_sort(parse_stack_t *stack, uint32_t elem);
bool check_array_sort(parse_stack_t *stack, uint32_t elem);


#endif