/**
 * 
*/
#include <stdarg.h>
#include <stddef.h>
#include <assert.h>

#include "parse/parse_stack.h"


void (*process_table[NUM_TAGS])(parse_stack_t *, moxi_context_t *) = {
    parse_stack_error,               // TAG_NONE,
    parse_stack_error,               // TAG_ERROR,
    parse_stack_numeral,     // TAG_NUMERAL,          
    parse_stack_sort,        // TAG_SORT,             
    parse_stack_variable,    // TAG_VARIABLE,         
    parse_stack_function,    // TAG_FUNCTION,         
    parse_stack_sort,        // TAG_SORT_CONSTRUCTOR, 
    parse_stack_system,      // TAG_SYSTEM,           
    parse_stack_symbol,      // TAG_IDENTIFIER,      
    parse_stack_bitvec,      // TAG_BITVEC,           
    parse_stack_int,         // TAG_INT,              
    parse_stack_decimal,     // TAG_DECIMAL,          
    parse_stack_term,        // TAG_TERM,             
    parse_stack_term_binder, // TAG_TERM_BINDER,      
    parse_stack_var_decl,    // TAG_SORT_BINDER,      
};


/**
 * Checks that the top elements of `stack` starting at the top frame are symbols
 * that match a sort definition in `context`, pops them off the stack, then
 * pushes the resulting sort or an error to the stack.
 *
 * Basic sort:       [<identifier>] -> [<sort>] 
 * Sort constructor: [<identifier>, <sort>, ..., <sort>] -> [<sort>]
*/
void parse_stack_sort(parse_stack_t *stack, moxi_context_t *context)
{   
    parse_stack_elem_t cur_elem;
    parse_stack_elem_t *new_elem;
    symbol_table_t *sort_table;
    char *symbol;

    cur_elem = stack->data[stack->top_frame];
    sort_table = &context->symbol_table;
    symbol = cur_elem.value.ident.symbol;

    init_parse_stack_elem(new_elem);
    new_elem->prev = cur_elem.prev;

    assert(cur_elem.tag == TAG_IDENTIFIER);
    uint32_t arity = symbol_table_find(sort_table, cur_elem.value.symbol);

    if (arity != parse_stack_top_frame_size(stack)) {
        parse_stack_pop_frame(stack);
        parse_stack_push_error(stack, 0, 0, 0, "invalid arity for sort constructor");
        return;
    }

    uint32_t i;
    for(i = stack->idx; i >= stack->top_frame; --i) {
        symbol = stack->data[i].value.ident.symbol;
        if (stack->data[i].tag == TAG_SORT) {
            parse_stack_push_error(stack, 0, 0, 0, "expected a valid sort");
        } else {
            parse_stack_pop(stack, 1);
        }

    }
}   

