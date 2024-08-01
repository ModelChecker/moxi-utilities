/**
 * 
*/
#include <stdarg.h>
#include <stddef.h>
#include <assert.h>

#include "parse/parse_stack.h"


void (*process_table[TAG_SORT_BINDER+1])(term_stack_t *, context_t *) = {
    term_stack_error,               // TAG_NONE,
    term_stack_error,               // TAG_ERROR,
    term_stack_process_numeral,     // TAG_NUMERAL,          
    term_stack_process_sort,        // TAG_SORT,             
    term_stack_process_variable,    // TAG_VARIABLE,         
    term_stack_process_function,    // TAG_FUNCTION,         
    term_stack_process_sort,        // TAG_SORT_CONSTRUCTOR, 
    term_stack_process_system,      // TAG_SYSTEM,           
    term_stack_process_symbol,      // TAG_IDENTIFIER,      
    term_stack_process_bitvec,      // TAG_BITVEC,           
    term_stack_process_int,         // TAG_INT,              
    term_stack_process_decimal,     // TAG_DECIMAL,          
    term_stack_process_term,        // TAG_TERM,             
    term_stack_process_term_binder, // TAG_TERM_BINDER,      
    term_stack_process_sort_binder, // TAG_SORT_BINDER,      
};


/**
 * Checks that the top elements of `stack` starting at the top frame are symbols that match a sort
 * definition in `context`, pops them off the stack, then pushes the resulting sort or an error to
 * the stack.
 * 
 * Basic sort:       [<identifier>] -> [<sort>]
 * Sort constructor: [<identifier>, <sort>, ..., <sort>] -> [<sort>]
*/
void term_stack_process_sort(term_stack_t *stack, context_t *context)
{   
    term_stack_elem_t cur_elem;
    term_stack_elem_t *new_elem;
    symbol_table_t *sort_table;
    char *symbol;

    cur_elem = stack->data[stack->top_frame];
    sort_table = &context->symbol_table;
    symbol = cur_elem.value.ident.symbol;

    init_term_stack_elem(new_elem);
    new_elem->prev = cur_elem.prev;

    assert(cur_elem.tag == TAG_IDENTIFIER);
    uint32_t arity = symbol_table_find(sort_table, cur_elem.value.symbol);

    if (arity != term_stack_top_frame_size(stack)) {
        term_stack_pop_frame(stack);
        term_stack_push_error(stack, 0, 0, 0, "invalid arity for sort constructor");
        return;
    }

    uint32_t i;
    for(i = stack->idx; i >= stack->top_frame; --i) {
        symbol = stack->data[i].value.ident.symbol;
        if (stack->data[i].tag == TAG_SORT) {
            term_stack_push_error(stack, 0, 0, 0, "expected a valid sort");
        } else {
            term_stack_pop(stack, 1);
        }

    }
}   

