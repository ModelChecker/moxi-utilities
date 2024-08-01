/**
 * 
*/
#ifndef __PARSE_STACK_H__
#define __PARSE_STACK_H__

#include <stdint.h>

#include "moxi/context.h"
#include "moxi/commands.h"
#include "moxi/terms.h"
#include "moxi/sorts.h"
#include "moxi/functions.h"
#include "moxi/systems.h"


typedef enum {
    TAG_NONE,
    TAG_ERROR,
    TAG_NUMERAL,          // numeral
    TAG_SORT,             // sort
    TAG_VARIABLE,         // variable
    TAG_FUNCTION,         // functions
    TAG_SORT_CONSTRUCTOR, // sort constructors
    TAG_SYSTEM,           // system
    TAG_IDENTIFIER,       // other symbol
    TAG_BITVEC,           // bit-vector constant
    TAG_INT,              // integer constant
    TAG_DECIMAL,          // decimal constant
    TAG_TERM,             // (post-processed) term 
    TAG_TERM_BINDER,      // pair <symbol, term>
    TAG_SORT_BINDER,      // pair <symbol, sort>
} tag_t;


typedef struct term_binder {
    char *symbol;
    term_t term;
} term_binder_t;


typedef struct sort_binder {
    char *symbol;
    sort_t sort;
} sort_binder_t;


typedef struct term_stack_elem {
    tag_t tag;
    union {
        identifier_t ident;
        sort_t sort;
        moxi_command_type_t command;
        term_binder_t term_binder;
        sort_binder_t sort_binder;
        char *symbol;
        uint64_t numeral;
    } value;
    uint32_t prev; // Previous stack frame
    uint32_t lineno;
    uint32_t col;
} term_stack_elem_t;

void init_term_stack_elem(term_stack_elem_t *elem);
void delete_term_stack_elem(term_stack_elem_t *elem);


/**
 * The parser uses a stack to store the current state of the parser. 
 * 
 * The following term would result in the subsequent stack:
 * 
 * `(op arg1 arg2 ... argN)`
 * [op, arg1, arg2, ..., argN]
 * 
 * Once the closing parentheses of `op` is parsed, we call `term_stack_process_function` which then
 * checks that the top N+1 elements match the signature of `op`, pops the top N+1 elements, and
 * pushes a term back onto the stack in its place.
 * 
 * `(+ a b c)`
 * 
 * [<+, TAG_FUNCTION>]
 * [<+, TAG_FUNCTION>, <a, TAG_VARIABLE>]
 * [<+, TAG_FUNCTION>, <Int, TAG_TERM>]
 * [<+, TAG_FUNCTION>, <Int, TAG_TERM>, <b, TAG_VARIABLE>]
 * [<+, TAG_FUNCTION>, <Int, TAG_TERM>, <Int, TAG_TERM>]
 * [<+, TAG_FUNCTION>, <Int, TAG_TERM>, <Int, TAG_TERM>, <c, TAG_VARIABLE>]
 * [<+, TAG_FUNCTION>, <Int, TAG_TERM>, <Int, TAG_TERM>, <Int, TAG_TERM>]
 * [<Int, TAG_TERM>]
 * 
 * 
 * `(exists ((x Int) (y Int)) (> y x))`
 * 
 * [<<x, Int>, TAG_SORT_BINDER>, <<y, Int>, TAG_SORT_BINDER>] --> adds x, y to context
 * [<<x, Int>, TAG_SORT_BINDER>, <<y, Int>, TAG_SORT_BINDER>, <'>', TAG_FUNCTION>]
 * [<<x, Int>, TAG_SORT_BINDER>, <<y, Int>, TAG_SORT_BINDER>, <'>', TAG_FUNCTION>, <x, TAG_VARIABLE>]
 * [<<x, Int>, TAG_SORT_BINDER>, <<y, Int>, TAG_SORT_BINDER>, <'>', TAG_FUNCTION>, <Int, TAG_TERM>]
 * [<<x, Int>, TAG_SORT_BINDER>, <<y, Int>, TAG_SORT_BINDER>, <'>', TAG_FUNCTION>, <Int, TAG_TERM>, <y, TAG_VARIABLE>]
 * [<<x, Int>, TAG_SORT_BINDER>, <<y, Int>, TAG_SORT_BINDER>, <'>', TAG_FUNCTION>, <Int, TAG_TERM>, <Int, TAG_TERM>]
 * [<<x, Int>, TAG_SORT_BINDER>, <<y, Int>, TAG_SORT_BINDER>, <Bool, TAG_TERM>]
 * [] --> removes x, y from context
 * 
 * 
 * `((_ extract 10 5) b)`
 * 
 * [<extract, TAG_FUNCTION>]
 * [<extract, TAG_FUNCTION>, <10, TAG_NUMERAL>]
 * [<extract, TAG_FUNCTION>, <10, TAG_NUMERAL>, <5, TAG_NUMERAL>]
 * [<extract, TAG_FUNCTION>, <10, TAG_NUMERAL>, <5, TAG_NUMERAL>, <b, TAG_VARIABLE>]
 * [<extract, TAG_FUNCTION>, <10, TAG_NUMERAL>, <5, TAG_NUMERAL>, <bv32, TAG_TERM>]
 * [<bv6, TAG_TERM>]
 * 
 * 
 * For sorts...
 * `(Array (_ BitVec 16) Int)`
 * 
 * [<Array, TAG_SORT_CONSTRUCTOR>]
 * [<Array, TAG_SORT_CONSTRUCTOR>, <BitVec, TAG_SYMBOL>, <16, TAG_NUMERAL>]
 * [<Array, TAG_SORT_CONSTRUCTOR>, <bv16, TAG_SORT>]
 * [<Array, TAG_SORT_CONSTRUCTOR>, <bv16, TAG_SORT>, <Int, TAG_SORT>]
 * [<<Array, bv16, Int>, TAG_SORT>]
 * 
 * 
 * 
 * Inside the process call, another tool might construct an AST or store the term in a term manager
 * (ex: Yices). Since we're just parsing, we only do a check.
*/
typedef struct term_stack {
    uint32_t size;
    uint32_t idx;
    term_stack_elem_t *data;
    uint32_t top_frame;
} term_stack_t;

#define TERM_STACK_MIN 256

void init_term_stack(term_stack_t *stack);
void delete_term_stack(term_stack_t *stack);

void term_stack_extend(term_stack_t *stack, uint32_t size);

inline uint32_t term_stack_top_frame_size(term_stack_t *stack) 
{
    return stack->idx - stack->top_frame + 1;
}

/**
 * Make the top element of the stack a new frame.
*/
inline void term_stack_new_frame(term_stack_t *stack)
{
    stack->data[stack->idx].prev = stack->top_frame;
    stack->top_frame = stack->idx;
}

void term_stack_push_elem(term_stack_t *stack, term_stack_elem_t *elem);
void term_stack_push_symbol(term_stack_t *stack, char *symbol);
void term_stack_push_numeral(term_stack_t *stack, uint64_t numeral);

void term_stack_check_error(term_stack_t *stack);

void term_stack_error(term_stack_t *stack, context_t *context);

/**
 * Checks that the top elements of `stack` starting at the top frame are symbols that match a sort
 * definition in `context`, pops them off the stack, then pushes the resulting sort or an error to
 * the stack.
 * 
 * {TAG_SORT, TAG_SORT_CONSTRUCTOR}
*/
void term_stack_process_sort(term_stack_t *stack, context_t *context);

/**
 * TAG_VARIABLE
*/
void term_stack_process_variable(term_stack_t *stack, context_t *context);

/**
 * Checks that the elements of the top frame in `stack` match a function signature in `context`,
 * pops the 
 * 
 * {TAG_FUNCTION}
*/
void term_stack_process_function(term_stack_t *stack, context_t *context);

/**
 * TAG_SYSTEM
*/
void term_stack_process_system(term_stack_t *stack, context_t *context);

/**
 * TAG_SYMBOL
*/
void term_stack_process_symbol(term_stack_t *stack, context_t *context);

/**
 * TAG_BITVEC
*/
void term_stack_process_bitvec(term_stack_t *stack, context_t *context);

/**
 * TAG_INT
*/
void term_stack_process_int(term_stack_t *stack, context_t *context);

/**
 * TAG_DECIMAL
*/
void term_stack_process_decimal(term_stack_t *stack, context_t *context);

/**
 * TAG_NUMERAL
*/
void term_stack_process_numeral(term_stack_t *stack, context_t *context);

/**
 * TAG_TERM
*/
void term_stack_process_term(term_stack_t *stack, context_t *context);

/**
 * TAG_TERM_BINDER
*/
void term_stack_process_term_binder(term_stack_t *stack, context_t *context, char *symbol);

/**
 * Creates and pushes a sort binder element onto `stack` and adds `symbol` to `context`.
 * 
 * [symbol, sort]
 * 
 * TAG_SORT_BINDER
*/
void term_stack_process_sort_binder(term_stack_t *stack, context_t *context, 
    char *symbol, sort_t sort, uint32_t lineno, uint32_t col);


extern void (*process_table[TAG_SORT_BINDER+1])(term_stack_t *, context_t *);


/**
 * Pops `n` elements from `stack`.
*/
void term_stack_pop(term_stack_t *stack, uint32_t n);

/**
 * Pops the top frame off `stack` (the top `stack->idx - stack->top_frame` elements).
*/
void term_stack_pop_frame(term_stack_t *stack);

#endif