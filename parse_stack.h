/**
 *
 */
#ifndef __PARSE_STACK_H__
#define __PARSE_STACK_H__

#include <stdint.h>

#include "moxi/commands.h"
#include "moxi/context.h"
#include "moxi/functions.h"
#include "moxi/sorts.h"
#include "moxi/systems.h"
#include "moxi/terms.h"

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
    TAG_VAR_DECL,         // pair <symbol, sort>
} tag_t;

#define NUM_TAGS (TAG_VAR_DECL + 1)

typedef struct term_binder {
    char *symbol;
    term_t term;
} term_binder_t;

typedef struct var_decl {
    char *symbol;
    sort_t sort;
} var_decl_t;

typedef struct parse_stack_elem {
    tag_t tag;
    union {
        identifier_t ident;
        sort_t sort;
        moxi_command_type_t command;
        term_binder_t term_binder;
        var_decl_t var_decl;
        char *symbol;
        uint64_t numeral;
    } value;
    uint32_t prev; // Previous stack frame
    uint32_t lineno;
    uint32_t col;
} parse_stack_elem_t;

void init_parse_stack_elem(parse_stack_elem_t *elem);
void delete_parse_stack_elem(parse_stack_elem_t *elem);

/**
 * The parser uses a stack to store the current state of the parser.
 *
 * The following term would result in the subsequent stack:
 *
 * `(op arg1 arg2 ... argN)`
 * [op, arg1, arg2, ..., argN]
 *
 * Once the closing parentheses of `op` is parsed, we call
 * `parse_stack_function` which then checks that the top N+1 elements match
 * the signature of `op`, pops the top N+1 elements, and pushes a term back onto
 * the stack in its place.
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
 * [<<x, Int>, TAG_VAR_DECL>, <<y, Int>, TAG_VAR_DECL>] --> adds x, y to
 * context
 * [<<x, Int>, TAG_VAR_DECL>, <<y, Int>, TAG_VAR_DECL>, <'>',
 * TAG_FUNCTION>]
 * [<<x, Int>, TAG_VAR_DECL>, <<y, Int>, TAG_VAR_DECL>, <'>',
 * TAG_FUNCTION>, <x, TAG_VARIABLE>]
 * [<<x, Int>, TAG_VAR_DECL>, <<y, Int>, TAG_VAR_DECL>, <'>',
 * TAG_FUNCTION>, <Int, TAG_TERM>]
 * [<<x, Int>, TAG_VAR_DECL>, <<y, Int>, TAG_VAR_DECL>, <'>',
 * TAG_FUNCTION>, <Int, TAG_TERM>, <y, TAG_VARIABLE>]
 * [<<x, Int>, TAG_VAR_DECL>, <<y, Int>, TAG_VAR_DECL>, <'>',
 * TAG_FUNCTION>, <Int, TAG_TERM>, <Int, TAG_TERM>]
 * [<<x, Int>, TAG_VAR_DECL>, <<y, Int>, TAG_VAR_DECL>, <Bool, TAG_TERM>]
 * [] --> removes x, y from context
 *
 *
 * `((_ extract 10 5) b)`
 *
 * [<extract, TAG_FUNCTION>]
 * [<extract, TAG_FUNCTION>, <10, TAG_NUMERAL>]
 * [<extract, TAG_FUNCTION>, <10, TAG_NUMERAL>, <5, TAG_NUMERAL>]
 * [<extract, TAG_FUNCTION>, <10, TAG_NUMERAL>, <5, TAG_NUMERAL>, <b,
 * TAG_VARIABLE>]
 * [<extract, TAG_FUNCTION>, <10, TAG_NUMERAL>, <5, TAG_NUMERAL>, <bv32,
 * TAG_TERM>]
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
 * Inside the process call, another tool might construct an AST or store the
 * term in a term manager (ex: Yices). Since we're just parsing, we only do a
 * check.
 */
typedef struct parse_stack {
    uint32_t size;
    uint32_t idx;
    parse_stack_elem_t *data;
    uint32_t top_frame;
} parse_stack_t;

#define parse_stack_MIN 256

void init_parse_stack(parse_stack_t *stack);
void delete_parse_stack(parse_stack_t *stack);

void parse_stack_extend(parse_stack_t *stack, uint32_t size);

inline uint32_t parse_stack_top_frame_size(parse_stack_t *stack) {
    return stack->idx - stack->top_frame + 1;
}

/**
 * Make the top element of the stack a new frame.
 */
inline void parse_stack_new_frame(parse_stack_t *stack) {
    stack->data[stack->idx].prev = stack->top_frame;
    stack->top_frame = stack->idx;
}

void parse_stack_push_elem(parse_stack_t *stack, parse_stack_elem_t *elem);
void parse_stack_push_symbol(parse_stack_t *stack, char *symbol);
void parse_stack_push_numeral(parse_stack_t *stack, uint64_t numeral);

void parse_stack_check_error(parse_stack_t *stack);

void parse_stack_error(parse_stack_t *stack, moxi_context_t *context);

/**
 * Checks that the top elements of `stack` starting at the top frame are symbols
 * that match a sort definition in `context`, pops them off the stack, then
 * pushes the resulting sort or an error to the stack.
 *
 * {TAG_SORT, TAG_SORT_CONSTRUCTOR}
 */
void parse_stack_sort(parse_stack_t *stack, moxi_context_t *context);

/**
 * TAG_VARIABLE
 */
void parse_stack_variable(parse_stack_t *stack, moxi_context_t *context);

/**
 * Checks that the elements of the top frame in `stack` match a function
 * signature in `context`, pops the
 *
 * {TAG_FUNCTION}
 */
void parse_stack_function(parse_stack_t *stack, moxi_context_t *context);

/**
 * TAG_SYSTEM
 */
void parse_stack_system(parse_stack_t *stack, moxi_context_t *context);

/**
 * TAG_SYMBOL
 */
void parse_stack_symbol(parse_stack_t *stack, moxi_context_t *context);

/**
 * TAG_BITVEC
 */
void parse_stack_bitvec(parse_stack_t *stack, moxi_context_t *context);

/**
 * TAG_INT
 */
void parse_stack_int(parse_stack_t *stack, moxi_context_t *context);

/**
 * TAG_DECIMAL
 */
void parse_stack_decimal(parse_stack_t *stack, moxi_context_t *context);

/**
 * TAG_NUMERAL
 */
void parse_stack_numeral(parse_stack_t *stack, moxi_context_t *context);

/**
 * TAG_TERM
 */
void parse_stack_term(parse_stack_t *stack, moxi_context_t *context);

/**
 * TAG_TERM_BINDER
 */
void parse_stack_term_binder(parse_stack_t *stack, moxi_context_t *context,
                             char *symbol);

/**
 * Creates and pushes a sort binder element onto `stack` and adds `symbol` to
 * `context`.
 *
 * [symbol, sort]
 *
 * TAG_VAR_DECL
 */
void parse_stack_var_decl(parse_stack_t *stack, moxi_context_t *context,
                          char *symbol, sort_t sort, uint32_t lineno,
                          uint32_t col);

extern void (*process_table[NUM_TAGS])(parse_stack_t *, moxi_context_t *);

/**
 * Pops `n` elements from `stack`.
 */
void parse_stack_pop(parse_stack_t *stack, uint32_t n);

/**
 * Pops the top frame off `stack` (the top `stack->idx - stack->top_frame`
 * elements).
 */
void parse_stack_pop_frame(parse_stack_t *stack);

#endif