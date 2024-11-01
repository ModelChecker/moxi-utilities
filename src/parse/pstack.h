/**
 *
 */
#ifndef __PSTACK_H__
#define __PSTACK_H__

#include <setjmp.h>
#include <stdint.h>

#include "io/file_reader.h"
#include "moxi/context.h"
#include "moxi/sort.h"
#include "util/char_buffer.h"

/**
 * Sort checking works on a parse stack (pstack) of syntactic elements. Each
 * high-level element is assigned a "frame" (ex: sorts, terms) where each frame
 * is checked for validity then replaced with its corresponding data structure.
 * For example, a frame that represents a sort will be checked that the sort is
 * well-formed, then popped off the stack, then a `sort_t` will be pushed to the
 * stack.
 *
 *
 * For example, consider operation of the stack for checking a sort:
 *
 *     (Array Int Real)
 *
 * The stack will first start a frame and push the symbol "Array" onto the
 * stack.
 *
 * [F0, "Array"]
 *
 * Next, it starts a new frame and pushes the symbol "Int".
 *
 * [F0, "Array", F1, "Int"]
 *
 * Since "Int" is a sort with no parameters, the stack evaluates the top frame,
 * checking that it is indeed a valid sort. The frame has no indices nor
 * parameters, which is correct for "Int", so the frame is popped and a sort is
 * pushed.
 *
 * [F0, "Array", <Int>]
 *
 * The same operation then occurs for "Real".
 *
 * [F0, "Array", <Int>, F1, "Real"]
 * [F0, "Array", <Int>, <Real>]
 *
 * Finally, we reach the end of frame 0, so we check that the frame has the
 * correct number of parameters for an "Array" sort (2) with no indices, which
 * we have.
 *
 * [<Array, Int, Real>]
 */

/**
 * The tag tells the stack how to interpret each stack element
 */
typedef enum {
    TAG_BASE, // Bottom of stack
    TAG_FRAME,
    TAG_NUMERAL,
    TAG_SORT,
    TAG_SORT_CONSTRUCTOR,
    TAG_SYSTEM,
    TAG_SYMBOL,
    TAG_IDENTIFIER,
    TAG_BITVEC,  // bit-vector constant
    TAG_DECIMAL, // decimal constant
    TAG_TERM,
    TAG_ERROR,
} tag_t;

#define NUM_TAGS (TAG_ERROR + 1)
extern const char *tag_str[NUM_TAGS];

/**
 * The frame type defines how the elements in the current frame are to be
 * interpreted.
 */
typedef enum frame_type {
    FRM_NOOP,
    FRM_SORT,
    FRM_TERM,
    FRM_EXIT,
    FRM_RESET,
    FRM_ASSERT,
    FRM_ECHO,
    FRM_SET_LOGIC,
    FRM_DEFINE_SYS,
    FRM_CHECK_SYS,
    FRM_DECLARE_SORT,
    FRM_DECLARE_ENUM_SORT,
    FRM_DECLARE_CONST,
    FRM_DECLARE_FUN,
    FRM_DEFINE_SORT,
    FRM_DEFINE_CONST,
    FRM_DEFINE_FUN,
    FRM_VAR_DECL,
    FRM_TERM_BIND,
    FRM_ERROR
} frame_type_t;

#define NUM_FRM_TYPES (FRM_ERROR + 1)
extern const char *frame_str[NUM_FRM_TYPES];

typedef enum pstack_error_type {
    BAD_FRAME_SIZE = -1,
    BAD_TAG = -2,
    BAD_SYMBOL_KIND = -3,
    BAD_SORT = -4,
    BAD_BVEXTRACT_IDX = -5,
    BAD_LOGIC = -6,
    BAD_TERM = -7,
    BAD_COMMAND = -8
} pstack_error_type_t;

// Terms are represented by their sorts
typedef sort_t term_t;

typedef struct pstack_elem {
    tag_t tag;
    union {
        frame_type_t frame_type;
        sort_t sort;
        int64_t numeral;
        char *symbol;
    } value;
    uint32_t frame; // Current stack frame ID
    loc_t loc;
} pstack_elem_t;

void delete_pstack_elem(pstack_elem_t *elem);

// A parse stack
typedef struct pstack {
    const char *filename; // Filename of the input file for error messages
    pstack_elem_t *data;
    uint32_t capacity;
    uint32_t size;   // Number of elements in pstack
    uint32_t frame; // Index of top frame element
    int status;
    var_kind_t cur_var_kind; // Used for var declarations
    jmp_buf env;
} pstack_t;

#define PSTACK_MIN_SIZE 256
#define PSTACK_MAX_SIZE 262144

void init_pstack(pstack_t *pstack, const char *filename);
void delete_pstack(pstack_t *pstack);
void pstack_reset(pstack_t *pstack);

/**
 * Increase the size of pstack by `size` elements
 */
void pstack_extend(pstack_t *pstack, uint32_t size);

static inline uint32_t pstack_top_frame_size(pstack_t *pstack)
{
    return pstack->size - pstack->frame - 1;
}

static inline pstack_elem_t *pstack_top_frame(pstack_t *pstack)
{
    return &pstack->data[pstack->frame];
}

static inline loc_t pstack_top_frame_loc(pstack_t *pstack)
{
    return pstack->data[pstack->frame].loc;
}

void pstack_push_frame(pstack_t *pstack, frame_type_t ftype, loc_t loc);
void pstack_push_term(pstack_t *pstack, term_t term, loc_t loc);
void pstack_push_sort(pstack_t *pstack, sort_t sort, loc_t loc);
void pstack_push_symbol(pstack_t *pstack, char_buffer_t *str, loc_t loc);
void pstack_push_numeral(pstack_t *pstack, char_buffer_t *str, loc_t loc);
void pstack_push_decimal(pstack_t *pstack, char_buffer_t *str, loc_t loc);
void pstack_push_error(pstack_t *pstack, loc_t loc);

static inline void pstack_set_vars_input(pstack_t *pstack)
{
    pstack->cur_var_kind = INPUT_VAR;
}

static inline void pstack_set_vars_output(pstack_t *pstack)
{
    pstack->cur_var_kind = OUTPUT_VAR;
}

static inline void pstack_set_vars_local(pstack_t *pstack)
{
    pstack->cur_var_kind = LOCAL_VAR;
}

static inline void pstack_set_vars_logic(pstack_t *pstack)
{
    pstack->cur_var_kind = LOGIC_VAR;
}

/**
 * Pops `n` elements from `pstack`.
 */
// void pstack_pop(pstack_t *pstack, uint32_t n);

/**
 * Pops the top frame off `pstack`.
 */
// void pstack_pop_frame(pstack_t *pstack);

// Function tables for parse table management
extern void (*frame_eval_table[NUM_FRM_TYPES])(pstack_t *, context_t *);
extern void (*term_eval_table[NUM_SYMBOLS])(pstack_t *, context_t *);

/**
 * Executes top frame of `pstack` according to the function defined in
 * `frame_eval_table`.
 */
void pstack_eval_frame(pstack_t *pstack, context_t *ctx);

void pstack_print_frame(pstack_t *pstack);

#endif