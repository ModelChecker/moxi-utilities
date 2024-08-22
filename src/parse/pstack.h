/**
 *
 */
#ifndef __PSTACK_H__
#define __PSTACK_H__

#include <stdint.h>
#include <setjmp.h>

#include "moxi/sort.h"
#include "moxi/context.h"
#include "util/string_buffer.h"

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
 * [F0, "Array", <Int>, F1, "Real"] [F0, "Array", <Int>, <Real>]
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
    TAG_INT,     // integer constant
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

// Terms are represented by their sorts
typedef sort_t term_t;

typedef struct pstack_elem {
    tag_t tag;
    union {
        frame_type_t frame_type;
        sort_t *sort;
        int64_t numeral;
        char *symbol;
    } value;
    uint32_t frame; // Current stack frame ID
    uint32_t lineno;
    uint32_t col;
} pstack_elem_t;

void delete_pstack_elem(pstack_elem_t *elem);

/**
 * The parser uses a stack to store the current state of the parser.
 */
typedef struct pstack {
    pstack_elem_t *data;
    uint32_t size;
    uint32_t top;   // Number of elements in pstack
    uint32_t frame; // Index of top frame element
    int status;
    jmp_buf env;
} pstack_t;

#define PSTACK_MIN_SIZE 256
#define PSTACK_MAX_SIZE 65536

void init_pstack(pstack_t *pstack);
void delete_pstack(pstack_t *pstack);
void pstack_reset(pstack_t *pstack);

/**
 * Increase the size of pstack by `size` elements
 */
void pstack_extend(pstack_t *pstack, uint32_t size);

static inline uint32_t pstack_top_frame_size(pstack_t *pstack)
{
    return pstack->top - pstack->frame - 1;
}

static inline pstack_elem_t *pstack_top_frame(pstack_t *pstack)
{
    return &pstack->data[pstack->frame];
}

static inline uint32_t pstack_top_frame_lineno(pstack_t *pstack)
{
    return pstack->data[pstack->frame].lineno;
}

static inline uint32_t pstack_top_frame_col(pstack_t *pstack)
{
    return pstack->data[pstack->frame].col;
}

void pstack_push_frame(pstack_t *pstack, frame_type_t ftype, uint32_t lineno,
                       uint32_t col);
void pstack_push_term(pstack_t *pstack, term_t *term, uint32_t lineno,
                      uint32_t col);
void pstack_push_sort(pstack_t *pstack, sort_t *sort, uint32_t lineno,
                      uint32_t col);
void pstack_push_symbol(pstack_t *pstack, string_buffer_t *str, uint32_t lineno,
                        uint32_t col);
void pstack_push_numeral(pstack_t *pstack, string_buffer_t *str,
                         uint32_t lineno, uint32_t col);
void pstack_push_error(pstack_t *pstack, uint32_t lineno, uint32_t col);

/**
 * Pops `n` elements from `pstack`.
 */
void pstack_pop(pstack_t *pstack, uint32_t n);

/**
 * Pops the top frame off `pstack`.
 */
void pstack_pop_frame(pstack_t *pstack);

/**
 * Function table for parse table management
 */
extern void (*frame_eval_table[NUM_FRM_TYPES])(pstack_t *, context_t *);

/**
 * Executes top frame of `pstack` according to the function defined in
 * `frame_eval_table`.
 */
void pstack_eval_frame(pstack_t *pstack, context_t *ctx);

void pstack_print_frame(pstack_t *pstack);


#endif