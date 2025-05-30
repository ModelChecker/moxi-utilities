/**
 *
 */
#ifndef __PSTACK_H__
#define __PSTACK_H__

#include <setjmp.h>
#include <stdint.h>

#include "io/file_reader.h"
#include "moxi/context.h"
#include "bitvec.h"
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
    TAG_ATTR,
    TAG_NUMERAL,
    TAG_SORT,
    TAG_SORT_CONSTRUCTOR,
    TAG_SYSTEM,
    TAG_SYMBOL,
    TAG_IDENTIFIER,
    TAG_BITVEC,  // bit-vector constant
    TAG_DECIMAL, // decimal constant
    TAG_TERM,
    TAG_QUANTIFIER,
    TAG_LET_BINDER,
    TAG_AS,
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
    FRM_NOOP_KEEP,
    FRM_SORT,
    FRM_TERM,
    FRM_VAR_DECL,
    FRM_TERM_BIND,
    FRM_EXIT,
    FRM_RESET,
    FRM_ASSERT,
    FRM_ECHO,
    FRM_SET_LOGIC,
    FRM_DECLARE_ENUM_SORT,
    FRM_DECLARE_SORT,
    FRM_DEFINE_SORT,
    FRM_DECLARE_CONST,
    FRM_DEFINE_CONST,
    FRM_DECLARE_FUN,
    FRM_DEFINE_FUN,
    FRM_DEFINE_SYS,
    FRM_CHECK_SYS,
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
    BAD_COMMAND = -8,
    BAD_ATTR = -9
} pstack_error_type_t;

typedef struct pstack_elem {
    tag_t tag;
    union {
        frame_type_t frame_type;
        token_type_t tok;
        sort_t sort;
        int64_t numeral;
        bv64_t bitvec;
        char *str;
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
    uint32_t size;  // Number of elements in pstack
    uint32_t frame; // Index of top frame element
    int status;
    var_kind_t cur_var_kind; // Used for var declarations
    bool input_next_vars_enabled;  // Allow primed input vars in current term
    bool output_next_vars_enabled; // Allow primed output vars in current term
    bool local_next_vars_enabled;  // Allow primed local vars in current term
    jmp_buf env;
    moxi_context_t ctx;
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

// Returns the number of elements top frame of `pstack`
static inline uint32_t pstack_top_frame_size(pstack_t *pstack)
{
    return pstack->size - pstack->frame;
}

static inline pstack_elem_t *pstack_top_frame(pstack_t *pstack)
{
    return &pstack->data[pstack->frame];
}

static inline loc_t pstack_top_frame_loc(pstack_t *pstack)
{
    return pstack->data[pstack->frame].loc;
}

void pstack_push_frame(pstack_t *, frame_type_t, loc_t);
void pstack_push_attr(pstack_t *, token_type_t, loc_t);
void pstack_push_term(pstack_t *, term_t, loc_t);
void pstack_push_sort(pstack_t *, sort_t , loc_t);
void pstack_push_string(pstack_t *, char_buffer_t *, loc_t);
void pstack_push_numeral(pstack_t *, char_buffer_t *, loc_t);
void pstack_push_decimal(pstack_t *, char_buffer_t *, loc_t);
void pstack_push_binary(pstack_t *, char_buffer_t *, loc_t);
void pstack_push_hex(pstack_t *, char_buffer_t *, loc_t);
void pstack_push_quantifier(pstack_t *, token_type_t, loc_t);
void pstack_push_let(pstack_t *, loc_t);
void pstack_push_as(pstack_t *, loc_t);
void pstack_push_error(pstack_t *, loc_t);

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

static inline void pstack_enable_next_vars(pstack_t *pstack)
{
    pstack->input_next_vars_enabled = true;
    pstack->output_next_vars_enabled = true;
    pstack->local_next_vars_enabled = true;
}

static inline void pstack_disable_next_vars(pstack_t *pstack)
{
    pstack->input_next_vars_enabled = false;
    pstack->output_next_vars_enabled = false;
    pstack->local_next_vars_enabled = false;
}

static inline void pstack_enable_input_next_vars(pstack_t *pstack)
{
    pstack->input_next_vars_enabled = true;
    pstack->output_next_vars_enabled = false;
    pstack->local_next_vars_enabled = false;
}

// Function tables for parse table management
// extern void (*frame_eval_table[NUM_FRM_TYPES])(pstack_t *, moxi_context_t *);
// extern void (*term_eval_table[NUM_THEORY_SYMBOLS])(pstack_t *, moxi_context_t *);

/**
 * Executes top frame of `pstack` according to the function defined in
 * `frame_eval_table`.
 */
void pstack_eval_frame(pstack_t *pstack);
void pstack_print_frame(pstack_t *pstack);

#endif
