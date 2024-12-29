/**
 * 
*/
#ifndef __TOKEN_H__
#define __TOKEN_H__

#include <stdbool.h>
#include <stdint.h>

typedef enum token_type {
    TOK_EOF,
    TOK_LP,
    TOK_RP,

    // constants
    TOK_NUMERAL,
    TOK_DECIMAL,
    TOK_BINARY,
    TOK_HEX,
    TOK_STRING,

    // reserved words
    TOK_RW_PAR,
    TOK_RW_NUM,
    TOK_RW_DEC,
    TOK_RW_STR,
    TOK_RW_UNDERSCORE,
    TOK_RW_BANG,
    TOK_RW_HASH,
    TOK_RW_AS,
    TOK_RW_LET,
    TOK_RW_EXISTS,
    TOK_RW_FORALL,
    TOK_RW_DEFINE_SYS,
    TOK_RW_CHECK_SYS,
    TOK_RW_DECLARE_SORT,
    TOK_RW_DECLARE_ENUM_SORT,
    TOK_RW_DECLARE_CONST,
    TOK_RW_DECLARE_FUN,
    TOK_RW_DEFINE_SORT,
    TOK_RW_DEFINE_CONST,
    TOK_RW_DEFINE_FUN,
    TOK_RW_EXIT,
    TOK_RW_SET_LOGIC,
    TOK_RW_ECHO,
    TOK_RW_RESET,
    TOK_RW_ASSERT,

    // keywords
    TOK_KW_INPUT,
    TOK_KW_OUTPUT,
    TOK_KW_LOCAL,
    TOK_KW_INIT,
    TOK_KW_TRANS,
    TOK_KW_INV,
    TOK_KW_SUBSYS,
    TOK_KW_ASSUMPTION,
    TOK_KW_REACHABLE,
    TOK_KW_FAIRNESS,
    TOK_KW_CURRENT,
    TOK_KW_QUERY,
    TOK_KW_QUERIES,
    TOK_KW_UNKNOWN,

    TOK_SYMBOL,

    // error tokens
    TOK_INVALID_CONSTANT,
    TOK_INVALID_NUMERAL_ZERO,
    TOK_INVALID_QUOTED_SYMBOL_EOF,
    TOK_INVALID_QUOTED_SYMBOL_CHAR,
    TOK_INVALID_STRING_EOF,
    TOK_INVALID_STRING_CHAR,
    TOK_INVALID_SYMBOL,
    TOK_INVALID_KEYWORD,
    TOK_ERROR,
} token_type_t;

#define NUM_TOKENS (TOK_ERROR+1)

// Lookup table for string representations of tokens
extern const char *token_type_str[NUM_TOKENS];

typedef struct token {
    const char *name;
    token_type_t type;
} token_t;

typedef enum theory_symbol_type {
    THY_SYM_BOOL,
    THY_SYM_TRUE,
    THY_SYM_FALSE,
    THY_SYM_NOT,
    THY_SYM_IMPLIES,
    THY_SYM_AND,
    THY_SYM_OR,
    THY_SYM_XOR,
    THY_SYM_EQ,
    THY_SYM_DISTINCT,
    THY_SYM_ITE,
    THY_SYM_ARRAY,
    THY_SYM_SELECT,
    THY_SYM_STORE,
    THY_SYM_INT,
    THY_SYM_REAL,
    THY_SYM_MINUS,
    THY_SYM_PLUS,
    THY_SYM_TIMES,
    THY_SYM_IDIV,
    THY_SYM_RDIV,
    THY_SYM_LE,
    THY_SYM_LT,
    THY_SYM_GE,
    THY_SYM_GT,
    THY_SYM_DIVISIBLE,
    THY_SYM_MOD,
    THY_SYM_ABS,
    THY_SYM_TO_REAL,
    THY_SYM_TO_INT,
    THY_SYM_BITVEC,
    THY_SYM_CONCAT,
    THY_SYM_EXTRACT,
    THY_SYM_REPEAT,
    THY_SYM_BVCOMP,
    THY_SYM_BVREDAND,
    THY_SYM_BVREDOR,
    THY_SYM_BVNOT,
    THY_SYM_BVAND,
    THY_SYM_BVOR,
    THY_SYM_BVNAND,
    THY_SYM_BVNOR,
    THY_SYM_BVXOR,
    THY_SYM_BVXNOR,
    THY_SYM_BVNEG,
    THY_SYM_BVADD,
    THY_SYM_BVSUB,
    THY_SYM_BVMUL,
    THY_SYM_BVUDIV,
    THY_SYM_BVUREM,
    THY_SYM_BVSDIV,
    THY_SYM_BVSREM,
    THY_SYM_BVSMOD,
    THY_SYM_BVSHL,
    THY_SYM_BVLSHR,
    THY_SYM_BVASHR,
    THY_SYM_ZERO_EXTEND,
    THY_SYM_SIGN_EXTEND,
    THY_SYM_ROTATE_LEFT,
    THY_SYM_ROTATE_RIGHT,
    THY_SYM_BVULT,
    THY_SYM_BVULE,
    THY_SYM_BVUGT,
    THY_SYM_BVUGE,
    THY_SYM_BVSLT,
    THY_SYM_BVSLE,
    THY_SYM_BVSGT,
    THY_SYM_BVSGE,
    THY_SYM_UNKNOWN,
} theory_symbol_type_t;

#define NUM_THEORY_SYMBOLS (THY_SYM_UNKNOWN+1)

typedef enum symbol_kind {
    TERM,
    SORT,
    SYSTEM,
    NONE,
} symbol_kind_t;

typedef struct theory_symbol {
    const char *name;
    theory_symbol_type_t type;
    symbol_kind_t kind;
} theory_symbol_t;

#endif
