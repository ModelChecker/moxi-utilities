/**
 * 
*/
#ifndef __TOKEN_H__
#define __TOKEN_H__

#include <stdbool.h>


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
    TOK_KW_ASSUME,
    TOK_KW_REACH,
    TOK_KW_FAIR,
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
    char *name;
    token_type_t type;
} token_t;

typedef enum symbol_type {
    SYM_BOOL,
    SYM_TRUE,
    SYM_FALSE,
    SYM_NOT,
    SYM_IMPLIES,
    SYM_AND,
    SYM_OR,
    SYM_XOR,
    SYM_EQ,
    SYM_DISTINCT,
    SYM_ITE,
    SYM_ARRAY,
    SYM_SELECT,
    SYM_STORE,
    SYM_INT,
    SYM_REAL,
    SYM_MINUS,
    SYM_PLUS,
    SYM_TIMES,
    SYM_DIVIDES,
    SYM_LE,
    SYM_LT,
    SYM_GE,
    SYM_GT,
    SYM_DIV,
    SYM_MOD,
    SYM_ABS,
    SYM_BITVEC,
    SYM_CONCAT,
    SYM_EXTRACT,
    SYM_REPEAT,
    SYM_BVCOMP,
    SYM_BVREDAND,
    SYM_BVREDOR,
    SYM_BVNOT,
    SYM_BVAND,
    SYM_BVOR,
    SYM_BVNAND,
    SYM_BVNOR,
    SYM_BVXOR,
    SYM_BVXNOR,
    SYM_BVNEG,
    SYM_BVADD,
    SYM_BVSUB,
    SYM_BVMUL,
    SYM_BVUDIV,
    SYM_BVUREM,
    SYM_BVSDIV,
    SYM_BVSREM,
    SYM_BVSMOD,
    SYM_BVSHL,
    SYM_BVLSHR,
    SYM_BVASHR,
    SYM_ZERO_EXTEND,
    SYM_SIGN_EXTEND,
    SYM_ROTATE_LEFT,
    SYM_ROTATE_RIGHT,
    SYM_BVULT,
    SYM_BVULE,
    SYM_BVUGT,
    SYM_BVUGE,
    SYM_BVSLT,
    SYM_BVSLE,
    SYM_BVSGT,
    SYM_BVSGE,
    SYM_SYMBOL,
    SYM_UNKNOWN,
} symbol_type_t;

#define NUM_SYMBOLS (SYM_UNKNOWN+1)

// Lookup table for string representations of symbols
extern const char *symbol_type_str[NUM_SYMBOLS];
extern bool is_indexed_symbol[NUM_SYMBOLS];


#endif