#include "token.h"

const char *token_type_str[MOXI_TOK_INVALID_SYMBOL+1] = {
    "<EOF>",
    "(",
    ")",
    "<numeral>",
    "<decimal>",
    "<binary>",
    "<hex>",
    "par",
    "NUMERAL",
    "DECIMAL",
    "STRING",
    "_",
    "!",
    "#",
    "as",
    "let",
    "exists",
    "forall",
    "define-system",
    "check-system",
    "declare-sort",
    "declare-enum-sort",
    "declare-const",
    "declare-fun",
    "define-sort",
    "define-const",
    "define-fun",
    "exit",
    "set-logic",
    "echo",
    ":input",
    ":output",
    ":local",
    ":init",
    ":trans",
    ":inv",
    ":subsys",
    ":assume",
    ":reach",
    ":fair",
    ":current",
    ":query",
    ":queries",
    "<symbol>",
    "<error-const>",
    "<error-num-zero>",
    "<error-quote-eof>",
    "<error-quote-char>",
    "<error-symbol>",
    "<error>"
};

bool is_indexed_symbol[MOXI_SYM_BVSGE+1] = {
    false, // MOXI_SYM_UNKNOWN
    false, // MOXI_SYM_BOOL
    false, // MOXI_SYM_TRUE
    false, // MOXI_SYM_FALSE
    false, // MOXI_SYM_NOT
    false, // MOXI_SYM_IMPLIES
    false, // MOXI_SYM_AND
    false, // MOXI_SYM_OR
    false, // MOXI_SYM_XOR
    false, // MOXI_SYM_EQ
    false, // MOXI_SYM_DISTINCT
    false, // MOXI_SYM_ITE
    false, // MOXI_SYM_ARRAY
    false, // MOXI_SYM_SELECT
    false, // MOXI_SYM_STORE
    false, // MOXI_SYM_INT
    false, // MOXI_SYM_REAL
    false, // MOXI_SYM_MINUS
    false, // MOXI_SYM_PLUS
    false, // MOXI_SYM_TIMES
    false, // MOXI_SYM_DIVIDES
    false, // MOXI_SYM_LE
    false, // MOXI_SYM_LT
    false, // MOXI_SYM_GE
    false, // MOXI_SYM_GT
    false, // MOXI_SYM_DIV
    false, // MOXI_SYM_MOD
    false, // MOXI_SYM_ABS
    true,  // MOXI_SYM_BITVEC
    false, // MOXI_SYM_CONCAT
    true,  // MOXI_SYM_EXTRACT
    true,  // MOXI_SYM_REPEAT
    false, // MOXI_SYM_BVCOMP
    false, // MOXI_SYM_BVREDAND
    false, // MOXI_SYM_BVREDOR
    false, // MOXI_SYM_BVNOT
    false, // MOXI_SYM_BVAND
    false, // MOXI_SYM_BVOR
    false, // MOXI_SYM_BVNAND
    false, // MOXI_SYM_BVNOR
    false, // MOXI_SYM_BVXOR
    false, // MOXI_SYM_BVXNOR
    false, // MOXI_SYM_BVNEG
    false, // MOXI_SYM_BVADD
    false, // MOXI_SYM_BVSUB
    false, // MOXI_SYM_BVMUL
    false, // MOXI_SYM_BVUDIV
    false, // MOXI_SYM_BVUREM
    false, // MOXI_SYM_BVSDIV
    false, // MOXI_SYM_BVSREM
    false, // MOXI_SYM_BVSMOD
    false, // MOXI_SYM_BVSHL
    false, // MOXI_SYM_BVLSHR
    false, // MOXI_SYM_BVASHR
    true,  // MOXI_SYM_ZERO_EXTEND
    true,  // MOXI_SYM_SIGN_EXTEND
    true,  // MOXI_SYM_ROTATE_LEFT
    true,  // MOXI_SYM_ROTATE_RIGHT
    false, // MOXI_SYM_BVULT
    false, // MOXI_SYM_BVULE
    false, // MOXI_SYM_BVUGT
    false, // MOXI_SYM_BVUGE
    false, // MOXI_SYM_BVSLT
    false, // MOXI_SYM_BVSLE
    false, // MOXI_SYM_BVSGT
    false, // MOXI_SYM_BVSGE
};

