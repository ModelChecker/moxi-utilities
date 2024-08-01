#include "token.h"

const char *token_type_str[NUM_TOKENS] = {
    "<EOF>",
    "(",
    ")",
    "<numeral>",
    "<decimal>",
    "<binary>",
    "<hex>",
    "<string>",
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
    "reset",
    "assert",
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
    "<unknown-keyword>",
    "<symbol>",
    "<error-const>",
    "<error-num-zero>",
    "<error-quote-eof>",
    "<error-quote-char>",
    "<error-string-eof>",
    "<error-string-char>",
    "<error-symbol>",
    "<error-keyword>",
    "<error>"
};

const char *symbol_type_str[NUM_SYMBOLS] = {
    "Bool",
    "true",
    "false",
    "not",
    "implies",
    "and",
    "or",
    "xor",
    "eq",
    "distinct",
    "ite",
    "Array",
    "select",
    "store",
    "Int",
    "Real",
    "-",
    "+",
    "*",
    "divisible",
    "<=",
    "<",
    ">=",
    ">",
    "/",
    "mod",
    "abs",
    "BitVec",
    "concat",
    "extract",
    "repeat",
    "bvcomp",
    "bvredand",
    "bvredor",
    "bvnot",
    "bvand",
    "bvor",
    "bvnand",
    "bvnor",
    "bvxor",
    "bvxnor",
    "bvneg",
    "bvadd",
    "bvsub",
    "bvmul",
    "bvudiv",
    "bvurem",
    "bvsdiv",
    "bvsrem",
    "bvsmod",
    "bvshl",
    "bvlshr",
    "bvashr",
    "zero_extend",
    "sign_extend",
    "rotate_left",
    "rotate_right",
    "bvult",
    "bvule",
    "bvugt",
    "bvuge",
    "bvslt",
    "bvsle",
    "bvsgt",
    "bvsge",
    "<unknown>",
    "<symbol>",
};


bool is_indexed_symbol[NUM_SYMBOLS] = {
    false, // SYM_BOOL
    false, // SYM_TRUE
    false, // SYM_FALSE
    false, // SYM_NOT
    false, // SYM_IMPLIES
    false, // SYM_AND
    false, // SYM_OR
    false, // SYM_XOR
    false, // SYM_EQ
    false, // SYM_DISTINCT
    false, // SYM_ITE
    false, // SYM_ARRAY
    false, // SYM_SELECT
    false, // SYM_STORE
    false, // SYM_INT
    false, // SYM_REAL
    false, // SYM_MINUS
    false, // SYM_PLUS
    false, // SYM_TIMES
    false, // SYM_DIVIDES
    false, // SYM_LE
    false, // SYM_LT
    false, // SYM_GE
    false, // SYM_GT
    false, // SYM_DIV
    false, // SYM_MOD
    false, // SYM_ABS
    true,  // SYM_BITVEC
    false, // SYM_CONCAT
    true,  // SYM_EXTRACT
    true,  // SYM_REPEAT
    false, // SYM_BVCOMP
    false, // SYM_BVREDAND
    false, // SYM_BVREDOR
    false, // SYM_BVNOT
    false, // SYM_BVAND
    false, // SYM_BVOR
    false, // SYM_BVNAND
    false, // SYM_BVNOR
    false, // SYM_BVXOR
    false, // SYM_BVXNOR
    false, // SYM_BVNEG
    false, // SYM_BVADD
    false, // SYM_BVSUB
    false, // SYM_BVMUL
    false, // SYM_BVUDIV
    false, // SYM_BVUREM
    false, // SYM_BVSDIV
    false, // SYM_BVSREM
    false, // SYM_BVSMOD
    false, // SYM_BVSHL
    false, // SYM_BVLSHR
    false, // SYM_BVASHR
    true,  // SYM_ZERO_EXTEND
    true,  // SYM_SIGN_EXTEND
    true,  // SYM_ROTATE_LEFT
    true,  // SYM_ROTATE_RIGHT
    false, // SYM_BVULT
    false, // SYM_BVULE
    false, // SYM_BVUGT
    false, // SYM_BVUGE
    false, // SYM_BVSLT
    false, // SYM_BVSLE
    false, // SYM_BVSGT
    false, // SYM_BVSGE
    false, // SYM_SYMBOL
    false, // SYM_UNKNOWN
};

