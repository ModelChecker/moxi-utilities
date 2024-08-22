#include <stddef.h>
#include <string.h>

#include "parse/token.h"
#include "parse/hash_symbol.h"

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
    "<symbol>",
    "<unknown>",
};

uint8_t symbol_num_indices[NUM_SYMBOLS] = {
    0, // BOOL
    0, // TRUE
    0, // FALSE
    0, // NOT
    0, // IMPLIES
    0, // AND
    0, // OR
    0, // XOR
    0, // EQ
    0, // DISTINCT
    0, // ITE
    0, // ARRAY
    0, // SELECT
    0, // STORE
    0, // INT
    0, // REAL
    0, // MINUS
    0, // PLUS
    0, // TIMES
    0, // DIVIDES
    0, // LE
    0, // LT
    0, // GE
    0, // GT
    0, // DIV
    0, // MOD
    0, // ABS
    1, // BITVEC
    0, // CONCAT
    2, // EXTRACT
    1, // REPEAT
    0, // BVCOMP
    0, // BVREDAND
    0, // BVREDOR
    0, // BVNOT
    0, // BVAND
    0, // BVOR
    0, // BVNAND
    0, // BVNOR
    0, // BVXOR
    0, // BVXNOR
    0, // BVNEG
    0, // BVADD
    0, // BVSUB
    0, // BVMUL
    0, // BVUDIV
    0, // BVUREM
    0, // BVSDIV
    0, // BVSREM
    0, // BVSMOD
    0, // BVSHL
    0, // BVLSHR
    0, // BVASHR
    1, // ZERO_EXTEND
    1, // SIGN_EXTEND
    1, // ROTATE_LEFT
    1, // ROTATE_RIGHT
    0, // BVULT
    0, // BVULE
    0, // BVUGT
    0, // BVUGE
    0, // BVSLT
    0, // BVSLE
    0, // BVSGT
    0, // BVSGE
    0, // SYMBOL
    0, // UNKNOWN
};

uint8_t get_num_indices(const char *symbol)
{
    const symbol_t *symbol_obj = in_moxi_sym(symbol, strlen(symbol));
    if (symbol_obj != NULL) {
        return symbol_num_indices[symbol_obj->type];
    } else {
        return 0;
    }
}

symbol_kind_t symbol_kind[NUM_SYMBOLS] = {
    SYM_KIND_SORT, // BOOL
    SYM_KIND_TERM, // TRUE
    SYM_KIND_TERM, // FALSE
    SYM_KIND_TERM, // NOT
    SYM_KIND_TERM, // IMPLIES
    SYM_KIND_TERM, // AND
    SYM_KIND_TERM, // OR
    SYM_KIND_TERM, // XOR
    SYM_KIND_TERM, // EQ
    SYM_KIND_TERM, // DISTINCT
    SYM_KIND_TERM, // ITE
    SYM_KIND_SORT, // ARRAY
    SYM_KIND_TERM, // SELECT
    SYM_KIND_TERM, // STORE
    SYM_KIND_SORT, // INT
    SYM_KIND_SORT, // REAL
    SYM_KIND_TERM, // MINUS
    SYM_KIND_TERM, // PLUS
    SYM_KIND_TERM, // TIMES
    SYM_KIND_TERM, // DIVIDES
    SYM_KIND_TERM, // LE
    SYM_KIND_TERM, // LT
    SYM_KIND_TERM, // GE
    SYM_KIND_TERM, // GT
    SYM_KIND_TERM, // DIV
    SYM_KIND_TERM, // MOD
    SYM_KIND_TERM, // ABS
    SYM_KIND_SORT, // BITVEC
    SYM_KIND_TERM, // CONCAT
    SYM_KIND_TERM, // EXTRACT
    SYM_KIND_TERM, // REPEAT
    SYM_KIND_TERM, // BVCOMP
    SYM_KIND_TERM, // BVREDAND
    SYM_KIND_TERM, // BVREDOR
    SYM_KIND_TERM, // BVNOT
    SYM_KIND_TERM, // BVAND
    SYM_KIND_TERM, // BVOR
    SYM_KIND_TERM, // BVNAND
    SYM_KIND_TERM, // BVNOR
    SYM_KIND_TERM, // BVXOR
    SYM_KIND_TERM, // BVXNOR
    SYM_KIND_TERM, // BVNEG
    SYM_KIND_TERM, // BVADD
    SYM_KIND_TERM, // BVSUB
    SYM_KIND_TERM, // BVMUL
    SYM_KIND_TERM, // BVUDIV
    SYM_KIND_TERM, // BVUREM
    SYM_KIND_TERM, // BVSDIV
    SYM_KIND_TERM, // BVSREM
    SYM_KIND_TERM, // BVSMOD
    SYM_KIND_TERM, // BVSHL
    SYM_KIND_TERM, // BVLSHR
    SYM_KIND_TERM, // BVASHR
    SYM_KIND_TERM, // ZERO_EXTEND
    SYM_KIND_TERM, // SIGN_EXTEND
    SYM_KIND_TERM, // ROTATE_LEFT
    SYM_KIND_TERM, // ROTATE_RIGHT
    SYM_KIND_TERM, // BVULT
    SYM_KIND_TERM, // BVULE
    SYM_KIND_TERM, // BVUGT
    SYM_KIND_TERM, // BVUGE
    SYM_KIND_TERM, // BVSLT
    SYM_KIND_TERM, // BVSLE
    SYM_KIND_TERM, // BVSGT
    SYM_KIND_TERM, // BVSGE
    SYM_KIND_NONE, // SYMBOL
    SYM_KIND_NONE, // UNKNOWN
};