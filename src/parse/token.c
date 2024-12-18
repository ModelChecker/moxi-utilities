#include <stddef.h>
#include <string.h>
#include <stdlib.h>

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

const symbol_t *get_symbol(const char *name, uint32_t len)
{
    return in_moxi_sym(name, len);
}

void init_symbol(symbol_t *symbol, const char *name, uint32_t len, symbol_type_t type,
                 symbol_kind_t kind)
{
    symbol->name = malloc((len + 1) * sizeof(char));
    strncpy(symbol->name, name, len);
    symbol->name[len] = '\0';
    symbol->type = type;
    symbol->kind = kind;
    symbol->len = len;
}

symbol_t *new_symbol(const char *name, uint32_t len, symbol_type_t type, symbol_kind_t kind)
{
    symbol_t *symbol = malloc(sizeof(symbol_t));
    init_symbol(symbol, name, len, type, kind);
    return symbol;
}

void delete_symbol(symbol_t *symbol)
{
    free(symbol->name);
    free(symbol);
}