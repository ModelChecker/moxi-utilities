/**
 * 
*/
#ifndef __AST_H__
#define __AST_H__

#include <stdint.h>


typedef enum node_type {
    MOXI_NUMERAL,
    MOXI_DECIMAL,
    MOXI_BINARY,
    MOXI_HEX,

    MOXI_PAR,
    MOXI_NUM,
    MOXI_DEC,
    MOXI_STR,
    MOXI_UNDERSCORE,
    MOXI_BANG,
    MOXI_HASH,
    MOXI_AS,
    MOXI_LET,
    MOXI_EXISTS,
    MOXI_FORALL,
    
    MOXI_DEFINE_SYS,
    MOXI_CHECK_SYS,
    MOXI_DECLARE_SORT,
    MOXI_DECLARE_ENUM_SORT,
    MOXI_DECLARE_CONST,
    MOXI_DECLARE_FUN,
    MOXI_DEFINE_SORT,
    MOXI_DEFINE_CONST,
    MOXI_DEFINE_FUN,
    MOXI_EXIT,
    MOXI_SET_LOGIC,
    MOXI_ECHO,

    MOXI_INPUT,
    MOXI_OUTPUT,
    MOXI_LOCAL,
    MOXI_INIT,
    MOXI_TRANS,
    MOXI_INV,
    MOXI_SUBSYS,
    MOXI_ASSUME,
    MOXI_REACH,
    MOXI_FAIR,
    MOXI_CURRENT,
    MOXI_QUERY,
    MOXI_QUERIES,

    MOXI_NONE
} node_type_t;


typedef struct moxi_node {
    uint64_t lineno;
    uint64_t col;
    node_type type;
    char *symbol;
    uint32_t *children;
} moxi_node_t;


typedef struct moxi_ast {
    moxi_node_t *tree;
    uint64_t size;
} moxi_ast_t;  



#endif