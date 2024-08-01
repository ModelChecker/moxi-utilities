/**
 * 
*/
#ifndef __IDENTIFIERS_H__
#define __IDENTIFIERS_H__

#include <stdint.h>
#include <stdbool.h>

/**
 * Indexed identifiers:
 * (_ BitVec <numeral>)
 * (_ extract <numeral> <numeral>)
 * (_ repeat <numeral>)
 * (_ zero_extend <numeral>)
 * (_ sign_extend <numeral>)
 * (_ rotate_right <numeral>)
 * (_ rotate_left <numeral>)
*/


typedef union {
    char *symbol;
    uint32_t numeral;
} index_t;

typedef struct identifier {
    char *symbol;
    index_t *indices;
} identifier_t;


void init_identifier(identifier_t *ident, char *sym, index_t *idxs);
void delete_identifier(identifier_t *ident, char *sym, index_t *idxs);

index_t get_identifier_index(identifier_t ident, uint32_t idx);
bool is_symbol(identifier_t *i1, char *symbol);
bool is_same_identifier(identifier_t *i1, identifier_t *i2);


#endif