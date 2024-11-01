/**
 * 
 */
#ifndef __LOGIC_H__
#define __LOGIC_H__

#include <stdbool.h>

typedef enum logic_type {
    //  Base logics (with quantifiers)
    AX,   // arrays
    BV,   // bitvectors
    IDL,  // integer difference logic
    LIA,  // linear integer arithmetic
    LRA,  // linear real arithmetic
    LIRA, // mixed linear arithmetic
    NIA,  // non-linear integer arithmetic
    NRA,  // non-linear real arithmetic
    NIRA, // non-linear mixed arithmetic
    RDL,  // real difference logic
    UF,   // uninterpreted functions

    //  Arrays + some other theory
    ABV,   // arrays + bitvectors
    ALIA,  // arrays + linear integer arithmetic
    ALRA,  // arrays + linear real arithmetic
    ALIRA, // arrays + mixed linear arithmetic
    ANIA,  // arrays + non-linear integer arithmetic
    ANRA,  // arrays + non-linear real arithmetic
    ANIRA, // arrays + mixed/non-linear arithmetic
    AUF,   // arrays + uninterpreted functions

    //  Uninterpreted function + another theory
    UFBV,    // uninterpreted functions + bitvectors
    UFBVLIA, // uninterpreted functions + bitvectors + linear integer
                   // arithmetic
    UFIDL,   // uninterpreted functions + integer difference logic
    UFLIA,   // uninterpreted functions + linear integer arithmetic
    UFLRA,   // uninterpreted functions + linear real arithmetic
    UFLIRA,  // uninterpreted functions + mixed linear arithmetic
    UFNIA,   // uninterpreted functions + non-linear integer arithmetic
    UFNRA,   // uninterpreted functions + non-linear real arithmetic
    UFNIRA,  // uninterpreted functions + mixed, non-linear arithmetic
    UFRDL,   // uninterpreted functions + real difference logic

    //  Arrays + uninterpreted functions + another theory
    AUFBV,    // arrays + uninterpreted functions + bitvectors
    AUFBVLIA, // arrays + uninterpreted functions + bitvectors + linear
                    // integer arithmetic
    AUFBVNIA, // arrays + uninterpreted functions + bitvectors + nonlinear
                    // integer arithmetic
    AUFLIA,   // arrays + uninterpreted functions + linear integer
                    // arithmetic
    AUFLRA,   // arrays + uninterpreted functions + linear real arithmetic
    AUFLIRA, // arrays + uninterpreted functions + mixed linear arithmetic
    AUFNIA,  // arrays + uninterpreted functions + non-linear integer
                   // arithmetic
    AUFNRA,  // arrays + uninterpreted functions + non-linear real
                   // arithmetic
    AUFNIRA, // arrays + uninterpreted functions + mixed, non-linear
                   // arithmetic

    /*
     * Quantifier-free fragments
     */
    QF_AX,   // arrays
    QF_BV,   // bitvectors
    QF_IDL,  // integer difference logic
    QF_LIA,  // linear integer arithmetic
    QF_LRA,  // linear real arithmetic
    QF_LIRA, // mixed linear arithmetic
    QF_NIA,  // non-linear integer arithmetic
    QF_NRA,  // non-linear real arithmetic
    QF_NIRA, // non-linear mixed arithmetic
    QF_RDL,  // real difference logic
    QF_UF,   // uninterpreted functions

    //  Arrays + some other theory
    QF_ABV,   // arrays + bitvectors
    QF_ALIA,  // arrays + linear integer arithmetic
    QF_ALRA,  // arrays + linear real arithmetic
    QF_ALIRA, // arrays + mixed linear arithmetic
    QF_ANIA,  // arrays + non-linear integer arithmetic
    QF_ANRA,  // arrays + non-linear real arithmetic
    QF_ANIRA, // arrays + mixed/non-linear arithmetic
    QF_AUF,   // arrays + uninterpreted functions

    //  Uninterpreted function + another theory
    QF_UFBV,    // uninterpreted functions + bitvectors
    QF_UFBVLIA, // uninterpreted functions + bitvectors + linear integer
                      // arithmetic
    QF_UFIDL,   // uninterpreted functions + integer difference logic
    QF_UFLIA,   // uninterpreted functions + linear integer arithmetic
    QF_UFLRA,   // uninterpreted functions + linear real arithmetic
    QF_UFLIRA,  // uninterpreted functions + mixed linear arithmetic
    QF_UFNIA,   // uninterpreted functions + non-linear integer arithmetic
    QF_UFNRA,   // uninterpreted functions + non-linear real arithmetic
    QF_UFNIRA,  // uninterpreted functions + mixed, non-linear arithmetic
    QF_UFRDL,   // uninterpreted functions + real difference logic

    //  Arrays + uninterpreted functions + another theory
    QF_AUFBV,    // arrays + uninterpreted functions + bitvectors
    QF_AUFBVLIA, // arrays + uninterpreted functions + bitvectors + linear
                       // integer arithmetic
    QF_AUFBVNIA, // arrays + uninterpreted functions + bitvectors +
                       // nonlinear integer arithmetic
    QF_AUFLIA,   // arrays + uninterpreted functions + linear integer
                       // arithmetic
    QF_AUFLRA,   // arrays + uninterpreted functions + linear real
                       // arithmetic
    QF_AUFLIRA,  // arrays + uninterpreted functions + mixed linear
                       // arithmetic
    QF_AUFNIA,   // arrays + uninterpreted functions + non-linear integer
                       // arithmetic
    QF_AUFNRA,   // arrays + uninterpreted functions + non-linear real
                       // arithmetic
    QF_AUFNIRA,  // arrays + uninterpreted functions + mixed, non-linear
                       // arithmetic

    LOGIC_NONE,
    LOGIC_ALL,
    LOGIC_UNKNOWN,
} logic_type_t;

#define NUM_LOGICS (LOGIC_UNKNOWN+1)

// A temporary struct used for gperf functions
typedef struct logic {
    char *name;
    logic_type_t type;
} logic_t;

extern logic_t unkown_logic;
extern logic_t no_logic;

extern const char *logic_str[NUM_LOGICS];

extern bool logic_is_supported[NUM_LOGICS];
extern bool logic_has_arrays[NUM_LOGICS];
extern bool logic_has_arithmetic[NUM_LOGICS];
extern bool logic_has_bitvectors[NUM_LOGICS];
extern bool logic_is_linear_arith[NUM_LOGICS];
extern bool logic_is_difference_logic[NUM_LOGICS];
extern bool logic_has_ints[NUM_LOGICS];
extern bool logic_has_reals[NUM_LOGICS];
extern bool logic_has_quantifiers[NUM_LOGICS];
extern bool logic_has_uf[NUM_LOGICS];

#endif