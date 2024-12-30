/**
 * 
 */
#include "moxi/logic.h"

// Global shared value for unknown logic
logic_t unkown_logic = (logic_t) {
    .name = "UNKNOWN",
    .type = LOGIC_UNKNOWN
};

// Global shared value for no logic
logic_t no_logic = (logic_t) {
    .name = "NONE",
    .type = LOGIC_NONE
};

const char *logic_str[NUM_LOGICS] = {
    "AX",
    "BV",
    "IDL",
    "LIA",
    "LRA",
    "LIRA",
    "NIA",
    "NRA",
    "NIRA",
    "RDL",
    "UF",
    "ABV",
    "ALIA",
    "ALRA",
    "ALIRA",
    "ANIA",
    "ANRA",
    "ANIRA",
    "AUF",
    "UFBV",
    "UFBVLIA",
    "UFIDL",
    "UFLIA",
    "UFLRA",
    "UFLIRA",
    "UFNIA",
    "UFNRA",
    "UFNIRA",
    "UFRDL",
    "AUFBV",
    "AUFBVLIA",
    "AUFBVNIA",
    "AUFLIA",
    "AUFLRA",
    "AUFLIRA",
    "AUFNIA",
    "AUFNRA",
    "AUFNIRA",
    "QF_AX",
    "QF_BV",
    "QF_IDL",
    "QF_LIA",
    "QF_LRA",
    "QF_LIRA",
    "QF_NIA",
    "QF_NRA",
    "QF_NIRA",
    "QF_RDL",
    "QF_UF",
    "QF_ABV",
    "QF_ALIA",
    "QF_ALRA",
    "QF_ALIRA",
    "QF_ANIA",
    "QF_ANRA",
    "QF_ANIRA",
    "QF_AUF",
    "QF_UFBV",
    "QF_UFBVLIA",
    "QF_UFIDL",
    "QF_UFLIA",
    "QF_UFLRA",
    "QF_UFLIRA",
    "QF_UFNIA",
    "QF_UFNRA",
    "QF_UFNIRA",
    "QF_UFRDL",
    "QF_AUFBV",
    "QF_AUFBVLIA",
    "QF_AUFBVNIA",
    "QF_AUFLIA",
    "QF_AUFLRA",
    "QF_AUFLIRA",
    "QF_AUFNIA",
    "QF_AUFNRA",
    "QF_AUFNIRA",
    "LOGIC_NONE",
    "LOGIC_ALL",
    "LOGIC_UNKNOWN"
};

bool logic_is_supported[NUM_LOGICS] = {
    true,  // AX
    true,  // BV
    false, // IDL
    true,  // LIA
    true,  // LRA
    true,  // LIRA
    true,  // NIA
    true,  // NRA
    true,  // NIRA
    false, // RDL
    true,  // UF
    true,  // ABV
    false, // ALIA
    false, // ALRA
    false, // ALIRA
    false, // ANIA
    false, // ANRA
    false, // ANIRA
    true, // AUF
    true, // UFBV
    true, // UFBVLIA
    false, // UFIDL
    true, // UFLIA
    true, // UFLRA
    true, // UFLIRA
    true, // UFNIA
    true, // UFNRA
    true, // UFNIRA
    false, // UFRDL
    false, // AUFBV
    false, // AUFBVLIA
    false, // AUFBVNIA
    false, // AUFLIA
    false, // AUFLRA
    false, // AUFLIRA
    false, // AUFNIA
    false, // AUFNRA
    false, // AUFNIRA
    false, // QF_AX
    true, // QF_BV
    false, // QF_IDL
    true,  // QF_LIA
    true, // QF_LRA
    true, // QF_LIRA
    true, // QF_NIA
    true, // QF_NRA
    true, // QF_NIRA
    false, // QF_RDL
    true, // QF_UF
    true, // QF_ABV
    false, // QF_ALIA
    false, // QF_ALRA
    false, // QF_ALIRA
    false, // QF_ANIA
    false, // QF_ANRA
    false, // QF_ANIRA
    false, // QF_AUF
    true, // QF_UFBV
    true, // QF_UFBVLIA
    false, // QF_UFIDL
    true, // QF_UFLIA
    true, // QF_UFLRA
    true, // QF_UFLIRA
    true, // QF_UFNIA
    true, // QF_UFNRA
    true, // QF_UFNIRA
    true, // QF_UFRDL
    false, // QF_AUFBV
    false, // QF_AUFBVLIA
    false, // QF_AUFBVNIA
    false, // QF_AUFLIA
    false, // QF_AUFLRA
    false, // QF_AUFLIRA
    false, // QF_AUFNIA
    false, // QF_AUFNRA
    false, // QF_AUFNIRA
    false, // LOGIC_NONE
    false, // LOGIC_ALL
    false, // LOGIC_UNKNOWN
};

bool logic_has_arrays[NUM_LOGICS] = {
    true,  // AX
    false, // BV
    false, // IDL
    false, // LIA
    false, // LRA
    false, // LIRA
    false, // NIA
    false, // NRA
    false, // NIRA
    false, // RDL
    false, // UF
    true,  // ABV
    true,  // ALIA
    true,  // ALRA
    true,  // ALIRA
    true,  // ANIA
    true,  // ANRA
    true,  // ANIRA
    true,  // AUF
    false, // UFBV
    false, // UFBVLIA
    false, // UFIDL
    false, // UFLIA
    false, // UFLRA
    false, // UFLIRA
    false, // UFNIA
    false, // UFNRA
    false, // UFNIRA
    false, // UFRDL
    true,  // AUFBV
    true,  // AUFBVLIA
    true,  // AUFBVNIA
    true,  // AUFLIA
    true,  // AUFLRA
    true,  // AUFLIRA
    true,  // AUFNIA
    true,  // AUFNRA
    true,  // AUFNIRA
    true,  // QF_AX
    false, // QF_BV
    false, // QF_IDL
    false, // QF_LIA
    false, // QF_LRA
    false, // QF_LIRA
    false, // QF_NIA
    false, // QF_NRA
    false, // QF_NIRA
    false, // QF_RDL
    false, // QF_UF
    true,  // QF_ABV
    true,  // QF_ALIA
    true,  // QF_ALRA
    true,  // QF_ALIRA
    true,  // QF_ANIA
    true,  // QF_ANRA
    true,  // QF_ANIRA
    true,  // QF_AUF
    false, // QF_UFBV
    false, // QF_UFBVLIA
    false, // QF_UFIDL
    false, // QF_UFLIA
    false, // QF_UFLRA
    false, // QF_UFLIRA
    false, // QF_UFNIA
    false, // QF_UFNRA
    false, // QF_UFNIRA
    false, // QF_UFRDL
    true,  // QF_AUFBV
    true,  // QF_AUFBVLIA
    true,  // QF_AUFBVNIA
    true,  // QF_AUFLIA
    true,  // QF_AUFLRA
    true,  // QF_AUFLIRA
    true,  // QF_AUFNIA
    true,  // QF_AUFNRA
    true,  // QF_AUFNIRA
    false, // LOGIC_NONE
    false, // LOGIC_ALL
    false, // LOGIC_UNKNOWN
};

bool logic_has_arithmetic[NUM_LOGICS] = {
    false, // AX
    false, // BV
    true,  // IDL
    true,  // LIA
    true,  // LRA
    true,  // LIRA
    true,  // NIA
    true,  // NRA
    true,  // NIRA
    true,  // RDL
    false, // UF
    false, // ABV
    true,  // ALIA
    true,  // ALRA
    true,  // ALIRA
    true,  // ANIA
    true,  // ANRA
    true,  // ANIRA
    false, // AUF
    false, // UFBV
    true,  // UFBVLIA
    true,  // UFIDL
    true,  // UFLIA
    true,  // UFLRA
    true,  // UFLIRA
    true,  // UFNIA
    true,  // UFNRA
    true,  // UFNIRA
    true,  // UFRDL
    false, // AUFBV
    true,  // AUFBVLIA
    true,  // AUFBVNIA
    true,  // AUFLIA
    true,  // AUFLRA
    true,  // AUFLIRA
    true,  // AUFNIA
    true,  // AUFNRA
    true,  // AUFNIRA
    false, // QF_AX
    false, // QF_BV
    true,  // QF_IDL
    true,  // QF_LIA
    true,  // QF_LRA
    true,  // QF_LIRA
    true,  // QF_NIA
    true,  // QF_NRA
    true,  // QF_NIRA
    true,  // QF_RDL
    false, // QF_UF
    false, // QF_ABV
    true,  // QF_ALIA
    true,  // QF_ALRA
    true,  // QF_ALIRA
    true,  // QF_ANIA
    true,  // QF_ANRA
    true,  // QF_ANIRA
    false, // QF_AUF
    false, // QF_UFBV
    true,  // QF_UFBVLIA
    true,  // QF_UFIDL
    true,  // QF_UFLIA
    true,  // QF_UFLRA
    true,  // QF_UFLIRA
    true,  // QF_UFNIA
    true,  // QF_UFNRA
    true,  // QF_UFNIRA
    true,  // QF_UFRDL
    true,  // QF_AUFBV
    true,  // QF_AUFBVLIA
    true,  // QF_AUFBVNIA
    true,  // QF_AUFLIA
    true,  // QF_AUFLRA
    true,  // QF_AUFLIRA
    true,  // QF_AUFNIA
    true,  // QF_AUFNRA
    true,  // QF_AUFNIRA
    false, // LOGIC_NONE
    true,  // LOGIC_ALL
    false, // LOGIC_UNKNOWN
};

bool logic_has_bitvectors[NUM_LOGICS] = {
    false, // AX
    true,  // BV
    false, // IDL
    false, // LIA
    false, // LRA
    false, // LIRA
    false, // NIA
    false, // NRA
    false, // NIRA
    false, // RDL
    false, // UF
    true,  // ABV
    false, // ALIA
    false, // ALRA
    false, // ALIRA
    false, // ANIA
    false, // ANRA
    false, // ANIRA
    false, // AUF
    true,  // UFBV
    true,  // UFBVLIA
    false, // UFIDL
    false, // UFLIA
    false, // UFLRA
    false, // UFLIRA
    false, // UFNIA
    false, // UFNRA
    false, // UFNIRA
    false, // UFRDL
    true,  // AUFBV
    true,  // AUFBVLIA
    true,  // AUFBVNIA
    false, // AUFLIA
    false, // AUFLRA
    false, // AUFLIRA
    false, // AUFNIA
    false, // AUFNRA
    false, // AUFNIRA
    false, // QF_AX
    true,  // QF_BV
    false, // QF_IDL
    false, // QF_LIA
    false, // QF_LRA
    false, // QF_LIRA
    false, // QF_NIA
    false, // QF_NRA
    false, // QF_NIRA
    false, // QF_RDL
    false, // QF_UF
    true,  // QF_ABV
    false, // QF_ALIA
    false, // QF_ALRA
    false, // QF_ALIRA
    false, // QF_ANIA
    false, // QF_ANRA
    false, // QF_ANIRA
    false, // QF_AUF
    true,  // QF_UFBV
    true,  // QF_UFBVLIA
    false, // QF_UFIDL
    false, // QF_UFLIA
    false, // QF_UFLRA
    false, // QF_UFLIRA
    false, // QF_UFNIA
    false, // QF_UFNRA
    false, // QF_UFNIRA
    false, // QF_UFRDL
    true,  // QF_AUFBV
    true,  // QF_AUFBVLIA
    true,  // QF_AUFBVNIA
    false, // QF_AUFLIA
    false, // QF_AUFLRA
    false, // QF_AUFLIRA
    false, // QF_AUFNIA
    false, // QF_AUFNRA
    false, // QF_AUFNIRA
    false, // LOGIC_NONE
    true,  // LOGIC_ALL
    false, // LOGIC_UNKNOWN
};

bool logic_is_linear_arith[NUM_LOGICS] = {
    false, // AX
    false, // BV
    false, // IDL
    true,  // LIA
    true,  // LRA
    true,  // LIRA
    false, // NIA
    false, // NRA
    false, // NIRA
    false, // RDL
    false, // UF
    false, // ABV
    true,  // ALIA
    true,  // ALRA
    true,  // ALIRA
    false, // ANIA
    false, // ANRA
    false, // ANIRA
    false, // AUF
    false, // UFBV
    true,  // UFBVLIA
    false, // UFIDL
    true,  // UFLIA
    true,  // UFLRA
    true,  // UFLIRA
    false, // UFNIA
    false, // UFNRA
    false, // UFNIRA
    false, // UFRDL
    false, // AUFBV
    true,  // AUFBVLIA
    false, // AUFBVNIA
    true,  // AUFLIA
    true,  // AUFLRA
    true,  // AUFLIRA
    false, // AUFNIA
    false, // AUFNRA
    false, // AUFNIRA
    false, // QF_AX
    false, // QF_BV
    false, // QF_IDL
    true,  // QF_LIA
    true,  // QF_LRA
    true,  // QF_LIRA
    false, // QF_NIA
    false, // QF_NRA
    false, // QF_NIRA
    false, // QF_RDL
    false, // QF_UF
    false, // QF_ABV
    true,  // QF_ALIA
    true,  // QF_ALRA
    true,  // QF_ALIRA
    false, // QF_ANIA
    false, // QF_ANRA
    false, // QF_ANIRA
    false, // QF_AUF
    false, // QF_UFBV
    true,  // QF_UFBVLIA
    false, // QF_UFIDL
    true,  // QF_UFLIA
    true,  // QF_UFLRA
    true,  // QF_UFLIRA
    false, // QF_UFNIA
    false, // QF_UFNRA
    false, // QF_UFNIRA
    false, // QF_UFRDL
    false, // QF_AUFBV
    true,  // QF_AUFBVLIA
    false, // QF_AUFBVNIA
    true,  // QF_AUFLIA
    true,  // QF_AUFLRA
    true,  // QF_AUFLIRA
    false, // QF_AUFNIA
    false, // QF_AUFNRA
    false, // QF_AUFNIRA
    false, // LOGIC_NONE
    false, // LOGIC_ALL
    false, // LOGIC_UNKNOWN
};

bool logic_is_difference_logic[NUM_LOGICS] = {
    false, // AX
    false, // BV
    true,  // IDL
    false, // LIA
    false, // LRA
    false, // LIRA
    false, // NIA
    false, // NRA
    false, // NIRA
    true,  // RDL
    false, // UF
    false, // ABV
    false, // ALIA
    false, // ALRA
    false, // ALIRA
    false, // ANIA
    false, // ANRA
    false, // ANIRA
    false, // AUF
    false, // UFBV
    false, // UFBVLIA
    true,  // UFIDL
    false, // UFLIA
    false, // UFLRA
    false, // UFLIRA
    false, // UFNIA
    false, // UFNRA
    false, // UFNIRA
    true,  // UFRDL
    false, // AUFBV
    false, // AUFBVLIA
    false, // AUFBVNIA
    false, // AUFLIA
    false, // AUFLRA
    false, // AUFLIRA
    false, // AUFNIA
    false, // AUFNRA
    false, // AUFNIRA
    false, // QF_AX
    false, // QF_BV
    true,  // QF_IDL
    false, // QF_LIA
    false, // QF_LRA
    false, // QF_LIRA
    false, // QF_NIA
    false, // QF_NRA
    false, // QF_NIRA
    true,  // QF_RDL
    false, // QF_UF
    false, // QF_ABV
    false, // QF_ALIA
    false, // QF_ALRA
    false, // QF_ALIRA
    false, // QF_ANIA
    false, // QF_ANRA
    false, // QF_ANIRA
    false, // QF_AUF
    false, // QF_UFBV
    false, // QF_UFBVLIA
    true,  // QF_UFIDL
    false, // QF_UFLIA
    false, // QF_UFLRA
    false, // QF_UFLIRA
    false, // QF_UFNIA
    false, // QF_UFNRA
    false, // QF_UFNIRA
    true,  // QF_UFRDL
    false, // QF_AUFBV
    false, // QF_AUFBVLIA
    false, // QF_AUFBVNIA
    false, // QF_AUFLIA
    false, // QF_AUFLRA
    false, // QF_AUFLIRA
    false, // QF_AUFNIA
    false, // QF_AUFNRA
    false, // QF_AUFNIRA
    false, // LOGIC_NONE
    false, // LOGIC_ALL
    false, // LOGIC_UNKNOWN
};

bool logic_has_ints[NUM_LOGICS] = {
    false, // AX
    false, // BV
    true,  // IDL
    true,  // LIA
    false, // LRA
    true,  // LIRA
    true,  // NIA
    false, // NRA
    true,  // NIRA
    false, // RDL
    false, // UF
    false, // ABV
    true,  // ALIA
    false, // ALRA
    true,  // ALIRA
    true,  // ANIA
    false, // ANRA
    true,  // ANIRA
    false, // AUF
    false, // UFBV
    true,  // UFBVLIA
    true,  // UFIDL
    true,  // UFLIA
    false, // UFLRA
    true,  // UFLIRA
    true,  // UFNIA
    false, // UFNRA
    true,  // UFNIRA
    false, // UFRDL
    false, // AUFBV
    true,  // AUFBVLIA
    true,  // AUFBVNIA
    true,  // AUFLIA
    false, // AUFLRA
    true,  // AUFLIRA
    true,  // AUFNIA
    false, // AUFNRA
    true,  // AUFNIRA
    false, // QF_AX
    false, // QF_BV
    true,  // QF_IDL
    true,  // QF_LIA
    false, // QF_LRA
    true,  // QF_LIRA
    true,  // QF_NIA
    false, // QF_NRA
    true,  // QF_NIRA
    false, // QF_RDL
    false, // QF_UF
    false, // QF_ABV
    true,  // QF_ALIA
    false, // QF_ALRA
    true,  // QF_ALIRA
    true,  // QF_ANIA
    false, // QF_ANRA
    true,  // QF_ANIRA
    false, // QF_AUF
    false, // QF_UFBV
    true,  // QF_UFBVLIA
    true,  // QF_UFIDL
    true,  // QF_UFLIA
    false, // QF_UFLRA
    true,  // QF_UFLIRA
    true,  // QF_UFNIA
    false, // QF_UFNRA
    true,  // QF_UFNIRA
    false, // QF_UFRDL
    false, // QF_AUFBV
    true,  // QF_AUFBVLIA
    true,  // QF_AUFBVNIA
    true,  // QF_AUFLIA
    false, // QF_AUFLRA
    true,  // QF_AUFLIRA
    true,  // QF_AUFNIA
    false, // QF_AUFNRA
    true,  // QF_AUFNIRA
    false, // LOGIC_NONE
    true,  // LOGIC_ALL
    false, // LOGIC_UNKNOWN
};

bool logic_has_reals[NUM_LOGICS] = {
    false, // AX
    false, // BV
    false, // IDL
    false, // LIA
    true,  // LRA
    true,  // LIRA
    false, // NIA
    true,  // NRA
    true,  // NIRA
    true,  // RDL
    false, // UF
    false, // ABV
    false, // ALIA
    true,  // ALRA
    true,  // ALIRA
    false, // ANIA
    true,  // ANRA
    true,  // ANIRA
    false, // AUF
    false, // UFBV
    false, // UFBVLIA
    false, // UFIDL
    false, // UFLIA
    true,  // UFLRA
    true,  // UFLIRA
    false, // UFNIA
    true,  // UFNRA
    true,  // UFNIRA
    true,  // UFRDL
    false, // AUFBV
    false, // AUFBVLIA
    false, // AUFBVNIA
    false, // AUFLIA
    true,  // AUFLRA
    true,  // AUFLIRA
    false, // AUFNIA
    true,  // AUFNRA
    true,  // AUFNIRA
    false, // QF_AX
    false, // QF_BV
    false, // QF_IDL
    false, // QF_LIA
    true,  // QF_LRA
    true,  // QF_LIRA
    false, // QF_NIA
    true,  // QF_NRA
    true,  // QF_NIRA
    true,  // QF_RDL
    false, // QF_UF
    false, // QF_ABV
    false, // QF_ALIA
    true,  // QF_ALRA
    true,  // QF_ALIRA
    false, // QF_ANIA
    true,  // QF_ANRA
    true,  // QF_ANIRA
    false, // QF_AUF
    false, // QF_UFBV
    false, // QF_UFBVLIA
    false, // QF_UFIDL
    false, // QF_UFLIA
    true,  // QF_UFLRA
    true,  // QF_UFLIRA
    false, // QF_UFNIA
    true,  // QF_UFNRA
    true,  // QF_UFNIRA
    true,  // QF_UFRDL
    false, // QF_AUFBV
    false, // QF_AUFBVLIA
    false, // QF_AUFBVNIA
    false, // QF_AUFLIA
    true,  // QF_AUFLRA
    true,  // QF_AUFLIRA
    false, // QF_AUFNIA
    true,  // QF_AUFNRA
    true,  // QF_AUFNIRA
    false, // LOGIC_NONE
    true,  // LOGIC_ALL
    false, // LOGIC_UNKNOWN
};

bool logic_has_quantifiers[NUM_LOGICS] = {
    true,  // AX
    true,  // BV
    true,  // IDL
    true,  // LIA
    true,  // LRA
    true,  // LIRA
    true,  // NIA
    true,  // NRA
    true,  // NIRA
    true,  // RDL
    true,  // UF
    true,  // ABV
    true,  // ALIA
    true,  // ALRA
    true,  // ALIRA
    true,  // ANIA
    true,  // ANRA
    true,  // ANIRA
    true,  // AUF
    true,  // UFBV
    true,  // UFBVLIA
    true,  // UFIDL
    true,  // UFLIA
    true,  // UFLRA
    true,  // UFLIRA
    true,  // UFNIA
    true,  // UFNRA
    true,  // UFNIRA
    true,  // UFRDL
    true,  // AUFBV
    true,  // AUFBVLIA
    true,  // AUFBVNIA
    true,  // AUFLIA
    true,  // AUFLRA
    true,  // AUFLIRA
    true,  // AUFNIA
    true,  // AUFNRA
    true,  // AUFNIRA
    false, // QF_AX
    false, // QF_BV
    false, // QF_IDL
    false, // QF_LIA
    false, // QF_LRA
    false, // QF_LIRA
    false, // QF_NIA
    false, // QF_NRA
    false, // QF_NIRA
    false, // QF_RDL
    false, // QF_UF
    false, // QF_ABV
    false, // QF_ALIA
    false, // QF_ALRA
    false, // QF_ALIRA
    false, // QF_ANIA
    false, // QF_ANRA
    false, // QF_ANIRA
    false, // QF_AUF
    false, // QF_UFBV
    false, // QF_UFBVLIA
    false, // QF_UFIDL
    false, // QF_UFLIA
    false, // QF_UFLRA
    false, // QF_UFLIRA
    false, // QF_UFNIA
    false, // QF_UFNRA
    false, // QF_UFNIRA
    false, // QF_UFRDL
    false, // QF_AUFBV
    false, // QF_AUFBVLIA
    false, // QF_AUFBVNIA
    false, // QF_AUFLIA
    false, // QF_AUFLRA
    false, // QF_AUFLIRA
    false, // QF_AUFNIA
    false, // QF_AUFNRA
    false, // QF_AUFNIRA
    false, // LOGIC_NONE
    true,  // LOGIC_ALL
    false, // LOGIC_UNKNOWN
};

bool logic_has_uf[NUM_LOGICS] = {
    false, // AX
    false, // BV
    false, // IDL
    false, // LIA
    false, // LRA
    false, // LIRA
    false, // NIA
    false, // NRA
    false, // NIRA
    false, // RDL
    true,  // UF
    false, // ABV
    false, // ALIA
    false, // ALRA
    false, // ALIRA
    false, // ANIA
    false, // ANRA
    false, // ANIRA
    true,  // AUF
    true,  // UFBV
    true,  // UFBVLIA
    true,  // UFIDL
    true,  // UFLIA
    true,  // UFLRA
    true,  // UFLIRA
    true,  // UFNIA
    true,  // UFNRA
    true,  // UFNIRA
    true,  // UFRDL
    true,  // AUFBV
    true,  // AUFBVLIA
    true,  // AUFBVNIA
    true,  // AUFLIA
    true,  // AUFLRA
    true,  // AUFLIRA
    true,  // AUFNIA
    true,  // AUFNRA
    true,  // AUFNIRA
    false, // QF_AX
    false, // QF_BV
    false, // QF_IDL
    false, // QF_LIA
    false, // QF_LRA
    false, // QF_LIRA
    false, // QF_NIA
    false, // QF_NRA
    false, // QF_NIRA
    false, // QF_RDL
    true,  // QF_UF
    false, // QF_ABV
    false, // QF_ALIA
    false, // QF_ALRA
    false, // QF_ALIRA
    false, // QF_ANIA
    false, // QF_ANRA
    false, // QF_ANIRA
    true,  // QF_AUF
    true,  // QF_UFBV
    true,  // QF_UFBVLIA
    true,  // QF_UFIDL
    true,  // QF_UFLIA
    true,  // QF_UFLRA
    true,  // QF_UFLIRA
    true,  // QF_UFNIA
    true,  // QF_UFNRA
    true,  // QF_UFNIRA
    true,  // QF_UFRDL
    true,  // QF_AUFBV
    true,  // QF_AUFBVLIA
    true,  // QF_AUFBVNIA
    true,  // QF_AUFLIA
    true,  // QF_AUFLRA
    true,  // QF_AUFLIRA
    true,  // QF_AUFNIA
    true,  // QF_AUFNRA
    true,  // QF_AUFNIRA
    false, // LOGIC_NONE
    true,  // LOGIC_ALL
    false, // LOGIC_UNKNOWN
};

