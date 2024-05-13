/**
 * 
*/
#ifndef __LOGICS_H__
#define __LOGICS_H__

#include "moxi/context.h"

typedef enum logic {
  /*
   * Base logics (with quantifiers)
   */
  LOGIC_AX,          // arrays
  LOGIC_BV,          // bitvectors
  LOGIC_IDL,         // integer difference logic
  LOGIC_LIA,         // linear integer arithmetic
  LOGIC_LRA,         // linear real arithmetic
  LOGIC_LIRA,        // mixed linear arithmetic
  LOGIC_NIA,         // non-linear integer arithmetic
  LOGIC_NRA,         // non-linear real arithmetic
  LOGIC_NIRA,        // non-linear mixed arithmetic
  LOGIC_RDL,         // real difference logic
  LOGIC_UF,          // uninterpreted functions

  //  Arrays + some other theory
  LOGIC_ABV,         // arrays + bitvectors
  LOGIC_ALIA,        // arrays + linear integer arithmetic
  LOGIC_ALRA,        // arrays + linear real arithmetic
  LOGIC_ALIRA,       // arrays + mixed linear arithmetic
  LOGIC_ANIA,        // arrays + non-linear integer arithmetic
  LOGIC_ANRA,        // arrays + non-linear real arithmetic
  LOGIC_ANIRA,       // arrays + mixed/non-linear arithmetic
  LOGIC_AUF,         // arrays + uninterpreted functions

  //  Uninterpreted function + another theory
  LOGIC_UFBV,        // uninterpreted functions + bitvectors
  LOGIC_UFBVLIA,     // uninterpreted functions + bitvectors + linear integer arithmetic
  LOGIC_UFIDL,       // uninterpreted functions + integer difference logic
  LOGIC_UFLIA,       // uninterpreted functions + linear integer arithmetic
  LOGIC_UFLRA,       // uninterpreted functions + linear real arithmetic
  LOGIC_UFLIRA,      // uninterpreted functions + mixed linear arithmetic
  LOGIC_UFNIA,       // uninterpreted functions + non-linear integer arithmetic
  LOGIC_UFNRA,       // uninterpreted functions + non-linear real arithmetic
  LOGIC_UFNIRA,      // uninterpreted functions + mixed, non-linear arithmetic
  LOGIC_UFRDL,       // uninterpreted functions + real difference logic

  //  Arrays + uninterpreted functions + another theory
  LOGIC_AUFBV,       // arrays + uninterpreted functions + bitvectors
  LOGIC_AUFBVLIA,    // arrays + uninterpreted functions + bitvectors + linear integer arithmetic
  LOGIC_AUFBVNIA,    // arrays + uninterpreted functions + bitvectors + nonlinear integer arithmetic
  LOGIC_AUFLIA,      // arrays + uninterpreted functions + linear integer arithmetic
  LOGIC_AUFLRA,      // arrays + uninterpreted functions + linear real arithmetic
  LOGIC_AUFLIRA,     // arrays + uninterpreted functions + mixed linear arithmetic
  LOGIC_AUFNIA,      // arrays + uninterpreted functions + non-linear integer arithmetic
  LOGIC_AUFNRA,      // arrays + uninterpreted functions + non-linear real arithmetic
  LOGIC_AUFNIRA,     // arrays + uninterpreted functions + mixed, non-linear arithmetic

  /*
   * Quantifier-free fragments
   */
  LOGIC_QF_AX,       // arrays
  LOGIC_QF_BV,       // bitvectors
  LOGIC_QF_IDL,      // integer difference logic
  LOGIC_QF_LIA,      // linear integer arithmetic
  LOGIC_QF_LRA,      // linear real arithmetic
  LOGIC_QF_LIRA,     // mixed linear arithmetic
  LOGIC_QF_NIA,      // non-linear integer arithmetic
  LOGIC_QF_NRA,      // non-linear real arithmetic
  LOGIC_QF_NIRA,     // non-linear mixed arithmetic
  LOGIC_QF_RDL,      // real difference logic
  LOGIC_QF_UF,       // uninterpreted functions

  //  Arrays + some other theory
  LOGIC_QF_ABV,      // arrays + bitvectors
  LOGIC_QF_ALIA,     // arrays + linear integer arithmetic
  LOGIC_QF_ALRA,     // arrays + linear real arithmetic
  LOGIC_QF_ALIRA,    // arrays + mixed linear arithmetic
  LOGIC_QF_ANIA,     // arrays + non-linear integer arithmetic
  LOGIC_QF_ANRA,     // arrays + non-linear real arithmetic
  LOGIC_QF_ANIRA,    // arrays + mixed/non-linear arithmetic
  LOGIC_QF_AUF,      // arrays + uninterpreted functions

  //  Uninterpreted function + another theory
  LOGIC_QF_UFBV,     // uninterpreted functions + bitvectors
  LOGIC_QF_UFBVLIA,  // uninterpreted functions + bitvectors + linear integer arithmetic
  LOGIC_QF_UFIDL,    // uninterpreted functions + integer difference logic
  LOGIC_QF_UFLIA,    // uninterpreted functions + linear integer arithmetic
  LOGIC_QF_UFLRA,    // uninterpreted functions + linear real arithmetic
  LOGIC_QF_UFLIRA,   // uninterpreted functions + mixed linear arithmetic
  LOGIC_QF_UFNIA,    // uninterpreted functions + non-linear integer arithmetic
  LOGIC_QF_UFNRA,    // uninterpreted functions + non-linear real arithmetic
  LOGIC_QF_UFNIRA,   // uninterpreted functions + mixed, non-linear arithmetic
  LOGIC_QF_UFRDL,    // uninterpreted functions + real difference logic

  //  Arrays + uninterpreted functions + another theory
  LOGIC_QF_AUFBV,    // arrays + uninterpreted functions + bitvectors
  LOGIC_QF_AUFBVLIA, // arrays + uninterpreted functions + bitvectors + linear integer arithmetic
  LOGIC_QF_AUFBVNIA, // arrays + uninterpreted functions + bitvectors + nonlinear integer arithmetic
  LOGIC_QF_AUFLIA,   // arrays + uninterpreted functions + linear integer arithmetic
  LOGIC_QF_AUFLRA,   // arrays + uninterpreted functions + linear real arithmetic
  LOGIC_QF_AUFLIRA,  // arrays + uninterpreted functions + mixed linear arithmetic
  LOGIC_QF_AUFNIA,   // arrays + uninterpreted functions + non-linear integer arithmetic
  LOGIC_QF_AUFNRA,   // arrays + uninterpreted functions + non-linear real arithmetic
  LOGIC_QF_AUFNIRA,  // arrays + uninterpreted functions + mixed, non-linear arithmetic
  
  LOGIC_NONE,
  LOGIC_ALL,
  LOGIC_UNKNOWN,
} logic_t;


void set_current_logic(context_t *context, logic_t logic);


#endif