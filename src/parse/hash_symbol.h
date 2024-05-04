/* ANSI-C code produced by gperf version 3.1 */
/* Command-line: gperf -C -E -t --output-file=src/parse/hash_symbol.h --lookup-function-name=in_moxi_sym --hash-function=hash_sym src/parse/gperf/symbol.gperf  */
/* Computed positions: -k'1,3-5' */

#if !((' ' == 32) && ('!' == 33) && ('"' == 34) && ('#' == 35) \
      && ('%' == 37) && ('&' == 38) && ('\'' == 39) && ('(' == 40) \
      && (')' == 41) && ('*' == 42) && ('+' == 43) && (',' == 44) \
      && ('-' == 45) && ('.' == 46) && ('/' == 47) && ('0' == 48) \
      && ('1' == 49) && ('2' == 50) && ('3' == 51) && ('4' == 52) \
      && ('5' == 53) && ('6' == 54) && ('7' == 55) && ('8' == 56) \
      && ('9' == 57) && (':' == 58) && (';' == 59) && ('<' == 60) \
      && ('=' == 61) && ('>' == 62) && ('?' == 63) && ('A' == 65) \
      && ('B' == 66) && ('C' == 67) && ('D' == 68) && ('E' == 69) \
      && ('F' == 70) && ('G' == 71) && ('H' == 72) && ('I' == 73) \
      && ('J' == 74) && ('K' == 75) && ('L' == 76) && ('M' == 77) \
      && ('N' == 78) && ('O' == 79) && ('P' == 80) && ('Q' == 81) \
      && ('R' == 82) && ('S' == 83) && ('T' == 84) && ('U' == 85) \
      && ('V' == 86) && ('W' == 87) && ('X' == 88) && ('Y' == 89) \
      && ('Z' == 90) && ('[' == 91) && ('\\' == 92) && (']' == 93) \
      && ('^' == 94) && ('_' == 95) && ('a' == 97) && ('b' == 98) \
      && ('c' == 99) && ('d' == 100) && ('e' == 101) && ('f' == 102) \
      && ('g' == 103) && ('h' == 104) && ('i' == 105) && ('j' == 106) \
      && ('k' == 107) && ('l' == 108) && ('m' == 109) && ('n' == 110) \
      && ('o' == 111) && ('p' == 112) && ('q' == 113) && ('r' == 114) \
      && ('s' == 115) && ('t' == 116) && ('u' == 117) && ('v' == 118) \
      && ('w' == 119) && ('x' == 120) && ('y' == 121) && ('z' == 122) \
      && ('{' == 123) && ('|' == 124) && ('}' == 125) && ('~' == 126))
/* The character set is not based on ISO-646.  */
#error "gperf generated tables don't work with this execution character set. Please report a bug to <bug-gperf@gnu.org>."
#endif

#line 1 "src/parse/gperf/symbol.gperf"

#include <string.h>
#include "token.h"
#line 5 "src/parse/gperf/symbol.gperf"
struct token_t;
/* maximum key range = 116, duplicates = 0 */

#ifdef __GNUC__
__inline
#else
#ifdef __cplusplus
inline
#endif
#endif
static unsigned int
hash_sym (register const char *str, register size_t len)
{
  static const unsigned char asso_values[] =
    {
      117, 117, 117, 117, 117, 117, 117, 117, 117, 117,
      117, 117, 117, 117, 117, 117, 117, 117, 117, 117,
      117, 117, 117, 117, 117, 117, 117, 117, 117, 117,
      117, 117, 117, 117, 117, 117, 117, 117, 117, 117,
      117, 117, 115, 110, 117, 105, 117,   0, 117, 117,
      117, 117, 117, 117, 117, 117, 117, 117, 117, 117,
       55,  35,  25, 117, 117,  10,   0, 117, 117, 117,
      117, 117, 117,  30, 117, 117, 117, 117, 117, 117,
      117, 117,   5, 117, 117, 117,  90, 117, 117, 117,
      117, 117, 117, 117, 117,   0, 117,   0,   0,   5,
       10,   0,  25,  35,  20,  20, 117, 117,  45,  35,
        0,   0,  85, 117,   0,  25,   5,   5,  20, 117,
       80,   5,  65, 117, 117, 117, 117, 117, 117, 117,
      117, 117, 117, 117, 117, 117, 117, 117, 117, 117,
      117, 117, 117, 117, 117, 117, 117, 117, 117, 117,
      117, 117, 117, 117, 117, 117, 117, 117, 117, 117,
      117, 117, 117, 117, 117, 117, 117, 117, 117, 117,
      117, 117, 117, 117, 117, 117, 117, 117, 117, 117,
      117, 117, 117, 117, 117, 117, 117, 117, 117, 117,
      117, 117, 117, 117, 117, 117, 117, 117, 117, 117,
      117, 117, 117, 117, 117, 117, 117, 117, 117, 117,
      117, 117, 117, 117, 117, 117, 117, 117, 117, 117,
      117, 117, 117, 117, 117, 117, 117, 117, 117, 117,
      117, 117, 117, 117, 117, 117, 117, 117, 117, 117,
      117, 117, 117, 117, 117, 117, 117, 117, 117, 117,
      117, 117, 117, 117, 117, 117
    };
  register unsigned int hval = len;

  switch (hval)
    {
      default:
        hval += asso_values[(unsigned char)str[4]];
      /*FALLTHROUGH*/
      case 4:
        hval += asso_values[(unsigned char)str[3]];
      /*FALLTHROUGH*/
      case 3:
        hval += asso_values[(unsigned char)str[2]];
      /*FALLTHROUGH*/
      case 2:
      case 1:
        hval += asso_values[(unsigned char)str[0]];
        break;
    }
  return hval;
}

const struct token_t *
in_moxi_sym (register const char *str, register size_t len)
{
  enum
    {
      TOTAL_KEYWORDS = 65,
      MIN_WORD_LENGTH = 1,
      MAX_WORD_LENGTH = 12,
      MIN_HASH_VALUE = 1,
      MAX_HASH_VALUE = 116
    };

  static const struct token_t wordlist[] =
    {
      {""},
#line 26 "src/parse/gperf/symbol.gperf"
      {"/",                 MOXI_TOK_SYM_DIVIDES},
#line 13 "src/parse/gperf/symbol.gperf"
      {"or",                MOXI_TOK_SYM_OR},
      {""},
#line 43 "src/parse/gperf/symbol.gperf"
      {"bvor",              MOXI_TOK_SYM_BVOR},
#line 45 "src/parse/gperf/symbol.gperf"
      {"bvnor",             MOXI_TOK_SYM_BVNOR},
#line 44 "src/parse/gperf/symbol.gperf"
      {"bvnand",            MOXI_TOK_SYM_BVNAND},
      {""},
#line 10 "src/parse/gperf/symbol.gperf"
      {"not",               MOXI_TOK_SYM_NOT},
      {""},
#line 41 "src/parse/gperf/symbol.gperf"
      {"bvnot",             MOXI_TOK_SYM_BVNOT},
#line 53 "src/parse/gperf/symbol.gperf"
      {"bvurem",            MOXI_TOK_SYM_BVUREM},
#line 36 "src/parse/gperf/symbol.gperf"
      {"extract",           MOXI_TOK_SYM_EXTRACT},
#line 12 "src/parse/gperf/symbol.gperf"
      {"and",               MOXI_TOK_SYM_AND},
#line 8 "src/parse/gperf/symbol.gperf"
      {"true",              MOXI_TOK_SYM_TRUE},
#line 42 "src/parse/gperf/symbol.gperf"
      {"bvand",             MOXI_TOK_SYM_BVAND},
#line 35 "src/parse/gperf/symbol.gperf"
      {"concat",            MOXI_TOK_SYM_CONCAT},
#line 40 "src/parse/gperf/symbol.gperf"
      {"bvredor",           MOXI_TOK_SYM_BVREDOR},
#line 39 "src/parse/gperf/symbol.gperf"
      {"bvredand",          MOXI_TOK_SYM_BVREDAND},
      {""},
#line 18 "src/parse/gperf/symbol.gperf"
      {"Array",             MOXI_TOK_SYM_ARRAY},
#line 62 "src/parse/gperf/symbol.gperf"
      {"rotate_left",       MOXI_TOK_SYM_ROTATE_LEFT},
#line 63 "src/parse/gperf/symbol.gperf"
      {"rotate_right",      MOXI_TOK_SYM_ROTATE_RIGHT},
#line 17 "src/parse/gperf/symbol.gperf"
      {"ite",               MOXI_TOK_SYM_ITE},
      {""},
#line 49 "src/parse/gperf/symbol.gperf"
      {"bvadd",             MOXI_TOK_SYM_BVADD},
#line 30 "src/parse/gperf/symbol.gperf"
      {">",                 MOXI_TOK_SYM_GT},
#line 29 "src/parse/gperf/symbol.gperf"
      {">=",                MOXI_TOK_SYM_GE},
#line 33 "src/parse/gperf/symbol.gperf"
      {"abs",               MOXI_TOK_SYM_ABS},
      {""},
#line 20 "src/parse/gperf/symbol.gperf"
      {"store",             MOXI_TOK_SYM_STORE},
#line 55 "src/parse/gperf/symbol.gperf"
      {"bvsrem",            MOXI_TOK_SYM_BVSREM},
      {""},
#line 31 "src/parse/gperf/symbol.gperf"
      {"div",               MOXI_TOK_SYM_DIV},
      {""},
#line 50 "src/parse/gperf/symbol.gperf"
      {"bvsub",             MOXI_TOK_SYM_BVSUB},
#line 15 "src/parse/gperf/symbol.gperf"
      {"=",                 MOXI_TOK_SYM_EQ},
#line 11 "src/parse/gperf/symbol.gperf"
      {"=>",                MOXI_TOK_SYM_IMPLIES},
#line 21 "src/parse/gperf/symbol.gperf"
      {"Int",               MOXI_TOK_SYM_INT},
      {""},
#line 48 "src/parse/gperf/symbol.gperf"
      {"bvneg",             MOXI_TOK_SYM_BVNEG},
#line 52 "src/parse/gperf/symbol.gperf"
      {"bvudiv",            MOXI_TOK_SYM_BVUDIV},
      {""}, {""}, {""},
#line 67 "src/parse/gperf/symbol.gperf"
      {"bvuge",             MOXI_TOK_SYM_BVUGE},
#line 38 "src/parse/gperf/symbol.gperf"
      {"bvcomp",            MOXI_TOK_SYM_BVCOMP},
      {""},
#line 32 "src/parse/gperf/symbol.gperf"
      {"mod",               MOXI_TOK_SYM_MOD},
#line 7 "src/parse/gperf/symbol.gperf"
      {"Bool",              MOXI_TOK_SYM_BOOL},
#line 66 "src/parse/gperf/symbol.gperf"
      {"bvugt",             MOXI_TOK_SYM_BVUGT},
#line 59 "src/parse/gperf/symbol.gperf"
      {"bvashr",            MOXI_TOK_SYM_BVASHR},
      {""}, {""},
#line 22 "src/parse/gperf/symbol.gperf"
      {"Real",              MOXI_TOK_SYM_REAL},
#line 65 "src/parse/gperf/symbol.gperf"
      {"bvule",             MOXI_TOK_SYM_BVULE},
#line 28 "src/parse/gperf/symbol.gperf"
      {"<",                 MOXI_TOK_SYM_LT},
#line 27 "src/parse/gperf/symbol.gperf"
      {"<=",                MOXI_TOK_SYM_LE},
      {""}, {""},
#line 64 "src/parse/gperf/symbol.gperf"
      {"bvult",             MOXI_TOK_SYM_BVULT},
#line 54 "src/parse/gperf/symbol.gperf"
      {"bvsdiv",            MOXI_TOK_SYM_BVSDIV},
      {""}, {""}, {""},
#line 71 "src/parse/gperf/symbol.gperf"
      {"bvsge",             MOXI_TOK_SYM_BVSGE},
#line 56 "src/parse/gperf/symbol.gperf"
      {"bvsmod",            MOXI_TOK_SYM_BVSMOD},
      {""},
#line 16 "src/parse/gperf/symbol.gperf"
      {"distinct",          MOXI_TOK_SYM_DISTINCT},
      {""},
#line 70 "src/parse/gperf/symbol.gperf"
      {"bvsgt",             MOXI_TOK_SYM_BVSGT},
#line 61 "src/parse/gperf/symbol.gperf"
      {"sign_extend",       MOXI_TOK_SYM_SIGN_EXTEND},
      {""}, {""}, {""},
#line 69 "src/parse/gperf/symbol.gperf"
      {"bvsle",             MOXI_TOK_SYM_BVSLE},
#line 60 "src/parse/gperf/symbol.gperf"
      {"zero_extend",       MOXI_TOK_SYM_ZERO_EXTEND},
      {""}, {""}, {""},
#line 68 "src/parse/gperf/symbol.gperf"
      {"bvslt",             MOXI_TOK_SYM_BVSLT},
#line 19 "src/parse/gperf/symbol.gperf"
      {"select",            MOXI_TOK_SYM_SELECT},
      {""},
#line 14 "src/parse/gperf/symbol.gperf"
      {"xor",               MOXI_TOK_SYM_XOR},
      {""},
#line 46 "src/parse/gperf/symbol.gperf"
      {"bvxor",             MOXI_TOK_SYM_BVXOR},
#line 47 "src/parse/gperf/symbol.gperf"
      {"bvxnor",            MOXI_TOK_SYM_BVXNOR},
      {""}, {""}, {""},
#line 51 "src/parse/gperf/symbol.gperf"
      {"bvmul",             MOXI_TOK_SYM_BVMUL},
#line 37 "src/parse/gperf/symbol.gperf"
      {"repeat",            MOXI_TOK_SYM_REPEAT},
      {""}, {""}, {""},
#line 57 "src/parse/gperf/symbol.gperf"
      {"bvshl",             MOXI_TOK_SYM_BVSHL},
#line 58 "src/parse/gperf/symbol.gperf"
      {"bvlshr",            MOXI_TOK_SYM_BVLSHR},
      {""}, {""}, {""},
#line 9 "src/parse/gperf/symbol.gperf"
      {"false",             MOXI_TOK_SYM_FALSE},
#line 34 "src/parse/gperf/symbol.gperf"
      {"BitVec",            MOXI_TOK_SYM_BITVEC},
      {""}, {""}, {""}, {""},
#line 23 "src/parse/gperf/symbol.gperf"
      {"-",                 MOXI_TOK_SYM_MINUS},
      {""}, {""}, {""}, {""},
#line 24 "src/parse/gperf/symbol.gperf"
      {"+",                 MOXI_TOK_SYM_PLUS},
      {""}, {""}, {""}, {""},
#line 25 "src/parse/gperf/symbol.gperf"
      {"*",                 MOXI_TOK_SYM_TIMES}
    };

  if (len <= MAX_WORD_LENGTH && len >= MIN_WORD_LENGTH)
    {
      register unsigned int key = hash_sym (str, len);

      if (key <= MAX_HASH_VALUE)
        {
          register const char *s = wordlist[key].name;

          if (*str == *s && !strcmp (str + 1, s + 1))
            return &wordlist[key];
        }
    }
  return 0;
}
