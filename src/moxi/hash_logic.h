/* ANSI-C code produced by gperf version 3.1 */
/* Command-line: gperf -C -E -t --output-file=src/moxi/hash_logic.h --lookup-function-name=in_moxi_logic --hash-function=hash_logic src/moxi/logic.gperf  */
/* Computed positions: -k'1-9' */

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

#line 1 "src/moxi/logic.gperf"

#include <string.h>
#include "context.h"
#line 5 "src/moxi/logic.gperf"
struct logic;
/* maximum key range = 222, duplicates = 0 */

#ifdef __GNUC__
__inline
#else
#ifdef __cplusplus
inline
#endif
#endif
static unsigned int
hash_logic (register const char *str, register size_t len)
{
  static const unsigned char asso_values[] =
    {
      224, 224, 224, 224, 224, 224, 224, 224, 224, 224,
      224, 224, 224, 224, 224, 224, 224, 224, 224, 224,
      224, 224, 224, 224, 224, 224, 224, 224, 224, 224,
      224, 224, 224, 224, 224, 224, 224, 224, 224, 224,
      224, 224, 224, 224, 224, 224, 224, 224, 224, 224,
      224, 224, 224, 224, 224, 224, 224, 224, 224, 224,
      224, 224, 224, 224, 224,  10,  75, 224, 115, 224,
        0, 224, 224,  35, 224, 224,  15, 224,   0, 224,
      224,   0,  65, 224, 224,   0,  70, 224,   0, 224,
      224, 224, 224, 224, 224,   0, 224, 224, 224, 224,
      224, 224, 224, 224, 224, 224, 224, 224, 224, 224,
      224, 224, 224, 224, 224, 224, 224, 224, 224, 224,
      224, 224, 224, 224, 224, 224, 224, 224, 224, 224,
      224, 224, 224, 224, 224, 224, 224, 224, 224, 224,
      224, 224, 224, 224, 224, 224, 224, 224, 224, 224,
      224, 224, 224, 224, 224, 224, 224, 224, 224, 224,
      224, 224, 224, 224, 224, 224, 224, 224, 224, 224,
      224, 224, 224, 224, 224, 224, 224, 224, 224, 224,
      224, 224, 224, 224, 224, 224, 224, 224, 224, 224,
      224, 224, 224, 224, 224, 224, 224, 224, 224, 224,
      224, 224, 224, 224, 224, 224, 224, 224, 224, 224,
      224, 224, 224, 224, 224, 224, 224, 224, 224, 224,
      224, 224, 224, 224, 224, 224, 224, 224, 224, 224,
      224, 224, 224, 224, 224, 224, 224, 224, 224, 224,
      224, 224, 224, 224, 224, 224, 224, 224, 224, 224,
      224, 224, 224, 224, 224, 224
    };
  register unsigned int hval = len;

  switch (hval)
    {
      default:
        hval += asso_values[(unsigned char)str[8]];
      /*FALLTHROUGH*/
      case 8:
        hval += asso_values[(unsigned char)str[7]];
      /*FALLTHROUGH*/
      case 7:
        hval += asso_values[(unsigned char)str[6]];
      /*FALLTHROUGH*/
      case 6:
        hval += asso_values[(unsigned char)str[5]];
      /*FALLTHROUGH*/
      case 5:
        hval += asso_values[(unsigned char)str[4]];
      /*FALLTHROUGH*/
      case 4:
        hval += asso_values[(unsigned char)str[3]];
      /*FALLTHROUGH*/
      case 3:
        hval += asso_values[(unsigned char)str[2]];
      /*FALLTHROUGH*/
      case 2:
        hval += asso_values[(unsigned char)str[1]];
      /*FALLTHROUGH*/
      case 1:
        hval += asso_values[(unsigned char)str[0]];
        break;
    }
  return hval;
}

const struct logic *
in_moxi_logic (register const char *str, register size_t len)
{
  enum
    {
      TOTAL_KEYWORDS = 76,
      MIN_WORD_LENGTH = 2,
      MAX_WORD_LENGTH = 11,
      MIN_HASH_VALUE = 2,
      MAX_HASH_VALUE = 223
    };

  static const struct logic wordlist[] =
    {
      {""}, {""},
#line 17 "src/moxi/logic.gperf"
      {"UF",             UF},
      {""}, {""},
#line 55 "src/moxi/logic.gperf"
      {"QF_UF",          QF_UF},
      {""}, {""}, {""}, {""}, {""}, {""},
#line 7 "src/moxi/logic.gperf"
      {"AX",             AX},
#line 25 "src/moxi/logic.gperf"
      {"AUF",            AUF},
      {""},
#line 45 "src/moxi/logic.gperf"
      {"QF_AX",          QF_AX},
#line 63 "src/moxi/logic.gperf"
      {"QF_AUF",         QF_AUF},
      {""}, {""}, {""}, {""}, {""}, {""}, {""}, {""}, {""},
      {""}, {""}, {""}, {""}, {""}, {""}, {""}, {""}, {""},
      {""}, {""}, {""}, {""}, {""}, {""}, {""}, {""}, {""},
      {""}, {""}, {""}, {""},
#line 13 "src/moxi/logic.gperf"
      {"NIA",            NIA},
      {""},
#line 32 "src/moxi/logic.gperf"
      {"UFNIA",          UFNIA},
#line 51 "src/moxi/logic.gperf"
      {"QF_NIA",         QF_NIA},
      {""},
#line 70 "src/moxi/logic.gperf"
      {"QF_UFNIA",       QF_UFNIA},
      {""}, {""}, {""}, {""}, {""},
#line 22 "src/moxi/logic.gperf"
      {"ANIA",           ANIA},
      {""},
#line 42 "src/moxi/logic.gperf"
      {"AUFNIA",         AUFNIA},
#line 60 "src/moxi/logic.gperf"
      {"QF_ANIA",        QF_ANIA},
#line 10 "src/moxi/logic.gperf"
      {"LIA",            LIA},
#line 80 "src/moxi/logic.gperf"
      {"QF_AUFNIA",      QF_AUFNIA},
#line 29 "src/moxi/logic.gperf"
      {"UFLIA",          UFLIA},
#line 48 "src/moxi/logic.gperf"
      {"QF_LIA",         QF_LIA},
      {""},
#line 67 "src/moxi/logic.gperf"
      {"QF_UFLIA",       QF_UFLIA},
      {""}, {""}, {""}, {""}, {""},
#line 19 "src/moxi/logic.gperf"
      {"ALIA",           ALIA},
      {""},
#line 39 "src/moxi/logic.gperf"
      {"AUFLIA",         AUFLIA},
#line 57 "src/moxi/logic.gperf"
      {"QF_ALIA",        QF_ALIA},
#line 14 "src/moxi/logic.gperf"
      {"NRA",            NRA},
#line 77 "src/moxi/logic.gperf"
      {"QF_AUFLIA",      QF_AUFLIA},
#line 33 "src/moxi/logic.gperf"
      {"UFNRA",          UFNRA},
#line 52 "src/moxi/logic.gperf"
      {"QF_NRA",         QF_NRA},
      {""},
#line 71 "src/moxi/logic.gperf"
      {"QF_UFNRA",       QF_UFNRA},
      {""}, {""}, {""}, {""}, {""},
#line 23 "src/moxi/logic.gperf"
      {"ANRA",           ANRA},
      {""},
#line 43 "src/moxi/logic.gperf"
      {"AUFNRA",         AUFNRA},
#line 61 "src/moxi/logic.gperf"
      {"QF_ANRA",        QF_ANRA},
#line 11 "src/moxi/logic.gperf"
      {"LRA",            LRA},
#line 81 "src/moxi/logic.gperf"
      {"QF_AUFNRA",      QF_AUFNRA},
#line 30 "src/moxi/logic.gperf"
      {"UFLRA",          UFLRA},
#line 49 "src/moxi/logic.gperf"
      {"QF_LRA",         QF_LRA},
      {""},
#line 68 "src/moxi/logic.gperf"
      {"QF_UFLRA",       QF_UFLRA},
      {""}, {""}, {""}, {""}, {""},
#line 20 "src/moxi/logic.gperf"
      {"ALRA",           ALRA},
      {""},
#line 40 "src/moxi/logic.gperf"
      {"AUFLRA",         AUFLRA},
#line 58 "src/moxi/logic.gperf"
      {"QF_ALRA",        QF_ALRA},
      {""},
#line 78 "src/moxi/logic.gperf"
      {"QF_AUFLRA",      QF_AUFLRA},
      {""}, {""}, {""}, {""},
#line 15 "src/moxi/logic.gperf"
      {"NIRA",           NIRA},
      {""},
#line 34 "src/moxi/logic.gperf"
      {"UFNIRA",         UFNIRA},
#line 53 "src/moxi/logic.gperf"
      {"QF_NIRA",        QF_NIRA},
      {""},
#line 72 "src/moxi/logic.gperf"
      {"QF_UFNIRA",      QF_UFNIRA},
#line 82 "src/moxi/logic.gperf"
      {"QF_AUFNIRA",     QF_AUFNIRA},
      {""}, {""}, {""}, {""},
#line 24 "src/moxi/logic.gperf"
      {"ANIRA",          ANIRA},
      {""},
#line 44 "src/moxi/logic.gperf"
      {"AUFNIRA",        AUFNIRA},
#line 62 "src/moxi/logic.gperf"
      {"QF_ANIRA",       QF_ANIRA},
#line 12 "src/moxi/logic.gperf"
      {"LIRA",           LIRA},
      {""},
#line 31 "src/moxi/logic.gperf"
      {"UFLIRA",         UFLIRA},
#line 50 "src/moxi/logic.gperf"
      {"QF_LIRA",        QF_LIRA},
      {""},
#line 69 "src/moxi/logic.gperf"
      {"QF_UFLIRA",      QF_UFLIRA},
#line 79 "src/moxi/logic.gperf"
      {"QF_AUFLIRA",     QF_AUFLIRA},
      {""}, {""}, {""}, {""},
#line 21 "src/moxi/logic.gperf"
      {"ALIRA",          ALIRA},
      {""},
#line 41 "src/moxi/logic.gperf"
      {"AUFLIRA",        AUFLIRA},
#line 59 "src/moxi/logic.gperf"
      {"QF_ALIRA",       QF_ALIRA},
      {""}, {""}, {""},
#line 8 "src/moxi/logic.gperf"
      {"BV",             BV},
      {""},
#line 26 "src/moxi/logic.gperf"
      {"UFBV",           UFBV},
#line 46 "src/moxi/logic.gperf"
      {"QF_BV",          QF_BV},
      {""},
#line 64 "src/moxi/logic.gperf"
      {"QF_UFBV",        QF_UFBV},
      {""}, {""}, {""}, {""}, {""},
#line 18 "src/moxi/logic.gperf"
      {"ABV",            ABV},
      {""},
#line 36 "src/moxi/logic.gperf"
      {"AUFBV",          AUFBV},
#line 56 "src/moxi/logic.gperf"
      {"QF_ABV",         QF_ABV},
      {""},
#line 74 "src/moxi/logic.gperf"
      {"QF_AUFBV",       QF_AUFBV},
      {""}, {""},
#line 76 "src/moxi/logic.gperf"
      {"QF_AUFBVNIA",    QF_AUFBVNIA},
      {""},
#line 9 "src/moxi/logic.gperf"
      {"IDL",            IDL},
      {""},
#line 28 "src/moxi/logic.gperf"
      {"UFIDL",          UFIDL},
#line 47 "src/moxi/logic.gperf"
      {"QF_IDL",         QF_IDL},
      {""},
#line 66 "src/moxi/logic.gperf"
      {"QF_UFIDL",       QF_UFIDL},
      {""}, {""}, {""}, {""}, {""}, {""}, {""},
#line 75 "src/moxi/logic.gperf"
      {"QF_AUFBVLIA",    QF_AUFBVLIA},
      {""}, {""}, {""}, {""}, {""}, {""}, {""}, {""}, {""},
      {""}, {""}, {""}, {""}, {""}, {""}, {""},
#line 16 "src/moxi/logic.gperf"
      {"RDL",            RDL},
      {""},
#line 35 "src/moxi/logic.gperf"
      {"UFRDL",          UFRDL},
#line 54 "src/moxi/logic.gperf"
      {"QF_RDL",         QF_RDL},
      {""},
#line 73 "src/moxi/logic.gperf"
      {"QF_UFRDL",       QF_UFRDL},
      {""},
#line 65 "src/moxi/logic.gperf"
      {"QF_UFBVLIA",     QF_UFBVLIA},
      {""}, {""},
#line 38 "src/moxi/logic.gperf"
      {"AUFBVNIA",       AUFBVNIA},
      {""}, {""}, {""},
#line 27 "src/moxi/logic.gperf"
      {"UFBVLIA",        UFBVLIA},
      {""}, {""}, {""}, {""}, {""}, {""}, {""}, {""}, {""},
      {""},
#line 37 "src/moxi/logic.gperf"
      {"AUFBVLIA",       AUFBVLIA}
    };

  if (len <= MAX_WORD_LENGTH && len >= MIN_WORD_LENGTH)
    {
      register unsigned int key = hash_logic (str, len);

      if (key <= MAX_HASH_VALUE)
        {
          register const char *s = wordlist[key].name;

          if (*str == *s && !strcmp (str + 1, s + 1))
            return &wordlist[key];
        }
    }
  return 0;
}
