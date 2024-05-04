/* ANSI-C code produced by gperf version 3.1 */
/* Command-line: gperf -C -E -t --output-file=src/parse/hash_reserved.h --lookup-function-name=in_moxi_rw --hash-function=hash_rw src/parse/gperf/reserved.gperf  */
/* Computed positions: -k'1,3' */

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

#line 1 "src/parse/gperf/reserved.gperf"

#include <string.h>
#include "token.h"
#line 5 "src/parse/gperf/reserved.gperf"
struct token_t;
/* maximum key range = 32, duplicates = 0 */

#ifdef __GNUC__
__inline
#else
#ifdef __cplusplus
inline
#endif
#endif
static unsigned int
hash_rw (register const char *str, register size_t len)
{
  static const unsigned char asso_values[] =
    {
      33, 33, 33, 33, 33, 33, 33, 33, 33, 33,
      33, 33, 33, 33, 33, 33, 33, 33, 33, 33,
      33, 33, 33, 33, 33, 33, 33, 33, 33, 33,
      33, 33, 33, 18, 33, 33, 33, 33, 33, 33,
      33, 33, 33, 33, 33, 33, 33, 33, 33, 33,
      33, 33, 33, 33, 33, 33, 33, 33, 33, 33,
      33, 33, 33, 33, 33, 33, 33,  5,  0, 33,
      33, 33, 33, 33, 33, 33, 33,  0,  0, 33,
      33, 33, 15, 10, 33, 33, 33, 33, 33, 33,
      33, 33, 33, 33, 33,  0, 33,  0, 33,  5,
      10,  0,  0, 33,  5,  0, 33, 33,  0, 33,
      33, 33,  0, 33, 10,  5,  0, 33, 33, 33,
      33, 33, 33, 33, 33, 33, 33, 33, 33, 33,
      33, 33, 33, 33, 33, 33, 33, 33, 33, 33,
      33, 33, 33, 33, 33, 33, 33, 33, 33, 33,
      33, 33, 33, 33, 33, 33, 33, 33, 33, 33,
      33, 33, 33, 33, 33, 33, 33, 33, 33, 33,
      33, 33, 33, 33, 33, 33, 33, 33, 33, 33,
      33, 33, 33, 33, 33, 33, 33, 33, 33, 33,
      33, 33, 33, 33, 33, 33, 33, 33, 33, 33,
      33, 33, 33, 33, 33, 33, 33, 33, 33, 33,
      33, 33, 33, 33, 33, 33, 33, 33, 33, 33,
      33, 33, 33, 33, 33, 33, 33, 33, 33, 33,
      33, 33, 33, 33, 33, 33, 33, 33, 33, 33,
      33, 33, 33, 33, 33, 33, 33, 33, 33, 33,
      33, 33, 33, 33, 33, 33
    };
  register unsigned int hval = len;

  switch (hval)
    {
      default:
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
in_moxi_rw (register const char *str, register size_t len)
{
  enum
    {
      TOTAL_KEYWORDS = 23,
      MIN_WORD_LENGTH = 1,
      MAX_WORD_LENGTH = 17,
      MIN_HASH_VALUE = 1,
      MAX_HASH_VALUE = 32
    };

  static const struct token_t wordlist[] =
    {
      {""},
#line 11 "src/parse/gperf/reserved.gperf"
      {"_",                 MOXI_TOK_RW_UNDERSCORE},
#line 13 "src/parse/gperf/reserved.gperf"
      {"as",                MOXI_TOK_RW_AS},
#line 14 "src/parse/gperf/reserved.gperf"
      {"let",               MOXI_TOK_RW_LET},
#line 27 "src/parse/gperf/reserved.gperf"
      {"exit",              MOXI_TOK_RW_EXIT},
      {""},
#line 15 "src/parse/gperf/reserved.gperf"
      {"exists",            MOXI_TOK_RW_EXISTS},
#line 8 "src/parse/gperf/reserved.gperf"
      {"NUMERAL",           MOXI_TOK_RW_NUM},
      {""},
#line 29 "src/parse/gperf/reserved.gperf"
      {"echo",              MOXI_TOK_RW_ECHO},
      {""},
#line 17 "src/parse/gperf/reserved.gperf"
      {"assert",            MOXI_TOK_RW_ASSERT},
#line 9 "src/parse/gperf/reserved.gperf"
      {"DECIMAL",           MOXI_TOK_RW_DEC},
#line 7 "src/parse/gperf/reserved.gperf"
      {"par",               MOXI_TOK_RW_PAR},
#line 28 "src/parse/gperf/reserved.gperf"
      {"set-logic",         MOXI_TOK_RW_SET_LOGIC},
      {""},
#line 16 "src/parse/gperf/reserved.gperf"
      {"forall",            MOXI_TOK_RW_FORALL},
#line 19 "src/parse/gperf/reserved.gperf"
      {"check-system",      MOXI_TOK_RW_CHECK_SYS},
      {""},
#line 12 "src/parse/gperf/reserved.gperf"
      {"!",                 MOXI_TOK_RW_BANG},
#line 26 "src/parse/gperf/reserved.gperf"
      {"define-fun",        MOXI_TOK_RW_DEFINE_FUN},
#line 24 "src/parse/gperf/reserved.gperf"
      {"define-sort",       MOXI_TOK_RW_DEFINE_SORT},
#line 25 "src/parse/gperf/reserved.gperf"
      {"define-const",      MOXI_TOK_RW_DEFINE_CONST},
#line 18 "src/parse/gperf/reserved.gperf"
      {"define-system",     MOXI_TOK_RW_DEFINE_SYS},
      {""}, {""},
#line 23 "src/parse/gperf/reserved.gperf"
      {"declare-fun",       MOXI_TOK_RW_DECLARE_FUN},
#line 20 "src/parse/gperf/reserved.gperf"
      {"declare-sort",      MOXI_TOK_RW_DECLARE_SORT},
#line 22 "src/parse/gperf/reserved.gperf"
      {"declare-const",     MOXI_TOK_RW_DECLARE_CONST},
      {""}, {""},
#line 10 "src/parse/gperf/reserved.gperf"
      {"STRING",            MOXI_TOK_RW_STR},
#line 21 "src/parse/gperf/reserved.gperf"
      {"declare-enum-sort", MOXI_TOK_RW_DECLARE_ENUM_SORT}
    };

  if (len <= MAX_WORD_LENGTH && len >= MIN_WORD_LENGTH)
    {
      register unsigned int key = hash_rw (str, len);

      if (key <= MAX_HASH_VALUE)
        {
          register const char *s = wordlist[key].name;

          if (*str == *s && !strcmp (str + 1, s + 1))
            return &wordlist[key];
        }
    }
  return 0;
}
