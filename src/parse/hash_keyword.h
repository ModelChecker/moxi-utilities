/* ANSI-C code produced by gperf version 3.1 */
/* Command-line: gperf -C -E -t --output-file=src/parse/hash_keyword.h --lookup-function-name=in_moxi_kw --hash-function=hash_kw src/parse/gperf/keyword.gperf  */
/* Computed positions: -k'2' */

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

#line 1 "src/parse/gperf/keyword.gperf"

#include <string.h>
#include "token.h"
#line 5 "src/parse/gperf/keyword.gperf"
struct token_t;
/* maximum key range = 17, duplicates = 0 */

#ifdef __GNUC__
__inline
#else
#ifdef __cplusplus
inline
#endif
#endif
static unsigned int
hash_kw (register const char *str, register size_t len)
{
  static const unsigned char asso_values[] =
    {
      22, 22, 22, 22, 22, 22, 22, 22, 22, 22,
      22, 22, 22, 22, 22, 22, 22, 22, 22, 22,
      22, 22, 22, 22, 22, 22, 22, 22, 22, 22,
      22, 22, 22, 22, 22, 22, 22, 22, 22, 22,
      22, 22, 22, 22, 22, 22, 22, 22, 22, 22,
      22, 22, 22, 22, 22, 22, 22, 22, 22, 22,
      22, 22, 22, 22, 22, 22, 22, 22, 22, 22,
      22, 22, 22, 22, 22, 22, 22, 22, 22, 22,
      22, 22, 22, 22, 22, 22, 22, 22, 22, 22,
      22, 22, 22, 22, 22, 22, 22, 10, 22,  5,
      22, 22,  0, 22, 22,  5, 22, 22,  9, 22,
      22,  5, 22,  0, 15,  0, 10, 22, 22, 22,
      22, 22, 22, 22, 22, 22, 22, 22, 22, 22,
      22, 22, 22, 22, 22, 22, 22, 22, 22, 22,
      22, 22, 22, 22, 22, 22, 22, 22, 22, 22,
      22, 22, 22, 22, 22, 22, 22, 22, 22, 22,
      22, 22, 22, 22, 22, 22, 22, 22, 22, 22,
      22, 22, 22, 22, 22, 22, 22, 22, 22, 22,
      22, 22, 22, 22, 22, 22, 22, 22, 22, 22,
      22, 22, 22, 22, 22, 22, 22, 22, 22, 22,
      22, 22, 22, 22, 22, 22, 22, 22, 22, 22,
      22, 22, 22, 22, 22, 22, 22, 22, 22, 22,
      22, 22, 22, 22, 22, 22, 22, 22, 22, 22,
      22, 22, 22, 22, 22, 22, 22, 22, 22, 22,
      22, 22, 22, 22, 22, 22, 22, 22, 22, 22,
      22, 22, 22, 22, 22, 22
    };
  return len + asso_values[(unsigned char)str[1]];
}

const struct token_t *
in_moxi_kw (register const char *str, register size_t len)
{
  enum
    {
      TOTAL_KEYWORDS = 13,
      MIN_WORD_LENGTH = 4,
      MAX_WORD_LENGTH = 8,
      MIN_HASH_VALUE = 5,
      MAX_HASH_VALUE = 21
    };

  static const struct token_t wordlist[] =
    {
      {""}, {""}, {""}, {""}, {""},
#line 16 "src/parse/gperf/keyword.gperf"
      {":fair",    MOXI_TOK_KW_FAIR},
#line 18 "src/parse/gperf/keyword.gperf"
      {":query",   MOXI_TOK_KW_QUERY},
#line 13 "src/parse/gperf/keyword.gperf"
      {":subsys",  MOXI_TOK_KW_SUBSYS},
#line 19 "src/parse/gperf/keyword.gperf"
      {":queries", MOXI_TOK_KW_QUERIES},
#line 12 "src/parse/gperf/keyword.gperf"
      {":inv",     MOXI_TOK_KW_INV},
#line 10 "src/parse/gperf/keyword.gperf"
      {":init",    MOXI_TOK_KW_INIT},
#line 7 "src/parse/gperf/keyword.gperf"
      {":input",   MOXI_TOK_KW_INPUT},
#line 8 "src/parse/gperf/keyword.gperf"
      {":output",  MOXI_TOK_KW_OUTPUT},
#line 17 "src/parse/gperf/keyword.gperf"
      {":current", MOXI_TOK_KW_CURRENT},
      {""},
#line 9 "src/parse/gperf/keyword.gperf"
      {":local",   MOXI_TOK_KW_LOCAL},
#line 11 "src/parse/gperf/keyword.gperf"
      {":trans",   MOXI_TOK_KW_TRANS},
#line 14 "src/parse/gperf/keyword.gperf"
      {":assume",  MOXI_TOK_KW_ASSUME},
      {""}, {""}, {""},
#line 15 "src/parse/gperf/keyword.gperf"
      {":reach",   MOXI_TOK_KW_REACH}
    };

  if (len <= MAX_WORD_LENGTH && len >= MIN_WORD_LENGTH)
    {
      register unsigned int key = hash_kw (str, len);

      if (key <= MAX_HASH_VALUE)
        {
          register const char *s = wordlist[key].name;

          if (*str == *s && !strcmp (str + 1, s + 1))
            return &wordlist[key];
        }
    }
  return 0;
}
