#ifndef _INTTYPES_H
#define _INTTYPES_H

#include <stdint.h>

typedef struct {
    intmax_t quot;
    intmax_t rem;
} imaxdiv_t;

extern intmax_t imaxabs(intmax_t j);
extern imaxdiv_t imaxdiv(intmax_t numer, intmax_t denom);
extern intmax_t strtoimax(const char *nptr, char **endptr, int base);
extern uintmax_t strtoumax(const char *nptr, char **endptr, int base);
extern intmax_t wcstoimax(const wchar_t *nptr, wchar_t **endptr, int base);
extern uintmax_t wcstoumax(const wchar_t *nptr, wchar_t **endptr, int base);

#define PRId8 "d"
#define PRId16 "d"
#define PRId32 "d"
#define PRId64 "lld"

#define PRIi8 "d"
#define PRIi16 "d"
#define PRIi32 "d"
#define PRIi64 "lld"

#define PRIo8 "o"
#define PRIo16 "o"
#define PRIo32 "o"
#define PRIo64 "llo"

#define PRIu8 "u"
#define PRIu16 "u"
#define PRIu32 "u"
#define PRIu64 "llu"

#define PRIx8 "x"
#define PRIx16 "x"
#define PRIx32 "x"
#define PRIx64 "llx"

#define PRIX8 "X"
#define PRIX16 "X"
#define PRIX32 "X"
#define PRIX64 "llX"

#define PRIdFAST8 "d"
#define PRIdFAST16 "d"
#define PRIdFAST32 "d"
#define PRIdFAST64 "ld"

#define PRIiFAST8 "d"
#define PRIiFAST16 "d"
#define PRIiFAST32 "d"
#define PRIiFAST64 "ld"

#define PRIoFAST8 "o"
#define PRIoFAST16 "o"
#define PRIoFAST32 "o"
#define PRIoFAST64 "lo"

#define PRIuFAST8 "u"
#define PRIuFAST16 "u"
#define PRIuFAST32 "u"
#define PRIuFAST64 "lu"

#define PRIxFAST8 "x"
#define PRIxFAST16 "x"
#define PRIxFAST32 "x"
#define PRIxFAST64 "lx"

#define PRIXFAST8 "X"
#define PRIXFAST16 "X"
#define PRIXFAST32 "X"
#define PRIXFAST64 "LX"

#define PRIdLEAST8 "d"
#define PRIdLEAST16 "d"
#define PRIdLEAST32 "d"
#define PRIdLEAST64 "lld"

#define PRIiLEAST8 "d"
#define PRIiLEAST16 "d"
#define PRIiLEAST32 "d"
#define PRIiLEAST64 "lld"

#define PRIoLEAST8 "o"
#define PRIoLEAST16 "o"
#define PRIoLEAST32 "o"
#define PRIoLEAST64 "llo"

#define PRIuLEAST8 "u"
#define PRIuLEAST16 "u"
#define PRIuLEAST32 "u"
#define PRIuLEAST64 "llu"

#define PRIxLEAST8 "x"
#define PRIxLEAST16 "x"
#define PRIxLEAST32 "x"
#define PRIxLEAST64 "llx"

#define PRIXLEAST8 "X"
#define PRIXLEAST16 "X"
#define PRIXLEAST32 "X"
#define PRIXLEAST64 "llX"

#define PRIdPTR "ld"
#define PRIiPTR "ld"
#define PRIoPTR "lo"
#define PRIuPTR "lu"
#define PRIxPTR "lx"
#define PRIXPTR "lX"

#define PRIdMAX "lld"
#define PRIiMAX "lld"
#define PRIoMAX "llo"
#define PRIuMAX "llu"
#define PRIxMAX "llx"
#define PRIXMAX "llX"

#endif