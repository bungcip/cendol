#ifndef _LOCALE_H
#define _LOCALE_H

typedef struct lconv {
    char *decimal_point;
    char *thousands_sep;
    char *grouping;
    char *int_curr_symbol;
    char *currency_symbol;
    char *mon_decimal_point;
    char *mon_thousands_sep;
    char *mon_grouping;
    char *positive_sign;
    char *negative_sign;
    int int_frac_digits;
    int frac_digits;
    int p_cs_precedes;
    int p_sep_by_space;
    int n_cs_precedes;
    int n_sep_by_space;
    int p_sign_posn;
    int n_sign_posn;
} lconv;

extern char *setlocale(int category, const char *locale);
extern struct lconv *localeconv(void);

#define LC_ALL 0
#define LC_COLLATE 1
#define LC_CTYPE 2
#define LC_MONETARY 3
#define LC_NUMERIC 4
#define LC_TIME 5

#endif