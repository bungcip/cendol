#ifndef _STDDEF_H
#define _STDDEF_H

/* NULL */
#define NULL (void*)0

/* size_t */
typedef __SIZE_TYPE__ size_t;

/* ptrdiff_t */
typedef __PTRDIFF_TYPE__ ptrdiff_t;

/* wchar_t */
typedef __WCHAR_TYPE__ wchar_t;

#define offsetof(type, member) __builtin_offsetof(type, member)

/* max_align_t */
#if __STDC_VERSION__ >= 201112L
typedef struct {
  long long __max_align_ll;
  long double __max_align_ld;
} max_align_t;
#endif

#endif