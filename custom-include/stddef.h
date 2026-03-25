#ifndef _STDDEF_H
#define _STDDEF_H

/* NULL */
#define NULL (void*)0

/* size_t */
#if __LP64__
typedef unsigned long size_t;
#else
typedef unsigned int size_t;
#endif

/* ptrdiff_t */
#if __LP64__
typedef long ptrdiff_t;
#else
typedef int ptrdiff_t;
#endif

/* wchar_t */
typedef int wchar_t;

#define offsetof(type, member) __builtin_offsetof(type, member)

/* max_align_t */
#if __STDC_VERSION__ >= 201112L
typedef struct {
  long long __max_align_ll;
  long double __max_align_ld;
} max_align_t;
#endif

#endif