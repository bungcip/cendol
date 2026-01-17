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

#endif