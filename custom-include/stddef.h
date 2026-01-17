#ifndef _STDDEF_H
#define _STDDEF_H

/* NULL */
#ifndef NULL
#define NULL (void*)0
#endif

/* size_t */
/* Skip size_t if _STDIO_H is defined, because stdio.h likely defines it */
#if !defined(_SIZE_T) && !defined(_SIZE_T_DEFINED) && !defined(__SIZE_T) && !defined(__size_t_defined) && !defined(_STDIO_H)
#define _SIZE_T
#define _SIZE_T_DEFINED
#define __SIZE_T
#define __size_t_defined
#if __LP64__
typedef unsigned long size_t;
#else
typedef unsigned int size_t;
#endif
#endif

/* ptrdiff_t */
#if !defined(_PTRDIFF_T) && !defined(_PTRDIFF_T_DEFINED) && !defined(__PTRDIFF_T)
#define _PTRDIFF_T
#define _PTRDIFF_T_DEFINED
#define __PTRDIFF_T
#if __LP64__
typedef long ptrdiff_t;
#else
typedef int ptrdiff_t;
#endif
#endif

/* wchar_t */
#ifndef _WCHAR_T_DEFINED
#define _WCHAR_T_DEFINED
typedef int wchar_t;
#endif

#endif