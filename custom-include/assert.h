#ifndef _ASSERT_H
#define _ASSERT_H

#ifdef NDEBUG
#define assert(ignore) ((void)0)
#else
#define assert(expr) ((expr) ? (void)0 : __assert(#expr, __FILE__, __LINE__))
#endif

void __assert(const char *expr, const char *file, int line);

#endif