#ifndef _STDLIB_H
#define _STDLIB_H

typedef unsigned long size_t;

typedef struct {
    int quot;
    int rem;
} div_t;

typedef struct {
    long quot;
    long rem;
} ldiv_t;

typedef struct {
    long long quot;
    long long rem;
} lldiv_t;

extern void *malloc(size_t size);
extern void free(void *ptr);
extern void *calloc(size_t num, size_t size);
extern void *realloc(void *ptr, size_t size);
extern void abort(void);
extern int atexit(void (*func)(void));
extern void exit(int status);
extern void _Exit(int status);
extern char *getenv(const char *name);
extern int system(const char *string);
extern void *bsearch(const void *key, const void *base, size_t nmemb, size_t size, int (*compar)(const void *, const void *));
extern void qsort(void *base, size_t nmemb, size_t size, int (*compar)(const void *, const void *));
extern int abs(int n);
extern long labs(long n);
extern long long llabs(long long n);
extern div_t div(int numer, int denom);
extern ldiv_t ldiv(long numer, long denom);
extern lldiv_t lldiv(long long numer, long long denom);
extern int rand(void);
extern void srand(unsigned int seed);

#define EXIT_SUCCESS 0
#define EXIT_FAILURE 1
#define RAND_MAX 2147483647

#endif