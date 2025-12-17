#ifndef _FENV_H
#define _FENV_H

typedef unsigned long fexcept_t;
typedef unsigned long fenv_t;

#define FE_DIVBYZERO 4
#define FE_INEXACT 1
#define FE_INVALID 8
#define FE_OVERFLOW 2
#define FE_UNDERFLOW 16
#define FE_ALL_EXCEPT 31

#define FE_DOWNWARD 1024
#define FE_TONEAREST 0
#define FE_TOWARDZERO 3072
#define FE_UPWARD 2048

extern int feclearexcept(int excepts);
extern int fegetexceptflag(fexcept_t *flagp, int excepts);
extern int feraiseexcept(int excepts);
extern int fesetexceptflag(const fexcept_t *flagp, int excepts);
extern int fetestexcept(int excepts);
extern int fegetround(void);
extern int fesetround(int round);
extern int fegetenv(fenv_t *envp);
extern int feholdexcept(fenv_t *envp);
extern int fesetenv(const fenv_t *envp);
extern int feupdateenv(const fenv_t *envp);

#endif