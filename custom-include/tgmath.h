#ifndef _TGMATH_H
#define _TGMATH_H

#include <math.h>
#include <complex.h>

#define acos(x) __tg_generic(acos, acosl, acosf, cacos, (x))
#define asin(x) __tg_generic(asin, asinl, asinf, casin, (x))
#define atan(x) __tg_generic(atan, atanl, atanf, catan, (x))
#define acosh(x) __tg_generic(acosh, acoshl, acoshf, cacosh, (x))
#define asinh(x) __tg_generic(asinh, asinhl, asinhf, casinh, (x))
#define atanh(x) __tg_generic(atanh, atanhl, atanhf, catanh, (x))
#define cos(x) __tg_generic(cos, cosl, cosf, ccos, (x))
#define sin(x) __tg_generic(sin, sinl, sinf, csin, (x))
#define tan(x) __tg_generic(tan, tanl, tanf, ctan, (x))
#define cosh(x) __tg_generic(cosh, coshl, coshf, ccosh, (x))
#define sinh(x) __tg_generic(sinh, sinhl, sinhf, csinh, (x))
#define tanh(x) __tg_generic(tanh, tanhl, tanhf, ctanh, (x))
#define exp(x) __tg_generic(exp, expl, expf, cexp, (x))
#define log(x) __tg_generic(log, logl, logf, clog, (x))
#define pow(x, y) __tg_generic2(pow, powl, powf, cpow, (x), (y))
#define sqrt(x) __tg_generic(sqrt, sqrtl, sqrtf, csqrt, (x))
#define fabs(x) __tg_generic(fabs, fabsl, fabsf, cabs, (x))

#endif