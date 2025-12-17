#ifndef _MATH_H
#define _MATH_H

typedef double double_t;
typedef float float_t;

extern double sin(double x);
extern double cos(double x);
extern double tan(double x);
extern double asin(double x);
extern double acos(double x);
extern double atan(double x);
extern double atan2(double y, double x);
extern double sinh(double x);
extern double cosh(double x);
extern double tanh(double x);
extern double exp(double x);
extern double log(double x);
extern double log10(double x);
extern double pow(double x, double y);
extern double sqrt(double x);
extern double ceil(double x);
extern double floor(double x);
extern double fabs(double x);
extern double fmod(double x, double y);
extern double trunc(double x);
extern double round(double x);
extern int isnan(double x);
extern int isinf(double x);
extern int isfinite(double x);
extern int signbit(double x);

#define M_PI 3.14159265358979323846
#define M_E 2.71828182845904523536
#define INFINITY (1.0f/0.0f)
#define NAN (0.0f/0.0f)

#endif