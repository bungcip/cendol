#ifndef _CENDOL_FLOAT_H
#define _CENDOL_FLOAT_H

/* Floating-point characteristics for IEEE 754 binary64 (double) and binary32 (float) */

/* Radix of exponent representation */
#define FLT_RADIX 2

/* Number of base-FLT_RADIX digits in the floating-point significand */
#define FLT_MANT_DIG 24
#define DBL_MANT_DIG 53
#define LDBL_MANT_DIG 53

/* Number of decimal digits that can be represented without change */
#define FLT_DIG 6
#define DBL_DIG 15
#define LDBL_DIG 15

/* Minimum negative integer such that FLT_RADIX raised to that power minus 1 is a normalized float */
#define FLT_MIN_EXP (-125)
#define DBL_MIN_EXP (-1021)
#define LDBL_MIN_EXP (-1021)

/* Minimum negative integer such that 10 raised to that power is in the range of normalized floats */
#define FLT_MIN_10_EXP (-37)
#define DBL_MIN_10_EXP (-307)
#define LDBL_MIN_10_EXP (-307)

/* Maximum integer such that FLT_RADIX raised to that power minus 1 is a representable finite float */
#define FLT_MAX_EXP 128
#define DBL_MAX_EXP 1024
#define LDBL_MAX_EXP 1024

/* Maximum integer such that 10 raised to that power is in the range of representable finite floats */
#define FLT_MAX_10_EXP 38
#define DBL_MAX_10_EXP 308
#define LDBL_MAX_10_EXP 308

/* Maximum representable finite floating-point number */
#define FLT_MAX 3.40282347e+38F
#define DBL_MAX 1.7976931348623157e+308
#define LDBL_MAX 1.7976931348623157e+308L

/* Difference between 1 and the least value greater than 1 that is representable */
#define FLT_EPSILON 1.19209290e-7F
#define DBL_EPSILON 2.2204460492503131e-16
#define LDBL_EPSILON 2.2204460492503131e-16L

/* Minimum normalized positive floating-point number */
#define FLT_MIN 1.17549435e-38F
#define DBL_MIN 2.2250738585072014e-308
#define LDBL_MIN 2.2250738585072014e-308L

/* Number of decimal digits to represent a floating-point number uniquely */
#define DECIMAL_DIG 17

/* C11 additions */
#define FLT_DECIMAL_DIG 9
#define DBL_DECIMAL_DIG 17
#define LDBL_DECIMAL_DIG 17

/* Evaluation method */
#define FLT_EVAL_METHOD 0

/* Rounding mode */
#define FLT_ROUNDS 1

/* Denormalized numbers support */
#define FLT_HAS_SUBNORM 1
#define DBL_HAS_SUBNORM 1
#define LDBL_HAS_SUBNORM 1

/* Minimum positive subnormal floating-point number */
#define FLT_TRUE_MIN 1.40129846e-45F
#define DBL_TRUE_MIN 4.9406564584124654e-324
#define LDBL_TRUE_MIN 4.9406564584124654e-324L

#endif
