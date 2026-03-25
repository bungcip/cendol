#ifndef _CENDOL_FLOAT_H
#define _CENDOL_FLOAT_H

/* Floating-point characteristics */

/* Radix of exponent representation */
#define FLT_RADIX __FLT_RADIX__

/* Number of base-FLT_RADIX digits in the floating-point significand */
#define FLT_MANT_DIG __FLT_MANT_DIG__
#define DBL_MANT_DIG __DBL_MANT_DIG__
#define LDBL_MANT_DIG __LDBL_MANT_DIG__

/* Number of decimal digits that can be represented without change */
#define FLT_DIG __FLT_DIG__
#define DBL_DIG __DBL_DIG__
#define LDBL_DIG __LDBL_DIG__

/* Minimum negative integer such that FLT_RADIX raised to that power minus 1 is a normalized float */
#define FLT_MIN_EXP __FLT_MIN_EXP__
#define DBL_MIN_EXP __DBL_MIN_EXP__
#define LDBL_MIN_EXP __LDBL_MIN_EXP__

/* Minimum negative integer such that 10 raised to that power is in the range of normalized floats */
#define FLT_MIN_10_EXP __FLT_MIN_10_EXP__
#define DBL_MIN_10_EXP __DBL_MIN_10_EXP__
#define LDBL_MIN_10_EXP __LDBL_MIN_10_EXP__

/* Maximum integer such that FLT_RADIX raised to that power minus 1 is a representable finite float */
#define FLT_MAX_EXP __FLT_MAX_EXP__
#define DBL_MAX_EXP __DBL_MAX_EXP__
#define LDBL_MAX_EXP __LDBL_MAX_EXP__

/* Maximum integer such that 10 raised to that power is in the range of representable finite floats */
#define FLT_MAX_10_EXP __FLT_MAX_10_EXP__
#define DBL_MAX_10_EXP __DBL_MAX_10_EXP__
#define LDBL_MAX_10_EXP __LDBL_MAX_10_EXP__

/* Maximum representable finite floating-point number */
#define FLT_MAX __FLT_MAX__
#define DBL_MAX __DBL_MAX__
#define LDBL_MAX __LDBL_MAX__

/* Difference between 1 and the least value greater than 1 that is representable */
#define FLT_EPSILON __FLT_EPSILON__
#define DBL_EPSILON __DBL_EPSILON__
#define LDBL_EPSILON __LDBL_EPSILON__

/* Minimum normalized positive floating-point number */
#define FLT_MIN __FLT_MIN__
#define DBL_MIN __DBL_MIN__
#define LDBL_MIN __LDBL_MIN__

/* Number of decimal digits to represent a floating-point number uniquely */
#define DECIMAL_DIG __DECIMAL_DIG__

/* C11 additions */
#define FLT_DECIMAL_DIG __FLT_DECIMAL_DIG__
#define DBL_DECIMAL_DIG __DBL_DECIMAL_DIG__
#define LDBL_DECIMAL_DIG __LDBL_DECIMAL_DIG__

/* Evaluation method */
#define FLT_EVAL_METHOD __FLT_EVAL_METHOD__

/* Rounding mode */
#define FLT_ROUNDS __FLT_ROUNDS__

/* Denormalized numbers support */
#define FLT_HAS_SUBNORM __FLT_HAS_SUBNORM__
#define DBL_HAS_SUBNORM __DBL_HAS_SUBNORM__
#define LDBL_HAS_SUBNORM __LDBL_HAS_SUBNORM__

/* Minimum positive subnormal floating-point number */
#define FLT_TRUE_MIN __FLT_TRUE_MIN__
#define DBL_TRUE_MIN __DBL_TRUE_MIN__
#define LDBL_TRUE_MIN __LDBL_TRUE_MIN__

#endif
