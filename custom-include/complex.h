#ifndef _COMPLEX_H
#define _COMPLEX_H

#define complex _Complex

#define _Complex_I (0.0f + 1.0if)
#define I _Complex_I

#define CMPLX(x, y) ((double _Complex){ (double)(x), (double)(y) })
#define CMPLXF(x, y) ((float _Complex){ (float)(x), (float)(y) })
#define CMPLXL(x, y) ((long double _Complex){ (long double)(x), (long double)(y) })

#define creal(z) (__real__(z))
#define cimag(z) (__imag__(z))

#endif
