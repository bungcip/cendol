#ifndef _ERRNO_H
#define _ERRNO_H

extern int *__errno_location(void);
#define errno (*__errno_location())

#define ENOENT 2
#define ENOTTY 25

#define EDOM 33
#define ERANGE 34

#endif