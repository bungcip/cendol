#ifndef _SYS_TIME_H
#define _SYS_TIME_H

#include <time.h>
#include <sys/types.h>

struct timeval {
    long tv_sec;
    long tv_usec;
};

#endif
