#ifndef _TIME_H
#define _TIME_H

typedef long clock_t;
typedef long time_t;

struct tm {
    int tm_sec;
    int tm_min;
    int tm_hour;
    int tm_mday;
    int tm_mon;
    int tm_year;
    int tm_wday;
    int tm_yday;
    int tm_isdst;
};

struct timespec {
    time_t tv_sec;
    long tv_nsec;
};

extern clock_t clock(void);
extern time_t time(time_t *t);
extern double difftime(time_t time1, time_t time0);
extern time_t mktime(struct tm *timeptr);
extern char *asctime(const struct tm *timeptr);
extern char *ctime(const time_t *timep);
extern struct tm *gmtime(const time_t *timep);
extern struct tm *localtime(const struct tm *timep);

#define CLOCKS_PER_SEC 1000000

#endif