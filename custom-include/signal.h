#ifndef _SIGNAL_H
#define _SIGNAL_H

typedef int sig_atomic_t;

typedef void (*sighandler_t)(int);

#define SIG_DFL ((sighandler_t)0)
#define SIG_ERR ((sighandler_t)(-1))
#define SIG_IGN ((sighandler_t)1)

#define SIGABRT 6
#define SIGFPE 8
#define SIGILL 4
#define SIGINT 2
#define SIGSEGV 11
#define SIGTERM 15

extern int raise(int sig);

#endif