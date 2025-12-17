#ifndef _THREADS_H
#define _THREADS_H

typedef int mtx_t;
typedef int cnd_t;
typedef int thrd_t;
typedef int tss_t;
typedef int once_flag;

typedef void (*tss_destructor_t)(void*);
typedef int (*thrd_start_t)(void*);

#define mtx_plain 0
#define mtx_recursive 1
#define mtx_timed 2

#define thrd_success 0
#define thrd_timeout 1
#define thrd_error 2
#define thrd_busy 3

#define tss_dtor_never 0
#define tss_dtor_always 1

extern int thrd_create(thrd_t *thr, thrd_start_t func, void *arg);
extern thrd_t thrd_current(void);
extern int thrd_detach(thrd_t thr);
extern void thrd_exit(int res);
extern int thrd_join(thrd_t thr, int *res);
extern void thrd_sleep(const struct timespec *duration, struct timespec *remaining);
extern void thrd_yield(void);

extern int mtx_init(mtx_t *mtx, int type);
extern void mtx_destroy(mtx_t *mtx);
extern int mtx_lock(mtx_t *mtx);
extern int mtx_timedlock(mtx_t *mtx, const struct timespec *ts);
extern int mtx_trylock(mtx_t *mtx);
extern int mtx_unlock(mtx_t *mtx);

extern int cnd_init(cnd_t *cond);
extern void cnd_destroy(cnd_t *cond);
extern int cnd_signal(cnd_t *cond);
extern int cnd_broadcast(cnd_t *cond);
extern int cnd_wait(cnd_t *cond, mtx_t *mtx);
extern int cnd_timedwait(cnd_t *cond, mtx_t *mtx, const struct timespec *ts);

extern void call_once(once_flag *flag, void (*func)(void));

extern int tss_create(tss_t *key, tss_destructor_t dtor);
extern void tss_delete(tss_t key);
extern void *tss_get(tss_t key);
extern int tss_set(tss_t key, void *val);

#endif