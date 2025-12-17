#ifndef _SETJMP_H
#define _SETJMP_H

typedef long jmp_buf[16];

extern int setjmp(jmp_buf env);
extern void longjmp(jmp_buf env, int val);

#endif