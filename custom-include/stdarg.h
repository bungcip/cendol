#ifndef _STDARG_H
#define _STDARG_H

/* SysV AMD64 ABI va_list structure */
typedef struct {
    unsigned int gp_offset;      /* Offset to next GP register in reg_save_area */
    unsigned int fp_offset;      /* Offset to next FP register in reg_save_area */
    void *overflow_arg_area;     /* Pointer to next stack-passed argument */
    void *reg_save_area;         /* Pointer to start of register save area */
} __va_list_tag;

typedef __va_list_tag va_list[1];

#define va_start(ap, last) __builtin_va_start(ap, last)
#define va_end(ap) __builtin_va_end(ap)
#define va_arg(ap, type) __builtin_va_arg(ap, type)
#define va_copy(dst, src) __builtin_va_copy(dst, src)

#endif