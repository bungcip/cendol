#ifndef _STDIO_H
#define _STDIO_H

#include <stddef.h> 
#include <sys/types.h>
#include <stdarg.h>

#define EOF (-1) 

typedef struct _IO_FILE FILE;

extern FILE *stdin;
extern FILE *stdout;
extern FILE *stderr;

extern int printf(const char *format, ...);
extern int fprintf(FILE *stream, const char *format, ...);
extern int sprintf(char *str, const char *format, ...);
extern int snprintf(char *str, size_t size, const char *format, ...);
extern int vsnprintf(char *str, size_t size, const char *format, va_list ap);
extern int sscanf(const char *str, const char *format, ...);

extern FILE *fopen(const char *filename, const char *mode);
extern int fclose(FILE *stream);
extern size_t fread(void *ptr, size_t size, size_t nmemb, FILE *stream);
extern size_t fwrite(const void *ptr, size_t size, size_t nmemb, FILE *stream);
extern int fgetc(FILE *stream);
extern int getc(FILE *stream);
extern char *fgets(char *s, int n, FILE *stream);
extern ssize_t getline(char **lineptr, size_t *n, FILE *stream);
extern int putchar(int c);
extern void perror(const char *s);

#endif