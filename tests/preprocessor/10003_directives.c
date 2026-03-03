// TEST: 10003_directives
// CATEGORY: preprocessor
// STANDARD: C11

#line 100 "new_file.c"
int x = __LINE__;
char *f = __FILE__;
