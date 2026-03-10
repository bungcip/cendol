#include <stdio.h>

_Thread_local int tls_var = 10;

int main() {
    printf("%d\n", tls_var);
    return 0;
}
