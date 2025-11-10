
#include <stdalign.h>
#include <stdatomic.h>
#include <stdbool.h>
#include <stdnoreturn>
#include <threads.h>

_Thread_local _Atomic bool global_flag = false;

noreturn void error_handler(void) {
    atomic_store(&global_flag, true);
    exit(1);
}

_Alignas(64) char aligned_buffer[64];

#define max(x, y) _Generic((x), \
    int: ((x) > (y) ? (x) : (y)), \
    default: 0 \
)

_Static_assert(sizeof(int) >= 4, "int too small");

int main(void) {
    bool condition = true;
    int result = max(10, 20);
    
    if (condition) {
        result *= 2;
    } else {
        error_handler();
    }
    
    return result;
}
