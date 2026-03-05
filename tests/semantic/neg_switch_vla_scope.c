// TEST: 00104_neg_switch_vla_scope
// CATEGORY: negative
// STANDARD: C11
// REFERENCE: ISO C11 §6.8.4.2p1
// EXPECT: compile_error

int main(void) {
    int n = 10;
    switch(n) {
        case 1:;
            int a[n];
        case 2: // Error: jump into scope of VLA
            return 0;
    }
}
