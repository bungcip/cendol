// TEST: 00103_neg_goto_vla_scope
// CATEGORY: negative
// STANDARD: C11
// REFERENCE: ISO C11 §6.8.6.1p1
// EXPECT: compile_error

int main(void) {
    int n = 10;
    goto target; // Error: jump into scope of VLA
    int a[n];
target:
    return 0;
}
