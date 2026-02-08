use crate::tests::codegen_common::run_c_code_with_output;

#[test]
fn test_pointer_arithmetic_offset() {
    let source = r#"
int printf(const char* format, ...);

typedef struct {
    long a, b, c, d;
} MyStruct; // sizeof should be 32 bytes

static const MyStruct arr[] = {
    {1, 1, 1, 1},
    {2, 2, 2, 2}
};

int main() {
    // Address via pointer arithmetic (ptr + i) should add i * sizeof(MyStruct)
    const MyStruct* p_index = &arr[1];
    const MyStruct* p_arith = arr + 1;

    long diff = (char*)p_arith - (char*)arr;

    if (p_arith != p_index) {
        printf("FAIL: (arr + 1) != &arr[1]\n");
        printf("      Expected offset: %lu\n", sizeof(MyStruct));
        printf("      Actual offset:   %ld\n", diff);
        return 1;
    }

    printf("PASSED: Pointer arithmetic is correct.\n");
    return 0;
}
"#;
    let output = run_c_code_with_output(source);
    assert!(output.contains("PASSED: Pointer arithmetic is correct."), "Output was: {}", output);
}

#[test]
fn test_pointer_arithmetic_sub_assign() {
    let source = r#"
int printf(const char* format, ...);

typedef struct {
    long a, b, c, d;
} MyStruct;

static MyStruct arr[2];

int main() {
    MyStruct* p = &arr[1];
    p -= 1; // ptr -= int

    if (p == &arr[0]) {
        printf("PASSED: Pointer sub assign is correct.\n");
    } else {
        printf("FAIL: Pointer sub assign failed.\n");
    }
    return 0;
}
"#;
    let output = run_c_code_with_output(source);
    assert!(output.contains("PASSED: Pointer sub assign is correct."), "Output was: {}", output);
}
