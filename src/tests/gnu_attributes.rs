use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::*;

#[test]
fn test_attribute_aligned_variable() {
    // __attribute__((aligned(16))) should set alignment
    let source = r#"
        int x __attribute__((aligned(16)));
        _Static_assert(_Alignof(x) == 16, "alignment should be 16");

        int main() {
            int y __attribute__((aligned(32)));
            _Static_assert(_Alignof(y) == 32, "alignment should be 32");
            return 0;
        }
    "#;
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_attribute_packed_struct() {
    // __attribute__((packed)) should remove padding
    let source = r#"
        struct __attribute__((packed)) S1 {
            char c;
            int i;
        };
        _Static_assert(sizeof(struct S1) == 5, "packed size should be 5");

        struct S2 {
            char c;
            int i;
        } __attribute__((packed));
        _Static_assert(sizeof(struct S2) == 5, "packed size should be 5");

        union __attribute__((packed)) U1 {
            char c;
            int i;
        };
        _Static_assert(sizeof(union U1) == 4, "union size should be 4");
    "#;
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_attribute_packed_member() {
    // __attribute__((packed)) on member should reduce its alignment
    let source = r#"
        struct S3 {
            char c;
            int i __attribute__((packed));
        };
        _Static_assert(sizeof(struct S3) == 5, "packed member should result in size 5");
    "#;
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_attribute_aligned_struct() {
    // __attribute__((aligned(16))) on struct definition
    let source = r#"
        struct __attribute__((aligned(16))) S4 {
            int x;
        };
        _Static_assert(_Alignof(struct S4) == 16, "struct alignment should be 16");
        _Static_assert(sizeof(struct S4) == 16, "struct size should be 16 due to alignment");
    "#;
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_attribute_multiple() {
    // Multiple attributes in one list
    let source = r#"
        struct __attribute__((packed, aligned(8))) S5 {
            char c;
            int i;
        };
        _Static_assert(sizeof(struct S5) == 8, "packed and aligned(8) size should be 8");
        _Static_assert(_Alignof(struct S5) == 8, "packed and aligned(8) alignment should be 8");
    "#;
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_attribute_underscore_variants() {
    // __aligned__ and __packed__ variants
    let source = r#"
        struct __attribute__((__packed__)) S6 {
            char c;
            int i;
        };
        _Static_assert(sizeof(struct S6) == 5, "packed size should be 5");

        int x __attribute__((__aligned__(16)));
        _Static_assert(_Alignof(x) == 16, "alignment should be 16");
    "#;
    run_pass(source, CompilePhase::Mir);
}
