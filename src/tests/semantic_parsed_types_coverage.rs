use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail, run_pass};

#[test]
fn test_sizeof_struct_expression() {
    // This test forces the parser to call `parse_parsed_type_name` -> `build_parsed_type_from_specifiers`
    // -> `parse_type_specifier_to_parsed_base` -> `alloc_struct_members`.
    // Then semantic lowering calls `visit_expression` -> `SizeOfExpr` -> ... -> `convert_to_qual_type`
    // -> `convert_parsed_base_type_to_qual_type` -> `get_struct_members`.
    run_pass(
        r#"
        int main() {
            int sz = sizeof(struct { int a; int b; });
            return 0;
        }
    "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_compound_literal_struct() {
    // Similarly, compound literals use type names with struct definitions.
    run_pass(
        r#"
        struct Point { int x; int y; };
        int main() {
            struct Point p = (struct Point){ 1, 2 };
            // Anonymous struct in compound literal
            int x = (struct { int a; }){ 1 }.a;
            return 0;
        }
    "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_alignof_struct_expression() {
    // _Alignof also takes a type name
    run_pass(
        r#"
        int main() {
            int al = _Alignof(struct { char c; });
            return 0;
        }
    "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_complex_type_specifiers() {
    // Tests various combinations in merge_parsed_type_specifiers
    run_pass("long long long x; int main() { return 0; }", CompilePhase::Mir);
    run_pass("int long long y; int main() { return 0; }", CompilePhase::Mir);
    run_pass("long long int z; int main() { return 0; }", CompilePhase::Mir);
    run_pass("unsigned long int ul; int main() { return 0; }", CompilePhase::Mir);
    run_pass(
        "int unsigned long long ull; int main() { return 0; }",
        CompilePhase::Mir,
    );
    run_pass("unsigned short int us; int main() { return 0; }", CompilePhase::Mir);
    run_pass("signed short int ss; int main() { return 0; }", CompilePhase::Mir);
}

#[test]
fn test_builtin_types_coverage() {
    // Tests for _Bool, _Complex, etc.
    run_pass(
        r#"
        _Bool b;
        _Complex float cf;
        _Complex double cd;
        _Complex long double cld;
        __builtin_va_list ap;
        int main() { return 0; }
    "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_alignment_coverage() {
    // Tests for _Alignas
    run_pass(
        r#"
        struct S {
            _Alignas(8) int x;
            _Alignas(int) char c;
        };
        int main() { return 0; }
    "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_enum_coverage() {
    // Tests for enum constants with literal evaluation
    run_pass(
        r#"
        enum E { A = 1, B = 2 };
        int main() { return 0; }
    "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_abstract_declarator_pointer() {
    // Tests for abstract pointer declarators in function params
    run_pass("void f(int *); int main() { return 0; }", CompilePhase::Mir);
}

#[test]
fn test_bitfield_declarator() {
    // Tests for bit-field declarators
    run_pass(
        r#"
        struct S {
            int x : 8;
        };
        int main() { return 0; }
    "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_anonymous_record_declarator() {
    // Tests for anonymous struct/union
    run_pass(
        r#"
        struct S {
            struct { int a; };
            int b;
        };
        int main() { return 0; }
    "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_sizeof_targeted_coverage() {
    // Tests for branches in parsed_type_builder.rs hit during type-name parsing
    run_pass("int main() { int sz = sizeof(const); return 0; }", CompilePhase::Mir);
    run_pass(
        "int main() { int sz = sizeof(_Atomic(int)); return 0; }",
        CompilePhase::Mir,
    );
    run_pass(
        "int main() { int sz = sizeof(__builtin_va_list); return 0; }",
        CompilePhase::Mir,
    );
    run_pass("int main() { int sz = sizeof(_Bool); return 0; }", CompilePhase::Mir);
    run_pass("int main() { int sz = sizeof(float); return 0; }", CompilePhase::Mir);
    run_pass("int main() { int sz = sizeof(double); return 0; }", CompilePhase::Mir);
    run_pass("int main() { int sz = sizeof(signed); return 0; }", CompilePhase::Mir);
    run_pass("int main() { int sz = sizeof(unsigned); return 0; }", CompilePhase::Mir);
    run_pass(
        "int main() { int sz = sizeof(int * restrict); return 0; }",
        CompilePhase::Mir,
    );

    // Atomic constraints
    run_fail(
        "int main() { int sz = sizeof(_Atomic(int(void))); return 0; }",
        CompilePhase::Mir,
    );

    // Hit merge_parsed_type_specifiers branches
    run_pass(
        "int main() { int sz = sizeof(long long long); return 0; }",
        CompilePhase::Mir,
    );
    run_pass(
        "int main() { int sz = sizeof(long int long long); return 0; }",
        CompilePhase::Mir,
    );
    run_pass(
        "int main() { int sz = sizeof(unsigned long long); return 0; }",
        CompilePhase::Mir,
    );
    run_pass(
        "int main() { int sz = sizeof(long long unsigned); return 0; }",
        CompilePhase::Mir,
    );
    run_pass(
        "int main() { int sz = sizeof(short int); return 0; }",
        CompilePhase::Mir,
    );
    run_pass(
        "int main() { int sz = sizeof(int short); return 0; }",
        CompilePhase::Mir,
    );
    run_pass(
        "int main() { int sz = sizeof(signed long); return 0; }",
        CompilePhase::Mir,
    );
    run_pass(
        "int main() { int sz = sizeof(long signed); return 0; }",
        CompilePhase::Mir,
    );
    run_pass("int main() { int sz = sizeof(long int); return 0; }", CompilePhase::Mir);
    run_pass("int main() { int sz = sizeof(int long); return 0; }", CompilePhase::Mir);
    run_pass(
        "int main() { int sz = sizeof(long double); return 0; }",
        CompilePhase::Mir,
    );
    run_pass(
        "int main() { int sz = sizeof(int long long); return 0; }",
        CompilePhase::Mir,
    );
    run_pass(
        "int main() { int sz = sizeof(long long int); return 0; }",
        CompilePhase::Mir,
    );
    run_pass(
        "int main() { int sz = sizeof(signed int); return 0; }",
        CompilePhase::Mir,
    );
    run_pass(
        "int main() { int sz = sizeof(int signed); return 0; }",
        CompilePhase::Mir,
    );
    run_pass(
        "int main() { int sz = sizeof(unsigned int); return 0; }",
        CompilePhase::Mir,
    );
    run_pass(
        "int main() { int sz = sizeof(int unsigned); return 0; }",
        CompilePhase::Mir,
    );

    // Conflicts
}

#[test]
fn test_default_to_int() {
    use crate::tests::test_utils::run_fail;
    // C allows 'static x;' at file scope but our lowering blocks it.
    // It should still be hit by the parser/builder.
    run_fail("static x; int main() { return 0; }", CompilePhase::Mir);
}

#[test]
fn test_sizeof_struct_with_alignment_coverage() {
    // Tests for alignment specifier processing in parsed_type_builder.rs (inside records)
    run_pass(
        r#"
        int main() {
            int sz = sizeof(struct { _Alignas(8) int x; });
            int sz2 = sizeof(struct { _Alignas(int) char c; });
            return 0;
        }
    "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_enum_evaluation_in_type_name() {
    // Tests for enum evaluating in parsed_type_builder.rs
    run_pass(
        r#"
        int main() {
            int sz = sizeof(enum { VAL = 42 });
            return 0;
        }
    "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_abstract_declarators_more() {
    // More abstract declarator coverage
    run_pass(
        "int sz = sizeof(int *[10]); int main() { return 0; }",
        CompilePhase::Mir,
    );
    run_pass(
        "int sz = sizeof(int (*)(void)); int main() { return 0; }",
        CompilePhase::Mir,
    );
}

#[test]
fn test_type_mismatch_in_type_name() {
    use crate::tests::test_utils::run_fail;
    // This should hit merge_parsed_type_specifiers mismatch arm
    run_fail(
        "int main() { int sz = sizeof(int float); return 0; }",
        CompilePhase::Mir,
    );
    run_fail(
        "int main() { int sz = sizeof(struct S int); return 0; }",
        CompilePhase::Mir,
    );
    run_fail(
        "int main() { int sz = sizeof(enum E int); return 0; }",
        CompilePhase::Mir,
    );
    run_fail(
        "int main() { int sz = sizeof(int struct S); return 0; }",
        CompilePhase::Mir,
    );
}

#[test]
fn test_struct_parsing_coverage() {
    use crate::driver::artifact::CompilePhase;
    use crate::tests::test_utils::run_pass;

    // 1. Nested Anonymous Struct with Multiple Declarators (Line 107)
    run_pass(
        "struct Outer { struct { int a; } s1, s2; }; int main() { return 0; }",
        CompilePhase::Mir,
    );

    // 2. Nested Named Struct Definitions (Lines 140-148, 151-162, 164-168, 171-181, 184-186, 188-191)
    run_pass(
        "struct Outer { struct Inner { int a; }; }; int main() { return 0; }",
        CompilePhase::Mir,
    );
    run_pass(
        "struct Outer { struct Inner { int a; } i; }; int main() { return 0; }",
        CompilePhase::Mir,
    );
    run_pass(
        "struct Outer { struct Inner2 { int a; } i1, i2; }; int main() { return 0; }",
        CompilePhase::Mir,
    );

    // 3. Forward Declaration in Struct Member (Lines 202, 204-207)
    run_pass(
        "struct Outer { struct Inner; }; int main() { return 0; }",
        CompilePhase::Mir,
    );

    // 4. GCC Attributes on Structs (Lines 22, 37)
    run_pass(
        "struct __attribute__((packed)) S { int x; }; int main() { return 0; }",
        CompilePhase::Mir,
    );
    run_pass(
        "struct S2 { int x; } __attribute__((aligned(8))); int main() { return 0; }",
        CompilePhase::Mir,
    );

    // 5. Union variants
    run_pass(
        "union U { union { int a; float b; } anonymous; }; int main() { return 0; }",
        CompilePhase::Mir,
    );
}
