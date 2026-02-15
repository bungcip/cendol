use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_pass;

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
