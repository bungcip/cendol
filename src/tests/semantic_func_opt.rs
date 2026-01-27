use crate::tests::semantic_common::*;

#[test]
fn test_func_opt_unused() {
    let source = r#"
        void foo() {
            // __func__ is not used here
        }
    "#;
    // Check the MIR to ensure __func__ global is NOT generated.
    let mir_output = setup_mir(source);
    insta::assert_snapshot!(mir_output, @r"
    type %t0 = void

    fn foo() -> void
    {

      bb1:
        return
    }
    ");
}

#[test]
fn test_func_opt_used() {
    let source = r#"
        int printf(const char *, ...);
        void foo() {
            printf("%s", __func__);
        }
    "#;
    let mir_output = setup_mir(source);
    insta::assert_snapshot!(mir_output, @r#"
    type %t0 = i32
    type %t1 = i8
    type %t2 = ptr<%t1>
    type %t3 = void
    type %t4 = fn(%t2, ...) -> %t0
    type %t5 = [3]%t1
    type %t6 = [3]%t1
    type %t7 = [4]%t1
    type %t8 = [4]%t1

    global @.L.str0: [3]i8 = const "%s"
    global @__func__.3: [4]i8 = const array_literal [const 102, const 111, const 111, const 0]

    extern fn printf(%param0: ptr<i8>, ...) -> i32

    fn foo() -> void
    {

      bb1:
        call printf(cast<ptr<i8>>(const @.L.str0), cast<ptr<i8>>(addr_of(@__func__.3)))
        return
    }
    "#);
}

#[test]
fn test_func_opt_shadowed() {
    let source = r#"
        int printf(const char *, ...);
        void foo() {
            const char* __func__ = "local";
            printf("%s", __func__);
        }
    "#;
    let mir_output = setup_mir(source);
    insta::assert_snapshot!(mir_output, @r#"
    type %t0 = i32
    type %t1 = i8
    type %t2 = ptr<%t1>
    type %t3 = void
    type %t4 = [6]%t1
    type %t5 = [6]%t1
    type %t6 = fn(%t2, ...) -> %t0
    type %t7 = [3]%t1
    type %t8 = [3]%t1

    global @.L.str0: [6]i8 = const "local"
    global @.L.str1: [3]i8 = const "%s"

    extern fn printf(%param0: ptr<i8>, ...) -> i32

    fn foo() -> void
    {
      locals {
        %__func__: ptr<i8>
      }

      bb1:
        %__func__ = cast<ptr<i8>>(const @.L.str0)
        call printf(cast<ptr<i8>>(const @.L.str1), %__func__)
        return
    }
    "#);
}
