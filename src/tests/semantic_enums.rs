use crate::driver::artifact::CompilePhase;
use crate::tests::semantic_common::{find_enum_constant, setup_lowering};

#[test]
fn test_enum_constant_expression_basic() {
    let source = r#"
    enum E {
        A = 1 + 2,
        B = 10,
        C = 5 * 2
    };
    "#;

    let (_, _, symbol_table) = setup_lowering(source);

    assert_eq!(find_enum_constant(&symbol_table, "A"), 3, "Enum A should be 3");
    assert_eq!(find_enum_constant(&symbol_table, "B"), 10, "Enum B should be 10");
    assert_eq!(find_enum_constant(&symbol_table, "C"), 10, "Enum C should be 10");
}

#[test]
fn test_enum_constant_expression_reference() {
    let source = r#"
    enum E {
        A = 10,
        B = A + 5
    };
    "#;

    let (_, _, symbol_table) = setup_lowering(source);

    // This is expected to fail or be incorrect with current implementation
    assert_eq!(find_enum_constant(&symbol_table, "B"), 15, "Enum B should be 15");
}
use crate::tests::test_utils::run_pass;

#[test]
fn test_enum_init_with_other_enum() {
    let source = r#"
enum A { A1 = 10 };
enum B { B1 = A1 };

int main() {
    return 0;
}
"#;
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_enum_init_with_other_enum_indirect() {
    let source = r#"
enum tree_code {
  SOME_CODE = 148,
  LAST_AND_UNUSED_TREE_CODE
};
enum c_tree_code {
  C_DUMMY_TREE_CODE = LAST_AND_UNUSED_TREE_CODE,
  STMT_EXPR,
  LAST_C_TREE_CODE
};
enum cplus_tree_code {
  CP_DUMMY_TREE_CODE = LAST_C_TREE_CODE,
  AMBIG_CONV,
  LAST_CPLUS_TREE_CODE
};

int main() {
    return 0;
}
"#;
    run_pass(source, CompilePhase::Mir);
}
