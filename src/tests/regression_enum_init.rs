use super::semantic_common::run_pass;
use crate::driver::artifact::CompilePhase;

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
