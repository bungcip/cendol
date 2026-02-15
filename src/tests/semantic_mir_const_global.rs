use crate::tests::test_utils;
use insta::assert_yaml_snapshot;

#[test]
fn test_const_global_mir() {
    let source = "
        const int x = 10;
        int y = 20;
    ";

    let outputs = test_utils::run_pipeline_to_mir(source);
    let unit = outputs.units.values().next().expect("No compilation unit found");
    let mir = unit.mir_program.as_ref().expect("MIR generation failed");

    // Sort globals by name for deterministic output
    let mut globals: Vec<_> = mir.globals.values().collect();
    globals.sort_by_key(|g| g.name.to_string());

    // we check is_constant value if it is constant, it will be true
    assert_yaml_snapshot!(globals, @"
    - id: 1
      name: x
      type_id: 1
      is_constant: true
      is_thread_local: false
      linkage: Export
      initial_value: 1
      alignment: ~
    - id: 2
      name: y
      type_id: 1
      is_constant: false
      is_thread_local: false
      linkage: Export
      initial_value: 2
      alignment: ~
    ");
}
