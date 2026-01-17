use crate::driver::CompilerDriver;
use crate::driver::artifact::CompilePhase;
use crate::driver::cli::CompileConfig;
use crate::semantic::SymbolKind;

#[test]
fn test_enum_constant_expression_basic() {
    let source = r#"
    enum E {
        A = 1 + 2,
        B = 10,
        C = 5 * 2
    };
    "#;

    let config = CompileConfig::from_virtual_file(source.to_string(), CompilePhase::SemanticLowering);
    let mut driver = CompilerDriver::from_config(config);
    let result = driver.run_pipeline(CompilePhase::SemanticLowering);

    assert!(result.is_ok(), "Compilation failed: {:?}", result.err());
    let outputs = result.unwrap();
    let unit = outputs.units.values().next().unwrap();
    let symbol_table = unit.symbol_table.as_ref().unwrap();

    let mut a_val = None;
    let mut b_val = None;
    let mut c_val = None;

    for entry in &symbol_table.entries {
        let name = entry.name.to_string();
        if name == "A" {
            if let SymbolKind::EnumConstant { value } = entry.kind {
                a_val = Some(value);
            }
        } else if name == "B" {
            if let SymbolKind::EnumConstant { value } = entry.kind {
                b_val = Some(value);
            }
        } else if name == "C"
            && let SymbolKind::EnumConstant { value } = entry.kind {
                c_val = Some(value);
            }
    }

    assert_eq!(a_val, Some(3), "Enum A should be 3");
    assert_eq!(b_val, Some(10), "Enum B should be 10");
    assert_eq!(c_val, Some(10), "Enum C should be 10");
}

#[test]
fn test_enum_constant_expression_reference() {
    let source = r#"
    enum E {
        A = 10,
        B = A + 5
    };
    "#;

    let config = CompileConfig::from_virtual_file(source.to_string(), CompilePhase::SemanticLowering);
    let mut driver = CompilerDriver::from_config(config);
    let result = driver.run_pipeline(CompilePhase::SemanticLowering);

    assert!(result.is_ok(), "Compilation failed: {:?}", result.err());
    let outputs = result.unwrap();
    let unit = outputs.units.values().next().unwrap();
    let symbol_table = unit.symbol_table.as_ref().unwrap();

    let mut b_val = None;

    for entry in &symbol_table.entries {
        let name = entry.name.to_string();
        if name == "B"
            && let SymbolKind::EnumConstant { value } = entry.kind {
                b_val = Some(value);
            }
    }

    // This is expected to fail or be incorrect with current implementation
    assert_eq!(b_val, Some(15), "Enum B should be 15");
}
