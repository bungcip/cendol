//! Common utilities for semantic analysis tests.
use crate::ast::Ast;
use crate::driver::artifact::CompilePhase;
use crate::mir::dumper::{MirDumpConfig, MirDumper};
use crate::semantic::TypeRegistry;
use crate::tests::test_utils;

pub fn setup_mir(source: &str) -> String {
    let (driver, result) = test_utils::run_pipeline(source, CompilePhase::Mir);
    let mut out = match result {
        Ok(out) => out,
        Err(_) => panic!("failed to run: {:?}", driver.get_diagnostics()),
    };
    let first = out.units.values_mut().next().expect("No units in output");
    let artifact = first;

    let mir = artifact.mir_program.as_ref().expect("No semantic output available");

    let dump_config = MirDumpConfig { include_header: false };
    let dumper = MirDumper::new(mir, &dump_config);

    dumper.generate_mir_dump().expect("Failed to generate MIR dump")
}

pub fn setup_lowering(source: &str) -> (Ast, TypeRegistry, crate::semantic::SymbolTable) {
    let (driver, result) = test_utils::run_pipeline(source, CompilePhase::SemanticLowering);
    let out = match result {
        Ok(out) => out,
        Err(_) => panic!("failed to run: {:?}", driver.get_diagnostics()),
    };
    let unit = out.units.into_iter().next().expect("No units in output").1;

    (
        unit.ast.expect("No AST available"),
        unit.type_registry.expect("No TypeRegistry available"),
        unit.symbol_table.expect("No SymbolTable available"),
    )
}

pub fn setup_analysis(source: &str) -> (Ast, TypeRegistry, crate::semantic::SymbolTable) {
    let (driver, result) = test_utils::run_pipeline(source, CompilePhase::SemanticLowering);
    let out = match result {
        Ok(out) => out,
        Err(_) => panic!("failed to run: {:?}", driver.get_diagnostics()),
    };
    let unit = out.units.into_iter().next().expect("No units in output").1;

    let mut ast = unit.ast.expect("No AST available");
    let mut registry = unit.type_registry.expect("No TypeRegistry available");
    let symbol_table = unit.symbol_table.expect("No SymbolTable available");

    let mut diagnostics = crate::diagnostic::DiagnosticEngine::from_warnings(&[]);
    let semantic_info =
        crate::semantic::analyzer::visit_ast(&ast, &mut diagnostics, &symbol_table, &mut registry);

    if diagnostics.has_errors() {
        panic!("Semantic analysis failed: {:?}", diagnostics.diagnostics());
    }

    ast.attach_semantic_info(semantic_info);

    (ast, registry, symbol_table)
}

pub fn find_layout<'a>(registry: &'a TypeRegistry, name: &str) -> &'a crate::semantic::types::TypeLayout {
    let s_ty = find_record_type(registry, name);
    s_ty.layout.as_ref().expect("Layout not computed for S")
}

pub fn find_record_type<'a>(registry: &'a TypeRegistry, name: &str) -> &'a crate::semantic::Type {
    registry
        .types
        .iter()
        .find(|ty| {
            if let crate::semantic::TypeKind::Record {
                tag: Some(tag_name), ..
            } = &ty.kind
            {
                tag_name.as_str() == name
            } else {
                false
            }
        })
        .unwrap_or_else(|| panic!("Record type '{}' not found in registry", name))
}

pub fn find_var_decl<'a>(ast: &'a Ast, name: &str) -> &'a crate::ast::VarDeclData {
    ast.kinds
        .iter()
        .find_map(|kind| {
            if let crate::ast::NodeKind::VarDecl(data) = kind
                && data.name.as_str() == name
            {
                Some(data)
            } else {
                None
            }
        })
        .unwrap_or_else(|| panic!("Variable declaration '{}' not found in AST", name))
}

pub fn find_enum_constant(symbol_table: &crate::semantic::SymbolTable, name: &str) -> i64 {
    symbol_table
        .entries
        .iter()
        .find_map(|entry| {
            if entry.name.as_str() == name {
                if let crate::semantic::SymbolKind::EnumConstant { value } = entry.kind {
                    Some(value)
                } else {
                    None
                }
            } else {
                None
            }
        })
        .unwrap_or_else(|| panic!("Enum constant '{}' not found", name))
}
