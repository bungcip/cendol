//! Common utilities for semantic analysis tests.
use crate::ast::{Ast, NameId, NodeKind, VarDecl};
use crate::diagnostic::DiagnosticEngine;
use crate::driver::artifact::CompilePhase;
use crate::mir::dumper::{MirDumpConfig, MirDumper};
use crate::semantic::{SymbolKind, SymbolTable, Type, TypeKind, TypeLayout, TypeRegistry};
use crate::tests::test_utils::run_pipeline;

pub(crate) fn setup_mir(source: &str) -> String {
    let (driver, result) = run_pipeline(source, CompilePhase::Mir);
    let mut out = result.unwrap_or_else(|_| panic!("failed to run: {:?}", driver.get_diagnostics()));
    let artifact = out.units.values_mut().next().expect("No units in output");

    let mir = artifact.mir_program.as_ref().expect("No semantic output available");
    let dumper = MirDumper::new(mir, &MirDumpConfig { include_header: false });

    dumper.generate_mir_dump().expect("Failed to generate MIR dump")
}

pub(crate) fn setup_lowering(source: &str) -> (Ast, TypeRegistry, SymbolTable) {
    let (driver, result) = run_pipeline(source, CompilePhase::SemanticLowering);
    let out = result.unwrap_or_else(|_| panic!("failed to run: {:?}", driver.get_diagnostics()));
    let unit = out.units.into_values().next().expect("No units in output");

    (
        unit.ast.expect("No AST available"),
        unit.type_registry.expect("No TypeRegistry available"),
        unit.symbol_table.expect("No SymbolTable available"),
    )
}

pub(crate) fn setup_analysis(source: &str) -> (Ast, TypeRegistry, SymbolTable) {
    let (driver, result) = run_pipeline(source, CompilePhase::SemanticLowering);
    let out = result.unwrap_or_else(|_| panic!("failed to run: {:?}", driver.get_diagnostics()));
    let unit = out.units.into_values().next().expect("No units in output");

    let mut ast = unit.ast.expect("No AST available");
    let mut registry = unit.type_registry.expect("No TypeRegistry available");
    let symbol_table = unit.symbol_table.expect("No SymbolTable available");

    let mut diag = DiagnosticEngine::from_warnings(&[]);
    let semantic_info = crate::semantic::analyzer::visit_ast(
        &ast,
        &mut diag,
        &symbol_table,
        &mut registry,
        &crate::lang_options::LangOptions::default(),
        &driver.sm,
    );

    if diag.has_errors() {
        panic!("Semantic analysis failed: {:?}", diag.diagnostics);
    }

    ast.attach_semantic_info(semantic_info);

    (ast, registry, symbol_table)
}

pub(crate) fn find_layout<'a>(registry: &'a TypeRegistry, name: &str) -> &'a TypeLayout {
    let s_ty = find_record_type(registry, name);
    s_ty.layout
        .as_ref()
        .unwrap_or_else(|| panic!("Layout not computed for '{name}'"))
}

pub(crate) fn find_record_type<'a>(registry: &'a TypeRegistry, name: &str) -> &'a Type {
    let sym = NameId::new(name);
    registry
        .types
        .iter()
        .find(|ty| matches!(ty.kind, TypeKind::Record { tag: Some(tag), .. } if tag == sym))
        .unwrap_or_else(|| panic!("Record type '{name}' not found in registry"))
}

pub(crate) fn find_var_decl<'a>(ast: &'a Ast, symbol_table: &SymbolTable, name: &str) -> &'a VarDecl {
    let sym = NameId::new(name);
    ast.kinds
        .iter()
        .find_map(|kind| match kind {
            NodeKind::VarDecl(data) if symbol_table.get_symbol(data.symbol).name == sym => Some(data),
            _ => None,
        })
        .unwrap_or_else(|| panic!("Variable declaration '{name}' not found in AST"))
}

pub(crate) fn find_enum_constant(symbol_table: &SymbolTable, name: &str) -> i64 {
    let sym = NameId::new(name);
    symbol_table
        .entries
        .iter()
        .find_map(|entry| match entry.kind {
            SymbolKind::EnumConstant { value } if entry.name == sym => Some(value),
            _ => None,
        })
        .unwrap_or_else(|| panic!("Enum constant '{name}' not found"))
}
