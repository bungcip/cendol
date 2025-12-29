#![allow(dead_code)]
use log::debug;

use crate::ast::{Ast, NodeRef};
use crate::diagnostic::DiagnosticEngine;
use crate::semantic::{ScopeId, SymbolTable};

struct TypeResolverCtx<'ast, 'diag> {
    _diag: &'diag mut DiagnosticEngine,
    _ast: &'ast Ast,
    _symbol_table: &'ast SymbolTable,
    _scope_id: ScopeId,
}

pub fn run_type_resolver(ast: &Ast, diag: &mut DiagnosticEngine, symbol_table: &SymbolTable) {
    let mut _ctx = TypeResolverCtx {
        _diag: diag,
        _ast: ast,
        _symbol_table: symbol_table,
        _scope_id: ScopeId::GLOBAL,
    };
    let _root = ast.get_root();
    // visit_node(&mut _ctx, _root);
}

fn visit_node(_ctx: &mut TypeResolverCtx, _node_ref: NodeRef) {
    debug!("Please write it...");
}
