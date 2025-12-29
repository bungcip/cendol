use log::debug;

use crate::ast::{Ast, NodeRef};
use crate::diagnostic::DiagnosticEngine;
use crate::semantic::{ScopeId, SymbolTable};

struct TypeResolverCtx<'ast, 'diag> {
    diag: &'diag mut DiagnosticEngine,
    ast: &'ast Ast,
    symbol_table: &'ast SymbolTable,
    scope_id: ScopeId,
}

pub fn run_type_resolver(ast: &Ast, diag: &mut DiagnosticEngine, symbol_table: &SymbolTable) {
    let mut ctx = TypeResolverCtx {
        diag,
        ast,
        symbol_table,
        scope_id: ScopeId::GLOBAL,
    };
    let root = ast.get_root();
    visit_node(&mut ctx, root);
}

fn visit_node(ctx: &mut TypeResolverCtx, node_ref: NodeRef) {
    debug!("Please write it...");
}
