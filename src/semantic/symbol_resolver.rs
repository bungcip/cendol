//! an ast visitor that resolves symbols and scopes
use crate::{
    ast::*,
    diagnostic::{DiagnosticEngine, SemanticError},
    semantic::{
        symbol_table::{Namespace, Symbol, SymbolTable},
        Scope, ScopeId, ScopeKind, SymbolKind, SymbolRef,
    },
};

pub fn run_symbol_resolver(
    ast: &mut Ast,
    diag: &mut DiagnosticEngine,
    symbol_table: &mut SymbolTable,
) -> Vec<Option<ScopeId>> {
    let nodes_len = ast.nodes.len();
    let mut ctx = SymbolResolverContext {
        ast,
        diag,
        symbol_table,
        scope_map: vec![None; nodes_len],
    };

    let root_node_ref = ctx.ast.get_root();
    ctx.scope_map[root_node_ref.get() as usize - 1] = Some(ScopeId::GLOBAL);
    let mut resolver = SymbolResolver {};
    resolver.visit_node(&mut ctx, root_node_ref);

    ctx.scope_map
}

struct SymbolResolver {}

struct SymbolResolverContext<'a> {
    ast: &'a mut Ast,
    diag: &'a mut DiagnosticEngine,
    symbol_table: &'a mut SymbolTable,
    scope_map: Vec<Option<ScopeId>>,
}

impl SymbolResolverContext<'_> {
    fn report_error(&mut self, error: SemanticError) {
        self.diag.report(error);
    }
}

impl SymbolResolver {
    fn visit_node(&mut self, ctx: &mut SymbolResolverContext, node_ref: NodeRef) {
        ctx.scope_map[node_ref.get() as usize - 1] = Some(ctx.symbol_table.current_scope());
        let node_kind = ctx.ast.get_node(node_ref).kind.clone();
        match node_kind {
            NodeKind::TranslationUnit(decls) => {
                for decl in decls {
                    self.visit_node(ctx, decl);
                }
            }
            NodeKind::Function(func_data) => {
                let func_scope = ctx.symbol_table.push_scope();
                let scope = ctx.symbol_table.get_scope_mut(func_scope);
                scope.kind = ScopeKind::Function(func_data.symbol);

                for param in &func_data.params {
                    let symbol = Symbol {
                        name: ctx.symbol_table.get_symbol(param.symbol).name,
                        kind: crate::semantic::symbol_table::SymbolKind::Variable {
                            is_global: false,
                            initializer: None,
                        },
                        type_info: param.ty,
                        storage_class: None,
                        scope_id: func_scope,
                        def_span: ctx.ast.get_node(node_ref).span,
                        def_state: crate::semantic::symbol_table::DefinitionState::Defined,
                        is_referenced: false,
                        is_completed: true,
                    };
                    ctx.symbol_table.add_symbol(symbol.name, symbol);
                }

                self.visit_node(ctx, func_data.body);
                ctx.symbol_table.pop_scope();
            }
            NodeKind::CompoundStatement(items) => {
                ctx.symbol_table.push_scope();
                for item in items {
                    self.visit_node(ctx, item);
                }
                ctx.symbol_table.pop_scope();
            }
            _ => {}
        }
    }
}
