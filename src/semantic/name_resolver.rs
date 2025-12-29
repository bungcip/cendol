//! NameResolver
//!
//! Responsibility
//! - binding identifier name to symbol
//! - binding label name to symbol
//! - binding goto name to symbol
use log::debug;

use crate::ast::{Ast, FunctionData, NodeKind, NodeRef, VarDeclData};
use crate::diagnostic::{DiagnosticEngine, SemanticError};
use crate::semantic::{Namespace, ScopeId, SymbolTable};

struct NameResolverCtx<'ast, 'diag> {
    diag: &'diag mut DiagnosticEngine,
    ast: &'ast Ast,
    symbol_table: &'ast SymbolTable,
    scope_id: ScopeId,
}

pub fn run_name_resolver(ast: &Ast, diag: &mut DiagnosticEngine, symbol_table: &SymbolTable) {
    let mut ctx = NameResolverCtx {
        diag,
        ast,
        symbol_table,
        scope_id: ScopeId::GLOBAL,
    };
    let root = ast.get_root();
    visit_node(&mut ctx, root);
}

fn visit_node(ctx: &mut NameResolverCtx, node_ref: NodeRef) {
    debug!("solving: {}", node_ref);
    let node = ctx.ast.get_node(node_ref);
    match &node.kind {
        NodeKind::TranslationUnit(decls) => {
            ctx.scope_id = ctx.ast.scope_of(node_ref);
            for decl in decls {
                visit_node(ctx, *decl);
            }
        }
        NodeKind::Function(data) => {
            let FunctionData { body, .. } = data;
            visit_node(ctx, *body);
        }
        NodeKind::CompoundStatement(stmts) => {
            ctx.scope_id = ctx.ast.scope_of(node_ref);
            for stmt in stmts {
                visit_node(ctx, *stmt);
            }
        }
        NodeKind::For(stmt) => {
            ctx.scope_id = ctx.ast.scope_of(node_ref);
            if let Some(init) = stmt.init {
                visit_node(ctx, init)
            }
            if let Some(cond) = stmt.condition {
                visit_node(ctx, cond)
            }
            if let Some(incr) = stmt.increment {
                visit_node(ctx, incr);
            }
            visit_node(ctx, stmt.body);
        }
        // Other nodes that might contain statements/declarations
        NodeKind::If(if_stmt) => {
            visit_node(ctx, if_stmt.condition);
            visit_node(ctx, if_stmt.then_branch);
            if let Some(else_branch) = if_stmt.else_branch {
                visit_node(ctx, else_branch);
            }
        }
        NodeKind::While(while_stmt) => {
            visit_node(ctx, while_stmt.condition);
            visit_node(ctx, while_stmt.body);
        }
        NodeKind::DoWhile(body, condition) => {
            visit_node(ctx, *body);
            visit_node(ctx, *condition);
        }
        NodeKind::Switch(_, body) => {
            visit_node(ctx, *body);
        }
        NodeKind::Return(expr) => {
            if let Some(expr) = expr {
                visit_node(ctx, *expr)
            }
        }
        NodeKind::Assignment(_, left, right) => {
            visit_node(ctx, *left);
            visit_node(ctx, *right);
        }
        NodeKind::IndexAccess(array, index) => {
            visit_node(ctx, *array);
            visit_node(ctx, *index);
        }
        NodeKind::MemberAccess(calle, ..) => {
            visit_node(ctx, *calle);
        }
        NodeKind::BinaryOp(_, left, right) => {
            visit_node(ctx, *left);
            visit_node(ctx, *right);
        }
        NodeKind::UnaryOp(_, expr) => {
            visit_node(ctx, *expr);
        }
        NodeKind::ExpressionStatement(expr) => {
            if let Some(expr) = expr {
                visit_node(ctx, *expr);
            }
        }
        NodeKind::FunctionCall(calle, args) => {
            visit_node(ctx, *calle);
            for arg in args {
                visit_node(ctx, *arg);
            }
        }
        NodeKind::ListInitializer(inits) => {
            for init in inits {
                visit_node(ctx, init.initializer);
            }
        }
        NodeKind::VarDecl(data) => {
            let VarDeclData { init, .. } = data;
            if let Some(init) = init {
                visit_node(ctx, *init);
            }
        }

        NodeKind::Ident(name, resolved) => {
            if let Some(sym) = ctx.symbol_table.lookup(*name, ctx.scope_id, Namespace::Ordinary) {
                resolved.set(Some(sym.0));
            } else {
                debug!("ndak nemu {}!", name);
                ctx.diag.report(SemanticError::UndeclaredIdentifier {
                    name: *name,
                    span: node.span,
                });
            }
        }
        NodeKind::Goto(name, resolved) => {
            if let Some(sym) = ctx.symbol_table.lookup(*name, ctx.scope_id, Namespace::Label) {
                resolved.set(Some(sym.0));
            } else {
                ctx.diag.report(SemanticError::UndeclaredIdentifier {
                    name: *name,
                    span: node.span,
                });
            }
        }
        NodeKind::Label(name, stmt, resolved) => {
            if let Some(sym) = ctx.symbol_table.lookup(*name, ctx.scope_id, Namespace::Label) {
                resolved.set(Some(sym.0));
            } else {
                ctx.diag.report(SemanticError::UndeclaredIdentifier {
                    name: *name,
                    span: node.span,
                });
            }

            visit_node(ctx, *stmt);
        }

        n => {
            debug!("ignoring {} {:?}", node_ref, n);
        }
    }
}
