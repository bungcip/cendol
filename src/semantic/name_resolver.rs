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
    deferred_static_asserts: Vec<NodeRef>,
}

pub(crate) fn run_name_resolver(ast: &Ast, diag: &mut DiagnosticEngine, symbol_table: &SymbolTable) {
    let mut ctx = NameResolverCtx {
        diag,
        ast,
        symbol_table,
        scope_id: ScopeId::GLOBAL,
        deferred_static_asserts: Vec::new(),
    };
    let root = ast.get_root();
    visit_node(&mut ctx, root);

    // Process any remaining deferred static asserts at file scope
    for assert_ref in ctx.deferred_static_asserts.drain(..).collect::<Vec<_>>() {
        if let NodeKind::StaticAssert(cond, _) = ctx.ast.get_node(assert_ref).kind.clone() {
            visit_node(&mut ctx, cond);
        }
    }
}

fn visit_node(ctx: &mut NameResolverCtx, node_ref: NodeRef) {
    let node = ctx.ast.get_node(node_ref);
    match &node.kind {
        NodeKind::TranslationUnit(decls) => {
            let prev_scope = ctx.scope_id;
            ctx.scope_id = ctx.ast.scope_of(node_ref);
            for decl in decls {
                visit_node(ctx, *decl);
            }
            ctx.scope_id = prev_scope;
        }
        NodeKind::Function(data) => {
            let FunctionData { body, .. } = data;
            visit_node(ctx, *body);
        }
        NodeKind::CompoundStatement(stmts) => {
            let prev_scope = ctx.scope_id;
            ctx.scope_id = ctx.ast.scope_of(node_ref);
            let deferred_count = ctx.deferred_static_asserts.len();
            for stmt in stmts {
                visit_node(ctx, *stmt);
            }

            // Process asserts deferred in this scope
            let asserts_in_scope: Vec<_> = ctx.deferred_static_asserts.drain(deferred_count..).collect();
            for assert_ref in asserts_in_scope {
                if let NodeKind::StaticAssert(cond, _) = ctx.ast.get_node(assert_ref).kind.clone() {
                    visit_node(ctx, cond);
                }
            }
            ctx.scope_id = prev_scope;
        }
        NodeKind::For(stmt) => {
            let prev_scope = ctx.scope_id;
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
            ctx.scope_id = prev_scope;
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
        NodeKind::Case(expr, stmt) => {
            visit_node(ctx, *expr);
            visit_node(ctx, *stmt);
        }
        NodeKind::CaseRange(start, end, stmt) => {
            visit_node(ctx, *start);
            visit_node(ctx, *end);
            visit_node(ctx, *stmt);
        }
        NodeKind::Default(stmt) => {
            visit_node(ctx, *stmt);
        }
        NodeKind::Switch(expr, body) => {
            visit_node(ctx, *expr);
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
        NodeKind::PostIncrement(expr) => {
            visit_node(ctx, *expr);
        }
        NodeKind::PostDecrement(expr) => {
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
        NodeKind::InitializerList(inits) => {
            for init in inits {
                visit_node(ctx, init.initializer);
                for designator in &init.designation {
                    if let crate::ast::Designator::ArrayIndex(idx_expr) = designator {
                        visit_node(ctx, *idx_expr);
                    }
                }
            }
        }
        // More expression nodes
        NodeKind::SizeOfExpr(expr) => {
            visit_node(ctx, *expr);
        }
        NodeKind::SizeOfType(_) => {
            // Already resolved
        }
        NodeKind::AlignOf(_) => {
            // Already resolved
        }
        NodeKind::Cast(_, expr) => {
            visit_node(ctx, *expr);
        }
        NodeKind::CompoundLiteral(_, init) => {
            visit_node(ctx, *init);
        }
        NodeKind::TernaryOp(cond, then_branch, else_branch) => {
            visit_node(ctx, *cond);
            visit_node(ctx, *then_branch);
            visit_node(ctx, *else_branch);
        }
        NodeKind::GenericSelection(ctrl, assocs) => {
            visit_node(ctx, *ctrl);
            for assoc in assocs {
                visit_node(ctx, assoc.result_expr);
            }
        }
        NodeKind::GnuStatementExpression(compound, result) => {
            visit_node(ctx, *compound);
            visit_node(ctx, *result);
        }
        NodeKind::VaArg(expr, _) => {
            visit_node(ctx, *expr);
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

        NodeKind::StaticAssert(..) => {
            ctx.deferred_static_asserts.push(node_ref);
        }
        n => {
            debug!("ignoring {} {:?}", node_ref, n);
        }
    }
}
