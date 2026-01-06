//! NameResolver
//!
//! Responsibility
//! - binding identifier name to symbol
//! - binding label name to symbol
//! - binding goto name to symbol
use log::debug;

use crate::ast::{Ast, FunctionData, NodeKind, NodeRef, VarDeclData};
use crate::diagnostic::{DiagnosticEngine, SemanticError};
use crate::semantic::{ArraySizeType, Namespace, ScopeId, SymbolTable, TypeKind, TypeRef, TypeRegistry};
use hashbrown::HashSet;

struct NameResolverCtx<'ast, 'diag> {
    diag: &'diag mut DiagnosticEngine,
    ast: &'ast Ast,
    symbol_table: &'ast SymbolTable,
    registry: &'ast TypeRegistry,
    scope_id: ScopeId,
    deferred_static_asserts: Vec<NodeRef>,
    visited_types: HashSet<TypeRef>,
}

pub fn run_name_resolver(
    ast: &Ast,
    diag: &mut DiagnosticEngine,
    symbol_table: &SymbolTable,
    registry: &TypeRegistry,
) {
    let mut ctx = NameResolverCtx {
        diag,
        ast,
        symbol_table,
        registry,
        scope_id: ScopeId::GLOBAL,
        deferred_static_asserts: Vec::new(),
        visited_types: HashSet::new(),
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

fn visit_type(ctx: &mut NameResolverCtx, type_ref: TypeRef) {
    if !ctx.visited_types.insert(type_ref) {
        return;
    }

    let ty = ctx.registry.get(type_ref);
    // clone kind to avoid borrowing issues if we need to recurse
    let kind = ty.kind.clone();

    match kind {
        TypeKind::Array { element_type, size } => {
            visit_type(ctx, element_type);
            if let ArraySizeType::Variable(expr_ref) = size {
                visit_node(ctx, expr_ref);
            }
        }
        TypeKind::Pointer { pointee } => {
            visit_type(ctx, pointee);
        }
        TypeKind::Function {
            return_type,
            parameters,
            ..
        } => {
            visit_type(ctx, return_type);
            for param in parameters {
                visit_type(ctx, param.param_type.ty);
            }
        }
        TypeKind::Record { members, .. } => {
            for member in members {
                visit_type(ctx, member.member_type.ty);
            }
        }
        // Other types don't contain expressions
        _ => {}
    }
}

fn visit_node(ctx: &mut NameResolverCtx, node_ref: NodeRef) {
    let node = ctx.ast.get_node(node_ref);
    match &node.kind {
        NodeKind::TranslationUnit(decls) => {
            ctx.scope_id = ctx.ast.scope_of(node_ref);
            for decl in decls {
                visit_node(ctx, *decl);
            }
        }
        NodeKind::Function(data) => {
            let FunctionData { body, ty, .. } = data;
            // Visit function type (to handle VLA in parameters)
            visit_type(ctx, *ty);
            visit_node(ctx, *body);
        }
        NodeKind::CompoundStatement(stmts) => {
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
        NodeKind::SizeOfType(ty) => {
            // Visit type for VLAs
            visit_type(ctx, ty.ty);
        }
        NodeKind::AlignOf(ty) => {
            visit_type(ctx, ty.ty);
        }
        NodeKind::Cast(ty, expr) => {
            visit_type(ctx, ty.ty);
            visit_node(ctx, *expr);
        }
        NodeKind::CompoundLiteral(ty, init) => {
            visit_type(ctx, ty.ty);
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
                if let Some(ty) = assoc.ty {
                    visit_type(ctx, ty.ty);
                }
            }
        }
        NodeKind::GnuStatementExpression(compound, result) => {
            visit_node(ctx, *compound);
            visit_node(ctx, *result);
        }
        NodeKind::VaArg(expr, ty) => {
            visit_node(ctx, *expr);
            visit_type(ctx, *ty);
        }
        NodeKind::VarDecl(data) => {
            let VarDeclData { init, ty, .. } = data;
            // Visit type to handle VLA sizes
            visit_type(ctx, ty.ty);
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
