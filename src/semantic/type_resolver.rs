use crate::{
    ast::{Ast, FunctionData, NodeKind, NodeRef, Type, TypeKind, TypeRef, UnaryOp},
    diagnostic::{DiagnosticEngine, SemanticError},
    semantic::{symbol_table::SymbolTable, ScopeId},
};
use std::cell::Cell;

/// The `TypeResolver` is a semantic analysis pass that walks the AST and
/// determines the type of every expression. It stores the resolved type

pub struct TypeResolver<'ast, 'diag> {
    diag: &'diag mut DiagnosticEngine,
    ast: &'ast mut Ast,
    symbol_table: &'ast SymbolTable,
    scope_map: Vec<Option<ScopeId>>,
    current_scope: Cell<ScopeId>,

    // Cached primitive types
    type_char: TypeRef,
    type_uchar: TypeRef,
    type_short: TypeRef,
    type_ushort: TypeRef,
    type_int: TypeRef,
    type_uint: TypeRef,
    type_long: TypeRef,
    type_ulong: TypeRef,
    type_llong: TypeRef,
    type_ullong: TypeRef,
    type_float: TypeRef,
    type_double: TypeRef,
}

impl<'ast, 'diag> TypeResolver<'ast, 'diag> {
    /// Create a new `TypeResolver` instance.
    pub fn new(
        diag: &'diag mut DiagnosticEngine,
        ast: &'ast mut Ast,
        symbol_table: &'ast SymbolTable,
        scope_map: Vec<Option<ScopeId>>,
    ) -> Self {
        let type_char = ast.push_type(Type::new(TypeKind::Char { is_signed: true }));
        let type_uchar = ast.push_type(Type::new(TypeKind::Char { is_signed: false }));
        let type_short = ast.push_type(Type::new(TypeKind::Short { is_signed: true }));
        let type_ushort = ast.push_type(Type::new(TypeKind::Short { is_signed: false }));
        let type_int = ast.push_type(Type::new(TypeKind::Int { is_signed: true }));
        let type_uint = ast.push_type(Type::new(TypeKind::Int { is_signed: false }));
        let type_long = ast.push_type(Type::new(TypeKind::Long {
            is_signed: true,
            is_long_long: false,
        }));
        let type_ulong = ast.push_type(Type::new(TypeKind::Long {
            is_signed: false,
            is_long_long: false,
        }));
        let type_llong = ast.push_type(Type::new(TypeKind::Long {
            is_signed: true,
            is_long_long: true,
        }));
        let type_ullong = ast.push_type(Type::new(TypeKind::Long {
            is_signed: false,
            is_long_long: true,
        }));
        let type_float = ast.push_type(Type::new(TypeKind::Float));
        let type_double = ast.push_type(Type::new(TypeKind::Double { is_long_double: false }));

        Self {
            diag,
            ast,
            symbol_table,
            scope_map,
            current_scope: Cell::new(ScopeId::GLOBAL),
            type_char,
            type_uchar,
            type_short,
            type_ushort,
            type_int,
            type_uint,
            type_long,
            type_ulong,
            type_llong,
            type_ullong,
            type_float,
            type_double,
        }
    }

    /// Run the type resolver pass, starting from the given node.
    pub fn run(&mut self, root: NodeRef) {
        self.visit_node(root);
    }

    /// The main visitor function that dispatches to the correct `visit_*` method.
    fn visit_node(&mut self, node_ref: NodeRef) {
        let Some(scope_id) = self.scope_map[node_ref.get() as usize - 1] else {
            return;
        };

        let old_scope = self.current_scope.replace(scope_id);
        let node_kind = self.ast.get_node(node_ref).kind.clone();

        match &node_kind {
            NodeKind::Function(func_data) => self.visit_function(func_data),
            NodeKind::If(if_stmt) => {
                self.visit_node(if_stmt.condition);
                self.visit_node(if_stmt.then_branch);
                if let Some(else_branch) = if_stmt.else_branch {
                    self.visit_node(else_branch);
                }
            }
            NodeKind::While(while_stmt) => {
                self.visit_node(while_stmt.condition);
                self.visit_node(while_stmt.body);
            }
            NodeKind::For(for_stmt) => {
                if let Some(init) = for_stmt.init {
                    self.visit_node(init);
                }
                if let Some(cond) = for_stmt.condition {
                    self.visit_node(cond);
                }
                if let Some(inc) = for_stmt.increment {
                    self.visit_node(inc);
                }
                self.visit_node(for_stmt.body);
            }
            NodeKind::CompoundStatement(nodes) => {
                for node in nodes {
                    self.visit_node(*node);
                }
            }
            NodeKind::DeclarationList(decls) => {
                for decl in decls {
                    self.visit_node(*decl);
                }
            }
            NodeKind::TranslationUnit(units) => {
                for unit in units {
                    self.visit_node(*unit);
                }
            }
            _ => {
                self.resolve_expr_type(node_ref);
            }
        };

        self.current_scope.set(old_scope);
    }

    /// Visit a function definition, including its body.
    fn visit_function(&mut self, func: &FunctionData) {
        self.visit_node(func.body);
    }

    /// Resolve the type of an expression node and store it.
    fn resolve_expr_type(&mut self, node_ref: NodeRef) -> TypeRef {
        let node_kind = self.ast.get_node(node_ref).kind.clone();
        let node_span = self.ast.get_node(node_ref).span;

        let ty = match &node_kind {
            NodeKind::LiteralInt(_) => self.type_int,
            NodeKind::LiteralFloat(_) => self.type_double,
            NodeKind::LiteralString(_) => self.ast.push_type(Type::new(TypeKind::Pointer {
                pointee: self.type_char,
            })),
            NodeKind::LiteralChar(_) => self.type_char,

            NodeKind::Ident(name, symbol_cell) => {
                if let Some((symbol_ref, _)) = self.symbol_table.lookup_symbol(*name) {
                    symbol_cell.set(Some(symbol_ref));
                    let symbol = self.symbol_table.get_symbol(symbol_ref);
                    symbol.type_info
                } else {
                    self.diag.report(SemanticError::UndeclaredIdentifier {
                        name: *name,
                        span: node_span,
                    });
                    self.type_int
                }
            }

            NodeKind::Assignment(_, lhs, rhs) => {
                let _ = self.resolve_expr_type(*lhs);
                let _ = self.resolve_expr_type(*rhs);
                self.type_int
            }

            NodeKind::UnaryOp(op, operand_ref) => {
                let operand_ty = self.resolve_expr_type(*operand_ref);
                match op {
                    UnaryOp::AddrOf => self.ast.push_type(Type::new(TypeKind::Pointer { pointee: operand_ty })),
                    UnaryOp::Deref => {
                        let operand_node = self.ast.get_type(operand_ty);
                        if let TypeKind::Pointer { pointee } = operand_node.kind {
                            pointee
                        } else {
                            self.diag.report(SemanticError::InvalidIndirection { span: node_span });
                            self.type_int
                        }
                    }
                    _ => operand_ty,
                }
            }

            NodeKind::BinaryOp(_op, left_ref, right_ref) => {
                let left_ty = self.resolve_expr_type(*left_ref);
                let right_ty = self.resolve_expr_type(*right_ref);
                self.usual_arithmetic_conversions(left_ty, right_ty)
            }

            NodeKind::FunctionCall(func_ref, _) => {
                let func_ty = self.resolve_expr_type(*func_ref);
                let func_type_node = self.ast.get_type(func_ty);
                match func_type_node.kind {
                    TypeKind::Function { return_type, .. } => return_type,
                    TypeKind::Pointer { pointee } => {
                        let pointee_node = self.ast.get_type(pointee);
                        if let TypeKind::Function { return_type, .. } = pointee_node.kind {
                            return_type
                        } else {
                            self.type_int
                        }
                    }
                    _ => self.type_int,
                }
            }

            NodeKind::MemberAccess(obj_ref, field_name, is_arrow, resolved_sym) => {
                let mut obj_ty = self.resolve_expr_type(*obj_ref);
                if *is_arrow {
                    if let TypeKind::Pointer { pointee } = self.ast.get_type(obj_ty).kind {
                        obj_ty = pointee;
                    } else {
                        // Error: indirection on non-pointer
                        return self.type_int;
                    }
                }

                if let Some(scope_id) = self.symbol_table.find_scope_for_record(obj_ty) {
                    let scope = self.symbol_table.get_scope(scope_id);
                    if let Some(sym_ref) = scope.symbols.get(field_name) {
                        resolved_sym.set(Some(*sym_ref));
                        let symbol = self.symbol_table.get_symbol(*sym_ref);
                        symbol.type_info
                    } else {
                        // Error: field not found
                        self.diag.report(SemanticError::UndeclaredIdentifier {
                            name: *field_name,
                            span: node_span,
                        });
                        self.type_int
                    }
                } else {
                    // Error: not a struct/union
                    self.type_int
                }
            }
            _ => self.type_int,
        };

        self.ast.get_node(node_ref).resolved_type.set(Some(ty));
        ty
    }
    fn usual_arithmetic_conversions(&self, left: TypeRef, right: TypeRef) -> TypeRef {
        let left_kind = &self.ast.get_type(left).kind;
        let right_kind = &self.ast.get_type(right).kind;

        if *left_kind == (TypeKind::Double { is_long_double: false })
            || *right_kind == (TypeKind::Double { is_long_double: false })
        {
            return self.type_double;
        }

        if *left_kind == TypeKind::Float || *right_kind == TypeKind::Float {
            return self.type_float;
        }

        let left_promoted = self.integer_promotion(left);
        let right_promoted = self.integer_promotion(right);

        let left_promoted_kind = &self.ast.get_type(left_promoted).kind;
        let right_promoted_kind = &self.ast.get_type(right_promoted).kind;

        if left_promoted == right_promoted {
            return left_promoted;
        }

        match (left_promoted_kind, right_promoted_kind) {
            (TypeKind::Int { .. }, TypeKind::Int { .. }) => {
                if self.is_unsigned(left_promoted) || self.is_unsigned(right_promoted) {
                    self.type_uint
                } else {
                    self.type_int
                }
            }
            (TypeKind::Long { .. }, TypeKind::Long { .. }) => {
                if self.is_unsigned(left_promoted) || self.is_unsigned(right_promoted) {
                    self.type_ulong
                } else {
                    self.type_long
                }
            }
            _ => left_promoted,
        }
    }

    fn integer_promotion(&self, ty_ref: TypeRef) -> TypeRef {
        let kind = &self.ast.get_type(ty_ref).kind;
        match kind {
            TypeKind::Bool | TypeKind::Char { .. } | TypeKind::Short { .. } => self.type_int,
            _ => ty_ref,
        }
    }

    fn is_unsigned(&self, ty_ref: TypeRef) -> bool {
        matches!(
            self.ast.get_type(ty_ref).kind,
            TypeKind::Char { is_signed: false }
                | TypeKind::Short { is_signed: false }
                | TypeKind::Int { is_signed: false }
                | TypeKind::Long { is_signed: false, .. }
        )
    }
}
