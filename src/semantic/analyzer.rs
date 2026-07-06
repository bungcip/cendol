use crate::{
    ast::{
        NodeRef,
        literal::{LitKind, LitRef, LitVal},
        nodes::*,
        *,
    },
    diagnostic::{DiagnosticEngine, DiagnosticLevel},
    lang_options::{CStandard, LangOptions},
    semantic::{
        ArraySizeType, BuiltinFunctionKind, BuiltinType, FunctionParam, QualType, RecordMember, SymbolKind, SymbolRef,
        SymbolTable, TypeKind, TypeQualifiers, TypeRef, TypeRegistry,
        const_eval::ConstEvalCtx,
        conversions::{integer_promotion, usual_arithmetic_conversions},
        errors::{SemanticDiag, SemanticError},
        literal_utils::{get_string_builtin_type, get_string_literal_size},
        types::TypeClass,
    },
};

use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::SmallVec;
use std::sync::Arc;

struct CaseRangeInterval {
    start: i64,
    end: i64,
}

impl CaseRangeInterval {
    fn overlaps(&self, other: &Self) -> bool {
        self.start <= other.end && other.start <= self.end
    }
}

struct SwitchCtx {
    cases: SmallVec<[CaseRangeInterval; 8]>,
    default_seen: bool,
    cond_type: QualType,
    orig_cond_type: QualType,
    vla_state: (NodeRef, usize),
}

/// Internal task used to extract information from TypeKind without cloning it.
enum TypeAnalysisTask {
    Record(Arc<[RecordMember]>, bool),
    Array(TypeRef, ArraySizeType),
    Function {
        return_type: TypeRef,
        parameters: Arc<[FunctionParam]>,
        is_variadic: bool,
    },
    None,
}

/// Context for the current function being analyzed.
#[derive(Debug, Clone, Copy)]
struct FunctionCtx {
    ret_type: QualType,
    name: NameId,
    is_noreturn: bool,
}

/// Side table containing semantic information for AST nodes.
/// Parallel vectors indexed by node index (NodeRef.index()).
#[derive(Debug, Clone, Default)]
pub struct SemanticInfo {
    pub types: Vec<Option<QualType>>,
    // Bolt ⚡: Optimization: Use a sparse HashMap for conversions to save memory.
    // Most nodes do not have implicit conversions.
    pub conversions: FxHashMap<usize, SmallVec<[Conversion; 1]>>,
    pub value_categories: Vec<ValueCategory>,
    pub generic_selections: FxHashMap<usize, NodeRef>, // Maps NodeIndex of GenericSelection to selected result_expr
    pub choose_expressions: FxHashMap<usize, NodeRef>, // Maps NodeIndex of BuiltinChooseExpr to selected branch
    pub offsetof_results: FxHashMap<usize, i64>,       // Maps NodeIndex of BuiltinOffsetof to computed offset
    pub anonymous_tags: FxHashMap<TypeRef, NameId>,    // Maps TypeRef to its stable anonymous name ($anonN)
}

impl SemanticInfo {
    fn with_capacity(n: usize) -> Self {
        Self {
            types: vec![None; n],
            conversions: FxHashMap::default(),
            value_categories: vec![ValueCategory::RValue; n],
            generic_selections: FxHashMap::default(),
            choose_expressions: FxHashMap::default(),
            offsetof_results: FxHashMap::default(),
            anonymous_tags: FxHashMap::default(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ValueCategory {
    LValue,
    #[default]
    RValue,
}

/// Implicit Conversions
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Conversion {
    /// LValue → RValue
    LValueToRValue,

    /// Array/function → pointer
    PointerDecay { to: TypeRef },

    /// char/short → int (store types as TypeRef)
    IntegerPromotion { from: TypeRef, to: TypeRef },

    /// int → long, unsigned → unsigned long, etc
    IntegerCast { from: TypeRef, to: TypeRef },

    /// float -> double, etc
    FloatingCast { from: TypeRef, to: TypeRef },

    /// real -> complex or complex -> complex (with precision change)
    ComplexCast { from: TypeRef, to: TypeRef },

    /// void* ↔ T*
    PointerCast { from: TypeRef, to: TypeRef },

    /// add/remove const/volatile
    QualifierAdjust { from: TypeQualifiers, to: TypeQualifiers },

    /// 0 / NULL → T*
    NullPointerConstant,
}

/// Run Semantic Analyzer in our AST and return analysist result in SemanticInfo
/// which contains resolved type, conversion table, and value category
pub(crate) fn visit_ast(
    ast: &Ast,
    diag: &mut DiagnosticEngine,
    symbol_table: &SymbolTable,
    registry: &mut TypeRegistry,
    lang_opts: &LangOptions,
    source_manager: &crate::source_manager::SourceManager,
) -> SemanticInfo {
    let mut semantic_info = SemanticInfo::with_capacity(ast.kinds.len());
    let mut resolver = SemanticAnalyzer {
        ast,
        diag,
        symbol_table,
        registry,
        semantic_info: &mut semantic_info,
        current_function: None,
        deferred_checks: Vec::new(),
        loop_depth: 0,
        switch_stack: SmallVec::new(),
        checked_types: FxHashSet::default(),
        active_vlas: Vec::new(),
        goto_vla_state: Vec::new(),
        label_vla_state: FxHashMap::default(),
        lang_opts,
        source_manager,
    };
    let root = ast.get_root();
    resolver.visit_node(root);
    // Important: process deferred checks BEFORE returning so static asserts
    // see the results of choose_expr and other semantic info.
    resolver.process_deferred_checks();
    semantic_info
}

enum DeferredCheck {
    StaticAssert(NodeRef),
}

struct SemanticAnalyzer<'a> {
    ast: &'a Ast,
    diag: &'a mut DiagnosticEngine,
    symbol_table: &'a SymbolTable,
    registry: &'a mut TypeRegistry,
    semantic_info: &'a mut SemanticInfo,
    current_function: Option<FunctionCtx>,
    deferred_checks: Vec<DeferredCheck>,
    loop_depth: usize,
    // Bolt ⚡: Use SmallVec for switch state to avoid heap allocations for nested switches.
    switch_stack: SmallVec<[SwitchCtx; 4]>,
    checked_types: FxHashSet<TypeRef>,
    active_vlas: Vec<NodeRef>,
    goto_vla_state: Vec<(NodeRef, Vec<NodeRef>)>,
    label_vla_state: FxHashMap<SymbolRef, (SourceSpan, Vec<NodeRef>)>,
    lang_opts: &'a crate::lang_options::LangOptions,
    source_manager: &'a crate::source_manager::SourceManager,
}

impl<'a> SemanticAnalyzer<'a> {
    fn report_error(&mut self, node: NodeRef, kind: SemanticError) {
        self.report_error_with_notes(node, kind, vec![])
    }

    fn report_error_with_notes(&mut self, node: NodeRef, kind: SemanticError, notes: Vec<(SourceSpan, SemanticError)>) {
        let span = self.ast.get_span(node);
        let mut error = SemanticDiag::new(span, kind);
        error.notes = notes;
        error.level = Some(DiagnosticLevel::Error);
        self.diag
            .report_semantic_streaming(error, self.source_manager, self.registry);
    }

    fn report_warning(&mut self, node: NodeRef, kind: SemanticError) {
        if kind.is_pedantic() && self.lang_opts.pedantic_errors {
            self.report_error(node, kind);
        } else {
            let span = self.ast.get_span(node);
            let mut error = SemanticDiag::new(span, kind);
            error.level = Some(DiagnosticLevel::Warning);
            self.diag
                .report_semantic_streaming(error, self.source_manager, self.registry);
        }
    }

    fn push_conversion(&mut self, node: NodeRef, conv: Conversion) {
        let conversions = self.semantic_info.conversions.entry(node.index()).or_default();
        // Avoid redundant identical conversions pushed multiple times to the same node.
        // This handles cases where semantic rules might be applied twice (e.g. in compound assignments)
        // or during double-visits of the same expression node.
        if conversions.iter().any(|c| c == &conv) {
            return;
        }
        conversions.push(conv);
    }

    fn push_arithmetic_cast(&mut self, node: NodeRef, from: TypeRef, to: TypeRef) {
        if from == to {
            return;
        }

        let conv = if from.is_complex() || to.is_complex() {
            Conversion::ComplexCast { from, to }
        } else if from.is_floating() || to.is_floating() {
            Conversion::FloatingCast { from, to }
        } else {
            Conversion::IntegerCast { from, to }
        };

        self.push_conversion(node, conv);
    }

    /// Internal helper to apply lvalue-to-rvalue conversion to a node.
    /// This is private because it is only used during the semantic analysis pass.
    fn apply_lvalue_conversion(&mut self, node: NodeRef) {
        if self.semantic_info.value_categories[node.index()] == ValueCategory::LValue {
            // C11 6.3.2.1p2: Lvalue-to-rvalue conversion does not apply to array or function types.
            if let Some(qt) = self.semantic_info.types[node.index()] {
                if qt.is_array() || qt.is_function() {
                    return;
                }
                if !qt.is_void() && !self.registry.is_complete(qt.ty()) {
                    self.report_error(node, SemanticError::IncompleteType { ty: qt });
                }
            }

            self.semantic_info.value_categories[node.index()] = ValueCategory::RValue;
            self.push_conversion(node, Conversion::LValueToRValue);
        }
    }

    fn get_analysis_task(&self, qt: QualType) -> TypeAnalysisTask {
        let type_info = self.registry.get(qt.ty());
        match &type_info.kind {
            TypeKind::Record { members, is_union, .. } => TypeAnalysisTask::Record(Arc::clone(members), *is_union),
            TypeKind::Array { element_type, size, .. } => TypeAnalysisTask::Array(*element_type, *size),
            TypeKind::Function {
                return_type,
                parameters,
                is_variadic,
                ..
            } => TypeAnalysisTask::Function {
                return_type: *return_type,
                parameters: Arc::clone(parameters),
                is_variadic: *is_variadic,
            },
            _ => TypeAnalysisTask::None,
        }
    }

    fn is_string_literal(&self, node: NodeRef) -> bool {
        matches!(self.ast.get_kind(node), NodeKind::Literal(l) if l.kind() == LitKind::String)
    }

    fn check_uac(&mut self, node: NodeRef, lhs_promoted: QualType, rhs_promoted: QualType) -> Option<QualType> {
        usual_arithmetic_conversions(self.registry, lhs_promoted, rhs_promoted).or_else(|| {
            self.report_error(
                node,
                SemanticError::InvalidBinaryOperands {
                    left_ty: lhs_promoted,
                    right_ty: rhs_promoted,
                },
            );
            None
        })
    }

    fn require_scalar(&mut self, node: NodeRef, ty: QualType) -> bool {
        if !ty.is_scalar() {
            self.report_error(node, SemanticError::ExpectedScalarType { found: ty });
            false
        } else {
            true
        }
    }

    fn require_integer(&mut self, node: NodeRef, ty: QualType) -> bool {
        if !ty.is_integer() {
            self.report_error(node, SemanticError::ExpectedIntegerType { found: ty });
            false
        } else {
            true
        }
    }

    fn require_arithmetic(&mut self, node: NodeRef, ty: QualType) -> bool {
        if !ty.is_arithmetic() {
            self.report_error(node, SemanticError::InvalidUnaryOperand { ty });
            false
        } else {
            true
        }
    }

    fn unwrap_init_item(&self, node: NodeRef) -> (NodeRef, NodeRef, u16) {
        if let NodeKind::InitializerItem(item) = self.ast.get_kind(node) {
            (item.initializer, item.designator_start, item.designator_len)
        } else {
            (node, NodeRef::new(1).unwrap(), 0)
        }
    }

    fn const_ctx(&self) -> ConstEvalCtx<'_> {
        ConstEvalCtx {
            ast: self.ast,
            symbol_table: self.symbol_table,
            registry: self.registry,
            semantic_info: self.semantic_info,
        }
    }

    /// Recursively visit type to find any expressions (e.g. VLA sizes) and resolve them.
    fn visit_type_exprs(&mut self, qt: QualType) {
        let ty = qt.ty();

        // ⚡ Bolt: Fast-path for types that cannot contain nested expressions.
        // This includes builtins, records, enums, and complex types.
        // Skipping these avoids expensive HashSet insertions and lookups.
        match ty.class() {
            TypeClass::Builtin | TypeClass::Record | TypeClass::Enum | TypeClass::Complex => return,
            _ => {}
        }

        if !self.checked_types.insert(ty) {
            return;
        }

        // Bolt ⚡: Extract only needed info from TypeKind while holding a reference
        // to avoid cloning the entire Kind (which contains Arcs and large Record/Enum data).
        // For TypeofExpr, we must release the borrow before updating the registry.
        enum Task {
            Array(TypeRef, Option<NodeRef>),
            Pointer(QualType),
            Function(TypeRef, Arc<[FunctionParam]>),
            Complex(TypeRef),
            Typeof(NodeRef, bool), // bool is true for unqual
            Alias(TypeRef),
            None,
        }

        let task = match &self.registry.get(ty).kind {
            TypeKind::Array { element_type, size } => {
                let vla_expr = if let ArraySizeType::Variable(expr) = size {
                    Some(*expr)
                } else {
                    None
                };
                Task::Array(*element_type, vla_expr)
            }
            TypeKind::Pointer { pointee } => Task::Pointer(*pointee),
            TypeKind::Function {
                return_type,
                parameters,
                ..
            } => Task::Function(*return_type, Arc::clone(parameters)),
            TypeKind::Complex { base_type } => Task::Complex(*base_type),
            TypeKind::TypeofExpr(expr) => Task::Typeof(*expr, false),
            TypeKind::TypeofUnqualExpr(expr) => Task::Typeof(*expr, true),
            TypeKind::Alias(inner) => Task::Alias(*inner),
            _ => Task::None,
        };

        match task {
            Task::Array(element_type, vla_expr) => {
                if let Some(expr) = vla_expr
                    && let Some(qt) = self.visit_node(expr)
                    && !qt.is_integer()
                {
                    self.report_error(expr, SemanticError::ArraySizeNotInteger);
                }
                self.visit_type_exprs(QualType::unqualified(element_type));
            }
            Task::Pointer(pointee) => {
                self.visit_type_exprs(pointee);
            }
            Task::Function(return_type, parameters) => {
                self.visit_type_exprs(QualType::unqualified(return_type));
                for param in parameters.iter() {
                    self.visit_type_exprs(param.param_type);
                }
            }
            Task::Complex(base_type) => {
                self.visit_type_exprs(QualType::unqualified(base_type));
            }
            Task::Typeof(expr, unqual) => {
                let mut resolved_qt = self
                    .visit_node(expr)
                    .unwrap_or(QualType::unqualified(self.registry.type_error));
                if unqual {
                    resolved_qt = QualType::unqualified(resolved_qt.ty());
                }
                self.registry.types[ty.index()].kind = TypeKind::Alias(resolved_qt.ty());
            }
            Task::Alias(inner) => {
                self.visit_type_exprs(QualType::unqualified(inner));
            }
            // For Records and Enums, we don't need to traverse members because
            // they cannot contain VLAs (C11 6.7.2.1).
            // Even if they did, the members would be visited during their declaration processing.
            Task::None => {}
        }
    }

    fn is_always_true(&self, expr: NodeRef) -> bool {
        self.const_ctx().eval_int(expr).is_some_and(|v| v != 0)
    }

    fn has_default(&self, node: NodeRef) -> bool {
        match self.ast.get_kind(node) {
            NodeKind::Default(_) => true,
            NodeKind::CompoundStmt(cs) => cs.stmt_start.range(cs.stmt_len).any(|s| self.has_default(s)),
            NodeKind::DeclList(dl) => dl.stmt_start.range(dl.stmt_len).any(|s| self.has_default(s)),
            NodeKind::If(if_stmt) => {
                self.has_default(if_stmt.then_branch) || if_stmt.else_branch.is_some_and(|e| self.has_default(e))
            }
            NodeKind::While(while_stmt) => self.has_default(while_stmt.body),
            NodeKind::DoWhile(body, _) => self.has_default(*body),
            NodeKind::For(for_stmt) => self.has_default(for_stmt.body),
            NodeKind::Label(_, stmt, _) => self.has_default(*stmt),
            NodeKind::Case(_, stmt) | NodeKind::CaseRange(.., stmt) => self.has_default(*stmt),
            // Nested switch has its own default labels
            NodeKind::Switch(_, _) => false,
            _ => false,
        }
    }

    fn is_noreturn_expr(&self, expr: NodeRef) -> bool {
        match self.ast.get_kind(expr) {
            NodeKind::FunctionCall(call) => {
                if let NodeKind::Ident(_, sym) = self.ast.get_kind(call.callee) {
                    let symbol = self.symbol_table.get_symbol(*sym);
                    if let SymbolKind::Function(f) = &symbol.kind
                        && f.is_noreturn
                    {
                        return true;
                    }
                }

                if let Some(callee_type) = self.semantic_info.types[call.callee.index()] {
                    let mut ty = callee_type.ty();
                    // Bolt ⚡: Optimization: use registry.get_pointee() and is_noreturn_function helper.
                    // This avoids redundant Cow<Type> allocations for pointers in the hot path.
                    while let Some(pointee) = self.registry.get_pointee(ty) {
                        ty = pointee.ty();
                    }
                    return self.registry.is_noreturn_function(ty);
                }
                false
            }
            NodeKind::BuiltinChooseExpr(..) => {
                if let Some(&selected) = self.semantic_info.choose_expressions.get(&expr.index()) {
                    self.is_noreturn_expr(selected)
                } else {
                    false
                }
            }
            NodeKind::GenericSelection(..) => {
                if let Some(&selected) = self.semantic_info.generic_selections.get(&expr.index()) {
                    self.is_noreturn_expr(selected)
                } else {
                    false
                }
            }
            _ => false,
        }
    }

    fn contains_break(&self, node: NodeRef) -> bool {
        match self.ast.get_kind(node) {
            NodeKind::Break => true,
            NodeKind::CompoundStmt(cs) => cs.stmt_start.range(cs.stmt_len).any(|s| self.contains_break(s)),
            NodeKind::DeclList(dl) => dl.stmt_start.range(dl.stmt_len).any(|s| self.contains_break(s)),
            NodeKind::If(if_stmt) => {
                self.contains_break(if_stmt.then_branch) || if_stmt.else_branch.is_some_and(|e| self.contains_break(e))
            }
            // Do not recurse into nested loops or switches as their breaks belong to them.
            NodeKind::While(_) | NodeKind::For(_) | NodeKind::DoWhile(_, _) | NodeKind::Switch(_, _) => false,
            NodeKind::Label(_, stmt, _) => self.contains_break(*stmt),
            NodeKind::Case(_, stmt) | NodeKind::CaseRange(.., stmt) | NodeKind::Default(stmt) => {
                self.contains_break(*stmt)
            }
            _ => false,
        }
    }

    fn can_fall_through(&self, node: NodeRef) -> bool {
        match self.ast.get_kind(node) {
            NodeKind::Return(_) | NodeKind::Break | NodeKind::Continue | NodeKind::Goto(_, _) => false,
            NodeKind::If(if_stmt) => {
                let then_ft = self.can_fall_through(if_stmt.then_branch);
                let else_ft = if_stmt.else_branch.is_none_or(|e| self.can_fall_through(e));
                then_ft || else_ft
            }
            NodeKind::ExpressionStmt(Some(expr)) => !self.is_noreturn_expr(*expr),
            NodeKind::While(while_stmt) => {
                !self.is_always_true(while_stmt.condition) || self.contains_break(while_stmt.body)
            }
            NodeKind::DoWhile(body, condition) => !self.is_always_true(*condition) || self.contains_break(*body),
            NodeKind::For(for_stmt) => {
                let cond = for_stmt.child_start.add_offset(1);
                let has_condition = !matches!(self.ast.get_kind(cond), NodeKind::Dummy);
                (has_condition && !self.is_always_true(cond)) || self.contains_break(for_stmt.body)
            }
            NodeKind::CompoundStmt(cs) => {
                for stmt in cs.stmt_start.range(cs.stmt_len) {
                    if !self.can_fall_through(stmt) {
                        return false;
                    }
                }
                true
            }
            NodeKind::DeclList(dl) => {
                for stmt in dl.stmt_start.range(dl.stmt_len) {
                    if !self.can_fall_through(stmt) {
                        return false;
                    }
                }
                true
            }
            NodeKind::Switch(_, body) => {
                if !self.has_default(*body) {
                    return true;
                }
                if self.contains_break(*body) {
                    return true;
                }
                self.can_fall_through(*body)
            }
            NodeKind::Case(_, stmt) | NodeKind::CaseRange(.., stmt) | NodeKind::Default(stmt) => {
                self.can_fall_through(*stmt)
            }
            NodeKind::Label(_, stmt, _) => self.can_fall_through(*stmt),
            _ => true,
        }
    }

    /// ⚡ Bolt: Checks if the node is an LValue.
    /// This function is optimized to use the already-computed value category from the side table.
    fn is_lvalue(&self, node: NodeRef) -> bool {
        self.semantic_info.value_categories[node.index()] == ValueCategory::LValue
    }

    fn is_numeric_literal(&self, node: NodeRef) -> bool {
        if let NodeKind::Literal(lit) = self.ast.get_kind(node) {
            matches!(lit.kind(), LitKind::Int | LitKind::Char | LitKind::Float)
        } else {
            false
        }
    }

    fn decay(&mut self, node: NodeRef, qt: QualType) -> QualType {
        if qt.is_array() || qt.is_function() {
            if qt.is_array() && self.is_register_variable(node) {
                self.report_error(node, SemanticError::AddressOfRegister);
            }

            let decayed = self.registry.decay(qt, TypeQualifiers::empty());
            self.push_conversion(node, Conversion::PointerDecay { to: decayed.ty() });
            decayed
        } else {
            qt
        }
    }
    fn get_bitfield_width(&self, node: NodeRef) -> Option<u16> {
        match self.ast.get_kind(node) {
            NodeKind::MemberAccess(obj, field_name, is_arrow) => {
                let obj_qt = self.semantic_info.types[obj.index()]?;
                let record_ty = if *is_arrow {
                    self.registry.get_pointee(obj_qt.ty()).map(|p| p.ty())
                } else {
                    Some(obj_qt.ty())
                };

                record_ty.and_then(|rt| {
                    self.registry
                        .get(rt)
                        .find_member(self.registry, *field_name)
                        .and_then(|m| m.bit_field_size)
                })
            }
            // Comma operator: the result is wholly the RHS value; propagate its bitfield width.
            NodeKind::BinaryOp(BinaryOp::Comma, _, rhs) => self.get_bitfield_width(*rhs),
            NodeKind::BuiltinChooseExpr(..) => self
                .semantic_info
                .choose_expressions
                .get(&node.index())
                .and_then(|&selected| self.get_bitfield_width(selected)),
            NodeKind::GenericSelection(_) => self
                .semantic_info
                .generic_selections
                .get(&node.index())
                .and_then(|&selected| self.get_bitfield_width(selected)),
            NodeKind::StatementExpr(_, result_expr) => self.get_bitfield_width(*result_expr),
            NodeKind::UnaryOp(UnaryOp::Real, operand) => self.get_bitfield_width(*operand),
            NodeKind::UnaryOp(UnaryOp::Imag, operand) => {
                let operand_ty = self.semantic_info.types.get(operand.index()).and_then(|t| *t);
                if operand_ty.is_some_and(|t| t.is_complex()) {
                    self.get_bitfield_width(*operand)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    fn is_register_variable(&self, node: NodeRef) -> bool {
        let node_kind = self.ast.get_kind(node);
        match node_kind {
            NodeKind::Ident(_, sym) => {
                let symbol = self.symbol_table.get_symbol(*sym);
                if let SymbolKind::Variable(v) = &symbol.kind {
                    return v.storage == Some(StorageClass::Register);
                }
                false
            }
            NodeKind::UnaryOp(UnaryOp::Real, operand) => self.is_register_variable(*operand),
            NodeKind::UnaryOp(UnaryOp::Imag, operand) => {
                let operand_ty = self.semantic_info.types.get(operand.index()).and_then(|t| *t);
                if operand_ty.is_some_and(|t| t.is_complex()) {
                    self.is_register_variable(*operand)
                } else {
                    false
                }
            }
            NodeKind::MemberAccess(obj, _, is_arrow) => !is_arrow && self.is_register_variable(*obj),
            NodeKind::IndexAccess(arr, _) => {
                let arr_ty = self.semantic_info.types.get(arr.index()).and_then(|t| *t);
                arr_ty.is_some_and(|t| t.is_array()) && self.is_register_variable(*arr)
            }
            NodeKind::BuiltinChooseExpr(..) => {
                if let Some(&selected) = self.semantic_info.choose_expressions.get(&node.index()) {
                    self.is_register_variable(selected)
                } else {
                    false
                }
            }
            NodeKind::GenericSelection(_) => {
                if let Some(&selected) = self.semantic_info.generic_selections.get(&node.index()) {
                    self.is_register_variable(selected)
                } else {
                    false
                }
            }
            _ => false,
        }
    }

    fn is_null_pointer_constant(&self, node: NodeRef) -> bool {
        // C11 6.3.2.3p3: An integer constant expression with the value 0,
        // or such an expression cast to type void *, is called a null pointer constant.
        // In C23, nullptr is also a null pointer constant.

        let node_kind = self.ast.get_kind(node);

        // Bolt ⚡: Optimization: Early-exit for node kinds that are definitely not constant expressions.
        // This avoids redundant type lookups and recursive evaluation attempts for common non-constant nodes.
        match node_kind {
            NodeKind::Assignment(..)
            | NodeKind::FunctionCall(..)
            | NodeKind::PostIncrement(..)
            | NodeKind::PostDecrement(..)
            | NodeKind::CompoundStmt(..)
            | NodeKind::DeclList(..)
            | NodeKind::If(..)
            | NodeKind::While(..)
            | NodeKind::For(..)
            | NodeKind::Return(..)
            | NodeKind::Break
            | NodeKind::Continue
            | NodeKind::Goto(..)
            | NodeKind::Label(..)
            | NodeKind::Switch(..)
            | NodeKind::ExpressionStmt(..)
            | NodeKind::AsmStmt(..)
            | NodeKind::TranslationUnit(..) => return false,
            _ => {}
        }

        match node_kind {
            NodeKind::Literal(l) if l.kind() == LitKind::Nullptr => return true,
            NodeKind::Cast(qt, inner) if qt.ty() == self.registry.type_void_ptr => {
                return self.is_null_pointer_constant(*inner);
            }
            // Transparent wrappers that preserve NPC status (DR 481)
            NodeKind::BuiltinChooseExpr(..) => {
                if let Some(&selected) = self.semantic_info.choose_expressions.get(&node.index()) {
                    return self.is_null_pointer_constant(selected);
                }
            }
            NodeKind::GenericSelection(_) => {
                if let Some(&selected) = self.semantic_info.generic_selections.get(&node.index()) {
                    return self.is_null_pointer_constant(selected);
                }
            }
            NodeKind::UnaryOp(UnaryOp::Real | UnaryOp::Imag, operand)
                // __real__ and __imag__ on pointers/integers are GCC extensions.
                // However, Cendol only allows them on real types (integers/floats) and complex types.
                // If applied to an integer NPC, propagate it.
                if self.is_null_pointer_constant(*operand) => {
                    return true;
                }
            _ => {}
        }

        self.is_integer_constant_zero(node)
    }

    fn is_integer_constant_zero(&self, node: NodeRef) -> bool {
        // Bolt ⚡: Fast-path for literals using the optimized LitRef::is_integer_zero().
        // This avoids recursive constant evaluation and RwLock acquisition for common literals.
        if let NodeKind::Literal(l) = self.ast.get_kind(node) {
            return l.is_integer_zero();
        }

        if let Some(qt) = self.semantic_info.types.get(node.index()).and_then(|t| *t)
            && qt.is_integer()
        {
            return self.const_ctx().eval_int(node) == Some(0);
        }
        false
    }

    /// Checks if the operand is valid for increment/decrement operations (prefix or postfix).
    /// C11 6.5.3.1 (prefix) and 6.5.2.4 (postfix): operand shall have scalar type.
    /// C11 6.5.6: pointer arithmetic requires pointer to complete object type.
    fn check_increment_decrement_operand(&mut self, node: NodeRef, qt: QualType) -> bool {
        if !qt.is_scalar() {
            self.report_error(node, SemanticError::InvalidUnaryOperand { ty: qt });
            return false;
        }

        if let Some(pointee) = self.registry.get_pointee(qt.ty())
            && (!self.registry.is_complete(pointee.ty()) || pointee.is_function())
        {
            self.report_error(node, SemanticError::InvalidUnaryOperand { ty: qt });
            return false;
        }

        true
    }

    /// Checks if the node is an LValue and is not const-qualified.
    /// Reports errors if check fails.
    fn check_lvalue_and_modifiable(&mut self, node: NodeRef, qt: QualType) -> bool {
        if !self.is_lvalue(node) || qt.is_array() || qt.is_function() {
            self.report_error(node, SemanticError::NotAnLvalue);
            false
        } else if !self.registry.is_complete(qt.ty()) {
            self.report_error(node, SemanticError::IncompleteType { ty: qt });
            false
        } else if self.registry.is_const_recursive(qt) {
            self.report_error(node, SemanticError::AssignmentToReadOnly);
            false
        } else {
            true
        }
    }

    /// Validates assignment constraints and records implicit conversions.
    /// Returns true if assignment is valid, false otherwise.
    fn validate_assignment(
        &mut self,
        report_node: NodeRef,
        lhs_qt: QualType,
        rhs_qt: QualType,
        rhs_node: NodeRef,
    ) -> bool {
        let is_npc = self.is_null_pointer_constant(rhs_node);
        if self.check_assignment_constraints(lhs_qt, rhs_qt, rhs_node, is_npc) {
            self.record_implicit_conversions(lhs_qt, rhs_qt, rhs_node, is_npc);
            true
        } else if self.is_incompatible_struct_pointer_types(lhs_qt, rhs_qt) {
            // Incompatible struct pointer types - report as warning but allow the assignment
            self.report_warning(
                report_node,
                SemanticError::IncompatiblePointerTypes {
                    expected: lhs_qt,
                    found: rhs_qt,
                },
            );
            // Still record conversions so the assignment works
            self.record_implicit_conversions(lhs_qt, rhs_qt, rhs_node, is_npc);
            true
        } else if self.is_pointer_signedness_mismatch(lhs_qt, rhs_qt) {
            // Pointers differ only in signedness - report as warning
            self.report_warning(
                report_node,
                SemanticError::PointerSignednessMismatch {
                    expected: lhs_qt,
                    found: rhs_qt,
                },
            );
            self.record_implicit_conversions(lhs_qt, rhs_qt, rhs_node, is_npc);
            true
        } else if self.is_discarding_pointer_qualifiers(lhs_qt, rhs_qt) {
            self.report_warning(
                report_node,
                SemanticError::PointerAssignmentDiscardsQualifiers {
                    expected: lhs_qt,
                    found: rhs_qt,
                },
            );
            self.record_implicit_conversions(lhs_qt, rhs_qt, rhs_node, is_npc);
            true
        } else if self.is_incompatible_pointer_types(lhs_qt, rhs_qt) {
            self.report_warning(
                report_node,
                SemanticError::IncompatiblePointerTypes {
                    expected: lhs_qt,
                    found: rhs_qt,
                },
            );
            self.record_implicit_conversions(lhs_qt, rhs_qt, rhs_node, is_npc);
            true
        } else {
            self.report_error(
                report_node,
                SemanticError::TypeMismatch {
                    expected: lhs_qt,
                    found: rhs_qt,
                },
            );
            false
        }
    }

    /// Check if the assignment is between pointers where target qualifiers are discarded
    fn is_discarding_pointer_qualifiers(&self, lhs: QualType, rhs: QualType) -> bool {
        let lhs = self.registry.canonical_qual_type(lhs);
        let rhs = self.registry.canonical_qual_type(rhs);
        // Both must be pointers (or array/function that decay to pointers)
        if !lhs.is_pointer() {
            return false;
        }

        // Resolve implicit decay for RHS
        let rhs_pointee = if rhs.is_array() {
            // Array qualifiers apply to the element type
            self.registry
                .get_array_element(rhs.ty())
                .map(|elem| QualType::new(elem, rhs.qualifiers()))
        } else if rhs.is_function() {
            Some(rhs) // Function decays to pointer to function (unqualified)
        } else if rhs.is_pointer() {
            self.registry.get_pointee(rhs.ty())
        } else {
            None
        };

        if let Some(rhs_base) = rhs_pointee {
            let lhs_base = self.registry.get_pointee(lhs.ty()).unwrap();

            // Check compatibility ignoring top-level qualifiers of the pointed-to type
            let compatible_ignoring_quals = if lhs_base.is_void() || rhs_base.is_void() {
                true
            } else {
                self.registry.is_compatible(lhs_base.strip_all(), rhs_base.strip_all())
            };

            if compatible_ignoring_quals {
                // Return true if qualifiers are DISCARDED (rhs has something lhs doesn't)
                return !lhs_base.qualifiers().contains(rhs_base.qualifiers());
            }
        }

        false
    }

    /// Check if the mismatch is between pointers to integers that only differ in signedness
    fn is_pointer_signedness_mismatch(&self, lhs: QualType, rhs: QualType) -> bool {
        let lhs = self.registry.canonical_qual_type(lhs);
        let rhs = self.registry.canonical_qual_type(rhs);
        if !lhs.is_pointer() || !rhs.is_pointer() {
            return false;
        }

        let lhs_pointee = self.registry.get_pointee(lhs.ty());
        let rhs_pointee = self.registry.get_pointee(rhs.ty());

        if let (Some(lhs_p), Some(rhs_p)) = (lhs_pointee, rhs_pointee) {
            let lhs_p_canon = self.registry.canonical_qual_type(lhs_p).ty();
            let rhs_p_canon = self.registry.canonical_qual_type(rhs_p).ty();

            if let (Some(lhs_b), Some(rhs_b)) = (lhs_p_canon.builtin(), rhs_p_canon.builtin()) {
                return lhs_b.is_integer() && rhs_b.is_integer() && lhs_b.rank() == rhs_b.rank() && lhs_b != rhs_b;
            }
        }

        false
    }

    /// Check if the mismatch is between pointers to different struct types
    fn is_incompatible_struct_pointer_types(&self, lhs: QualType, rhs: QualType) -> bool {
        let lhs = self.registry.canonical_qual_type(lhs);
        let rhs = self.registry.canonical_qual_type(rhs);
        // Both must be pointers
        if !lhs.is_pointer() || !rhs.is_pointer() {
            return false;
        }

        // Get the pointed-to types
        let lhs_pointee = self.registry.get_pointee(lhs.ty());
        let rhs_pointee = self.registry.get_pointee(rhs.ty());

        if let (Some(lhs_p), Some(rhs_p)) = (lhs_pointee, rhs_pointee) {
            // Both pointees must be struct/union types (Record with different types)
            let lhs_pointee_ty = self.registry.get(lhs_p.ty());
            let rhs_pointee_ty = self.registry.get(rhs_p.ty());

            if let (TypeKind::Record { .. }, TypeKind::Record { .. }) = (&lhs_pointee_ty.kind, &rhs_pointee_ty.kind) {
                // They must be different types (not compatible)
                return lhs_p.ty() != rhs_p.ty();
            }
        }

        false
    }

    /// Check if the mismatch is between incompatible level-1 pointer types or pointers of different levels
    fn is_incompatible_pointer_types(&self, lhs: QualType, rhs: QualType) -> bool {
        let lhs = self.registry.canonical_qual_type(lhs);
        let rhs = self.registry.canonical_qual_type(rhs);
        if !lhs.is_pointer() {
            return false;
        }

        // Resolve implicit decay for RHS
        let rhs_pointee = if rhs.is_array() {
            self.registry
                .get_array_element(rhs.ty())
                .map(|elem| QualType::new(elem, rhs.qualifiers()))
        } else if rhs.is_function() {
            Some(rhs)
        } else if rhs.is_pointer() {
            self.registry.get_pointee(rhs.ty())
        } else {
            None
        };

        if let Some(rhs_base) = rhs_pointee {
            let lhs_base = self.registry.get_pointee(lhs.ty()).unwrap();

            // We only warn for level-1 pointers or pointers of different levels to prevent silent bypass of nested qualifiers constraints.
            if (!lhs_base.is_pointer() && !rhs_base.is_pointer()) || (lhs_base.is_pointer() != rhs_base.is_pointer()) {
                return !self.registry.is_compatible(
                    QualType::unqualified(lhs_base.ty()),
                    QualType::unqualified(rhs_base.ty()),
                );
            }
        }

        false
    }

    fn check_scalar_condition(&mut self, condition: NodeRef) {
        let Some(mut cond_qt) = self.visit_node(condition) else {
            return;
        };

        if cond_qt.is_array()
            && let NodeKind::Ident(name, _) = self.ast.get_kind(condition)
        {
            self.report_warning(condition, SemanticError::AddressOfArrayAlwaysTrue { name: *name });
        }

        if cond_qt.is_array() || cond_qt.is_function() {
            cond_qt = self.decay(condition, cond_qt);
            self.semantic_info.types[condition.index()] = Some(cond_qt);
        }

        if !cond_qt.is_scalar() {
            self.report_error(condition, SemanticError::ExpectedScalarType { found: cond_qt });
        }
    }

    fn visit_if_statement(&mut self, stmt: &IfStmt) {
        self.check_scalar_condition(stmt.condition);
        self.visit_node(stmt.then_branch);
        if let Some(else_branch) = stmt.else_branch {
            self.visit_node(else_branch);
        }
    }

    fn visit_while_statement(&mut self, stmt: &WhileStmt) {
        self.check_scalar_condition(stmt.condition);
        self.loop_depth += 1;
        self.visit_node(stmt.body);
        self.loop_depth -= 1;
    }

    fn visit_for_statement(&mut self, stmt: &ForStmt) {
        let init = stmt.child_start;
        let cond = stmt.child_start.add_offset(1);
        let inc = stmt.child_start.add_offset(2);

        if !matches!(self.ast.get_kind(init), NodeKind::Dummy) {
            self.visit_node(init);
        }
        if !matches!(self.ast.get_kind(cond), NodeKind::Dummy) {
            self.check_scalar_condition(cond);
        }
        if !matches!(self.ast.get_kind(inc), NodeKind::Dummy) {
            self.visit_node(inc);
        }
        self.loop_depth += 1;
        self.visit_node(stmt.body);
        self.loop_depth -= 1;
    }

    fn visit_return_statement(&mut self, node: NodeRef, value_expr: &Option<NodeRef>) {
        let Some(ctx) = self.current_function else {
            unreachable!("ICE: Return outside function");
        };

        let expr_ty = if let Some(expr) = value_expr {
            let ty = self.visit_node(*expr);
            if ty.is_some() {
                self.apply_lvalue_conversion(*expr);
            }
            ty
        } else {
            None
        };

        if ctx.is_noreturn {
            self.report_error(node, SemanticError::NoreturnFunctionHasReturn { name: ctx.name });
        }

        let ret_ty = Some(ctx.ret_type);
        let is_void_func = ctx.ret_type.is_void();
        let func_name = ctx.name;

        if value_expr.is_none() {
            if !is_void_func {
                self.report_error(node, SemanticError::NonVoidReturnWithoutValue { name: func_name });
            }
            return;
        }

        if is_void_func {
            // C11 §6.8.6.4p3: "A return statement with an expression shall not appear in a function whose return type is void."
            if let Some(expr) = value_expr {
                if expr_ty.map(|t| t.is_void()).unwrap_or(false) {
                    self.report_warning(*expr, SemanticError::VoidReturnWithVoidExpr { name: func_name });
                } else {
                    self.report_error(*expr, SemanticError::VoidReturnWithValue { name: func_name });
                }
            }
        }

        if let Some(expr_ty) = expr_ty
            && let Some(target_ty) = ret_ty
            && let Some(expr) = value_expr
        {
            self.validate_assignment(node, target_ty, expr_ty, *expr);
        }

        if let Some(expr) = value_expr
            && let NodeKind::UnaryOp(UnaryOp::AddrOf, operand) = self.ast.get_kind(*expr)
            && let NodeKind::Ident(name, sym) = self.ast.get_kind(*operand)
        {
            let symbol = self.symbol_table.get_symbol(*sym);
            if let SymbolKind::Variable(v) = &symbol.kind {
                // Check if it's a local variable (not static/extern)
                let is_local = symbol.scope_id != crate::semantic::ScopeId::GLOBAL
                    && v.storage != Some(StorageClass::Static)
                    && v.storage != Some(StorageClass::Extern)
                    && v.storage != Some(StorageClass::ThreadLocal);

                if is_local {
                    self.report_warning(node, SemanticError::ReturnLocalAddress { name: *name });
                }
            }
        }
    }

    fn visit_unary_op(&mut self, node: NodeRef, op: UnaryOp, expr: NodeRef) -> Option<QualType> {
        let operand_qt = self.visit_node(expr)?;

        match op {
            UnaryOp::AddrOf => {
                if !self.is_lvalue(expr) {
                    self.report_error(node, SemanticError::NotAnLvalue);
                    return None;
                }
                if self.get_bitfield_width(expr).is_some() {
                    self.report_error(node, SemanticError::AddressOfBitfield);
                    return None;
                }
                if self.is_register_variable(expr) {
                    self.report_error(node, SemanticError::AddressOfRegister);
                    return None;
                }
                // Taking address of array or function: result is pointer to array/function (no decay)
                Some(QualType::unqualified(self.registry.pointer_to(operand_qt)))
            }
            UnaryOp::Deref => {
                self.apply_lvalue_conversion(expr);
                let actual_qt = self.decay(expr, operand_qt);

                if actual_qt.is_pointer() {
                    // Bolt ⚡: Eagerly set value category to LValue for dereference.
                    self.semantic_info.value_categories[node.index()] = ValueCategory::LValue;
                    self.registry.get_pointee(actual_qt.ty())
                } else {
                    self.report_error(node, SemanticError::IndirectionRequiresPointer { ty: actual_qt });
                    None
                }
            }
            UnaryOp::Real | UnaryOp::Imag => {
                if let TypeKind::Complex { base_type } = &self.registry.get(operand_qt.ty()).kind {
                    // Bolt ⚡: Eagerly set value category to LValue for __real__/__imag__ on complex LValue.
                    if self.semantic_info.value_categories[expr.index()] == ValueCategory::LValue {
                        self.semantic_info.value_categories[node.index()] = ValueCategory::LValue;
                    }
                    Some(QualType::new(*base_type, operand_qt.qualifiers()))
                } else if self.require_arithmetic(node, operand_qt) {
                    if op == UnaryOp::Real {
                        // Bolt ⚡: Eagerly set value category to LValue for __real__ on real LValue.
                        if self.semantic_info.value_categories[expr.index()] == ValueCategory::LValue {
                            self.semantic_info.value_categories[node.index()] = ValueCategory::LValue;
                        }
                        Some(operand_qt)
                    } else {
                        // __imag__ on real type returns zero of that type
                        Some(operand_qt.strip_all())
                    }
                } else {
                    None
                }
            }
            UnaryOp::PreIncrement | UnaryOp::PreDecrement => {
                self.check_lvalue_and_modifiable(expr, operand_qt);
                if self.check_increment_decrement_operand(node, operand_qt) {
                    Some(operand_qt)
                } else {
                    None
                }
            }
            UnaryOp::Plus | UnaryOp::Minus => {
                self.apply_lvalue_conversion(expr);
                if self.require_arithmetic(node, operand_qt) {
                    // C11 6.5.3.3: The integer promotions are performed on the operand,
                    // and the result has the promoted type.
                    let promoted = self.apply_integer_promotion(expr, operand_qt);

                    // Strip all qualifiers for unary plus/minus operations
                    let stripped = promoted.strip_all();
                    if stripped.qualifiers() != promoted.qualifiers() {
                        self.push_conversion(
                            expr,
                            Conversion::QualifierAdjust {
                                from: promoted.qualifiers(),
                                to: stripped.qualifiers(),
                            },
                        );
                    }
                    Some(stripped)
                } else {
                    None
                }
            }
            UnaryOp::LogicNot => {
                self.apply_lvalue_conversion(expr);

                let mut actual_qt = operand_qt;

                if actual_qt.is_array()
                    && let NodeKind::Ident(name, _) = self.ast.get_kind(expr)
                {
                    self.report_warning(node, SemanticError::AddressOfArrayAlwaysTrue { name: *name });
                }

                if actual_qt.is_array() || actual_qt.is_function() {
                    actual_qt = self.decay(expr, actual_qt);
                    self.semantic_info.types[expr.index()] = Some(actual_qt);
                }

                if !actual_qt.is_scalar() {
                    self.report_error(node, SemanticError::ExpectedScalarType { found: actual_qt });
                    return None;
                }

                // Logical NOT always returns int type (C11 6.5.3.3)
                Some(QualType::unqualified(self.registry.type_int))
            }
            UnaryOp::BitNot => {
                self.apply_lvalue_conversion(expr);
                if operand_qt.is_integer() {
                    Some(self.apply_integer_promotion(expr, operand_qt))
                } else if operand_qt.is_complex() {
                    Some(operand_qt)
                } else {
                    self.report_error(node, SemanticError::InvalidUnaryOperand { ty: operand_qt });
                    None
                }
            }
        }
    }

    fn apply_integer_promotion(&mut self, node: NodeRef, qt: QualType) -> QualType {
        let bitfield_width = self.get_bitfield_width(node);
        let promoted = integer_promotion(self.registry, qt, bitfield_width);
        if promoted.ty() != qt.ty() {
            self.push_conversion(
                node,
                Conversion::IntegerPromotion {
                    from: qt.ty(),
                    to: promoted.ty(),
                },
            );
        }
        promoted
    }

    fn analyze_binary_operation_types(
        &mut self,
        node: NodeRef,
        op: BinaryOp,
        lhs_promoted: QualType,
        rhs_promoted: QualType,
    ) -> Option<(QualType, QualType)> {
        match op {
            BinaryOp::Add if lhs_promoted.is_pointer() || rhs_promoted.is_pointer() => {
                self.analyze_pointer_arithmetic(node, op, lhs_promoted, rhs_promoted)
            }
            BinaryOp::Sub if lhs_promoted.is_pointer() || rhs_promoted.is_pointer() => {
                self.analyze_pointer_arithmetic(node, op, lhs_promoted, rhs_promoted)
            }
            BinaryOp::Equal
            | BinaryOp::NotEqual
            | BinaryOp::Less
            | BinaryOp::LessEqual
            | BinaryOp::Greater
            | BinaryOp::GreaterEqual => self.analyze_comparison(node, op, lhs_promoted, rhs_promoted),
            BinaryOp::LogicAnd | BinaryOp::LogicOr => self.analyze_logical(node, lhs_promoted, rhs_promoted),
            BinaryOp::LShift | BinaryOp::RShift => self.analyze_shift(node, lhs_promoted, rhs_promoted),
            _ => self.analyze_arithmetic(node, lhs_promoted, rhs_promoted),
        }
    }

    fn analyze_pointer_arithmetic(
        &mut self,
        node: NodeRef,
        op: BinaryOp,
        lhs: QualType,
        rhs: QualType,
    ) -> Option<(QualType, QualType)> {
        match op {
            BinaryOp::Add => {
                if lhs.is_pointer() && rhs.is_integer() {
                    self.check_pointer_arithmetic_operand(node, lhs, rhs, lhs)?;
                    Some((lhs, lhs))
                } else if lhs.is_integer() && rhs.is_pointer() {
                    self.check_pointer_arithmetic_operand(node, lhs, rhs, rhs)?;
                    Some((rhs, rhs))
                } else {
                    self.report_error(
                        node,
                        SemanticError::InvalidBinaryOperands {
                            left_ty: lhs,
                            right_ty: rhs,
                        },
                    );
                    None
                }
            }
            BinaryOp::Sub => {
                if lhs.is_pointer() && rhs.is_integer() {
                    self.check_pointer_arithmetic_operand(node, lhs, rhs, lhs)?;
                    Some((lhs, lhs))
                } else if lhs.is_pointer() && rhs.is_pointer() {
                    let lhs_base = self.registry.get_pointee(lhs.ty()).unwrap();
                    let rhs_base = self.registry.get_pointee(rhs.ty()).unwrap();

                    let compatible = self.registry.is_compatible(lhs_base.strip_all(), rhs_base.strip_all());
                    let complete_lhs = self.registry.is_complete(lhs_base.ty());
                    let complete_rhs = self.registry.is_complete(rhs_base.ty());
                    let is_func_lhs = lhs_base.is_function();
                    let is_func_rhs = rhs_base.is_function();

                    if !compatible || !complete_lhs || !complete_rhs || is_func_lhs || is_func_rhs {
                        self.report_error(
                            node,
                            SemanticError::InvalidBinaryOperands {
                                left_ty: lhs,
                                right_ty: rhs,
                            },
                        );
                        return None;
                    }

                    Some((QualType::unqualified(self.registry.type_long), lhs))
                } else {
                    self.report_error(
                        node,
                        SemanticError::InvalidBinaryOperands {
                            left_ty: lhs,
                            right_ty: rhs,
                        },
                    );
                    None
                }
            }
            _ => unreachable!(),
        }
    }

    fn check_pointer_arithmetic_operand(
        &mut self,
        node: NodeRef,
        lhs: QualType,
        rhs: QualType,
        ptr_ty: QualType,
    ) -> Option<()> {
        if let Some(pointee) = self.registry.get_pointee(ptr_ty.ty())
            && (!self.registry.is_complete(pointee.ty()) || pointee.is_function())
        {
            self.report_error(
                node,
                SemanticError::InvalidBinaryOperands {
                    left_ty: lhs,
                    right_ty: rhs,
                },
            );
            return None;
        }
        Some(())
    }

    fn analyze_comparison(
        &mut self,
        node: NodeRef,
        op: BinaryOp,
        lhs: QualType,
        rhs: QualType,
    ) -> Option<(QualType, QualType)> {
        let is_equality = matches!(op, BinaryOp::Equal | BinaryOp::NotEqual);
        let common = if lhs.is_pointer() && rhs.is_pointer() {
            let lhs_base = self.registry.get_pointee(lhs.ty()).unwrap();
            let rhs_base = self.registry.get_pointee(rhs.ty()).unwrap();

            if is_equality {
                if lhs_base.is_void() || rhs_base.is_void() {
                    QualType::unqualified(self.registry.type_void_ptr)
                } else if self.registry.is_compatible(lhs_base.strip_all(), rhs_base.strip_all()) {
                    lhs
                } else {
                    self.report_warning(node, SemanticError::IncompatiblePointerComparison { lhs, rhs });
                    lhs
                }
            } else {
                if lhs_base.is_function() || rhs_base.is_function() {
                    self.report_error(
                        node,
                        SemanticError::InvalidBinaryOperands {
                            left_ty: lhs,
                            right_ty: rhs,
                        },
                    );
                    return None;
                }

                if lhs_base != rhs_base {
                    self.report_warning(node, SemanticError::IncompatiblePointerComparison { lhs, rhs });
                }
                lhs
            }
        } else if is_equality && lhs.is_pointer() {
            lhs
        } else if is_equality && rhs.is_pointer() {
            rhs
        } else if (is_equality && lhs.is_arithmetic() && rhs.is_arithmetic())
            || (!is_equality && lhs.is_real() && rhs.is_real())
        {
            self.check_uac(node, lhs, rhs)?
        } else {
            self.report_error(
                node,
                SemanticError::InvalidBinaryOperands {
                    left_ty: lhs,
                    right_ty: rhs,
                },
            );
            return None;
        };

        Some((QualType::unqualified(self.registry.type_int), common))
    }

    fn analyze_logical(&mut self, node: NodeRef, lhs: QualType, rhs: QualType) -> Option<(QualType, QualType)> {
        if !lhs.is_scalar() || !rhs.is_scalar() {
            self.report_error(
                node,
                SemanticError::InvalidBinaryOperands {
                    left_ty: lhs,
                    right_ty: rhs,
                },
            );
            return None;
        }
        Some((QualType::unqualified(self.registry.type_int), lhs))
    }

    fn analyze_shift(&mut self, node: NodeRef, lhs: QualType, rhs: QualType) -> Option<(QualType, QualType)> {
        if !lhs.is_integer() || !rhs.is_integer() {
            self.report_error(
                node,
                SemanticError::InvalidBinaryOperands {
                    left_ty: lhs,
                    right_ty: rhs,
                },
            );
            return None;
        }
        Some((lhs, lhs))
    }

    fn analyze_arithmetic(&mut self, node: NodeRef, lhs: QualType, rhs: QualType) -> Option<(QualType, QualType)> {
        if !lhs.is_arithmetic() || !rhs.is_arithmetic() {
            self.report_error(
                node,
                SemanticError::InvalidBinaryOperands {
                    left_ty: lhs,
                    right_ty: rhs,
                },
            );
            return None;
        }

        if let Some(ty) = usual_arithmetic_conversions(self.registry, lhs, rhs) {
            Some((ty, ty))
        } else {
            self.report_error(
                node,
                SemanticError::InvalidBinaryOperands {
                    left_ty: lhs,
                    right_ty: rhs,
                },
            );
            None
        }
    }

    fn visit_binary_op(&mut self, op: BinaryOp, lhs: NodeRef, rhs: NodeRef) -> Option<QualType> {
        debug_assert!(
            !op.is_assignment(),
            "visit_binary_op called with assignment operator: {:?}",
            op
        );
        let lhs_ty = self.visit_node(lhs)?;
        let rhs_ty = self.visit_node(rhs)?;

        if op == BinaryOp::Comma {
            self.apply_lvalue_conversion(lhs);
            let mut rhs_decayed = rhs_ty;
            if rhs_ty.is_array() || rhs_ty.is_function() {
                rhs_decayed = self.registry.decay(rhs_ty, TypeQualifiers::empty());
                self.push_conversion(rhs, Conversion::PointerDecay { to: rhs_decayed.ty() });
            }
            return Some(rhs_decayed);
        }

        let (result_ty, _) = self.resolve_binary_operation_types(op, lhs, rhs, lhs_ty, rhs_ty)?;
        Some(result_ty)
    }

    fn resolve_binary_operation_types(
        &mut self,
        op: BinaryOp,
        lhs: NodeRef,
        rhs: NodeRef,
        lhs_qt: QualType,
        rhs_qt: QualType,
    ) -> Option<(QualType, QualType)> {
        // Perform array/function decay first
        let lhs_decayed = self.decay(lhs, lhs_qt);
        let rhs_decayed = self.decay(rhs, rhs_qt);

        // Perform integer promotions and record them
        let lhs_promoted = self.apply_integer_promotion(lhs, lhs_decayed);
        let rhs_promoted = self.apply_integer_promotion(rhs, rhs_decayed);

        if op == BinaryOp::Mod && (!lhs_promoted.is_integer() || !rhs_promoted.is_integer()) {
            self.report_error(
                lhs,
                SemanticError::InvalidBinaryOperands {
                    left_ty: lhs_promoted,
                    right_ty: rhs_promoted,
                },
            );
            return None;
        }

        let (result_qt, common_qt) = self.analyze_binary_operation_types(lhs, op, lhs_promoted, rhs_promoted)?;

        // For arithmetic/comparison operations, operands should be converted to a common type.
        let lhs_target = common_qt.ty();
        if lhs_promoted.ty() != lhs_target || self.is_numeric_literal(lhs) {
            // Check if this conversion is already the last one to avoid duplicates
            // resolve_binary_operation_types might be called multiple times in some complex nested scenarios
            let needs_push = match self.semantic_info.conversions.get(&lhs.index()).and_then(|v| v.last()) {
                Some(Conversion::IntegerCast { to, .. }) => *to != lhs_target,
                Some(Conversion::FloatingCast { to, .. }) => *to != lhs_target,
                Some(Conversion::ComplexCast { to, .. }) => *to != lhs_target,
                _ => true,
            };

            if needs_push {
                self.push_arithmetic_cast(lhs, lhs_promoted.ty(), lhs_target);
            }
        }

        let rhs_target = common_qt.ty();
        if rhs_promoted.ty() != rhs_target || self.is_numeric_literal(rhs) {
            let needs_push = match self.semantic_info.conversions.get(&rhs.index()).and_then(|v| v.last()) {
                Some(Conversion::IntegerCast { to, .. }) => *to != rhs_target,
                Some(Conversion::FloatingCast { to, .. }) => *to != rhs_target,
                Some(Conversion::ComplexCast { to, .. }) => *to != rhs_target,
                _ => true,
            };

            if needs_push {
                self.push_arithmetic_cast(rhs, rhs_promoted.ty(), rhs_target);
            }
        }

        Some((result_qt, common_qt))
    }

    fn visit_assignment(&mut self, node: NodeRef, op: BinaryOp, lhs: NodeRef, rhs: NodeRef) -> Option<QualType> {
        debug_assert!(
            op.is_assignment(),
            "visit_assignment called with non-assignment operator: {:?}",
            op
        );

        let lhs_ty = self.visit_node(lhs)?;
        let rhs_ty = self.visit_node(rhs)?;

        if !self.check_lvalue_and_modifiable(lhs, lhs_ty) {
            return None;
        }

        if let Some(arithmetic_op) = op.without_assignment() {
            self.apply_lvalue_conversion(rhs);
            return self.visit_compound_assignment(node, arithmetic_op, lhs, rhs, lhs_ty, rhs_ty);
        }

        // Simple assignment
        self.apply_lvalue_conversion(rhs);
        if !self.validate_assignment(node, lhs_ty, rhs_ty, rhs) {
            return None;
        }

        Some(lhs_ty)
    }

    fn visit_compound_assignment(
        &mut self,
        node: NodeRef,
        arithmetic_op: BinaryOp,
        lhs: NodeRef,
        rhs: NodeRef,
        lhs_qt: QualType,
        rhs_qt: QualType,
    ) -> Option<QualType> {
        let (_, common_qt) = self.resolve_binary_operation_types(arithmetic_op, lhs, rhs, lhs_qt, rhs_qt)?;

        // Check assignment constraints (C11 6.5.16.1)
        let is_npc = self.is_null_pointer_constant(rhs);
        if !self.check_assignment_constraints(lhs_qt, common_qt, rhs, is_npc) {
            self.report_error(
                node,
                SemanticError::TypeMismatch {
                    expected: lhs_qt,
                    found: common_qt,
                },
            );
            return None;
        }

        if lhs_qt.ty() != common_qt.ty() {
            self.push_arithmetic_cast(node, common_qt.ty(), lhs_qt.ty());
        }

        Some(lhs_qt)
    }

    fn check_assignment_constraints(&self, lhs_qt: QualType, rhs_qt: QualType, _rhs: NodeRef, is_npc: bool) -> bool {
        let lhs_ty_canon = self.registry.canonical_qual_type(lhs_qt);
        let rhs_ty_canon = self.registry.canonical_qual_type(rhs_qt);

        // 0. Identical types
        if lhs_ty_canon.ty() == rhs_ty_canon.ty() {
            return true;
        }

        // 1. Arithmetic types
        if lhs_ty_canon.is_arithmetic() && rhs_ty_canon.is_arithmetic() {
            return true;
        }

        // 2. Structure or Union types
        if lhs_ty_canon.is_record() || rhs_ty_canon.is_record() {
            return lhs_ty_canon.is_record() && rhs_ty_canon.is_record() && lhs_ty_canon.ty() == rhs_ty_canon.ty();
        }

        // 3. Pointers
        if lhs_ty_canon.is_pointer() {
            if is_npc {
                return true;
            }

            // Resolve implicit decay for RHS to check compatibility
            let rhs_pointee = if rhs_ty_canon.is_array() {
                // Array qualifiers apply to the element type
                self.registry
                    .get_array_element(rhs_ty_canon.ty())
                    .map(|elem| QualType::new(elem, rhs_ty_canon.qualifiers()))
            } else if rhs_ty_canon.is_function() {
                Some(rhs_ty_canon) // Function decays to pointer to function (unqualified)
            } else if rhs_ty_canon.is_pointer() {
                self.registry.get_pointee(rhs_ty_canon.ty())
            } else {
                None
            };

            if let Some(rhs_base) = rhs_pointee {
                // Check compatibility
                let lhs_base = self.registry.get_pointee(lhs_ty_canon.ty()).unwrap();

                // void* wildcard
                if lhs_base.is_void() || rhs_base.is_void() {
                    return lhs_base.qualifiers().contains(rhs_base.qualifiers());
                }

                // Check compatibility ignoring top-level qualifiers of the pointed-to type
                // (e.g. char is compatible with char, even if one is const)
                if !self.registry.is_compatible(
                    QualType::unqualified(lhs_base.ty()),
                    QualType::unqualified(rhs_base.ty()),
                ) {
                    return false;
                }

                return lhs_base.qualifiers().contains(rhs_base.qualifiers());
            }

            return false;
        }

        // 4. _Bool = Pointer
        if lhs_ty_canon.ty() == self.registry.type_bool
            && (rhs_ty_canon.is_pointer() || rhs_ty_canon.is_array() || rhs_ty_canon.is_function())
        {
            return true;
        }

        false
    }

    fn record_implicit_conversions(&mut self, lhs_qt: QualType, rhs_qt: QualType, rhs: NodeRef, is_npc: bool) {
        let lhs_qt = self.registry.canonical_qual_type(lhs_qt);
        let mut rhs_qt = self.registry.canonical_qual_type(rhs_qt);
        // 1. Null pointer constant conversion (0 or (void*)0 -> T*)
        if lhs_qt.is_pointer() && is_npc {
            self.push_conversion(rhs, Conversion::NullPointerConstant);
            if lhs_qt.ty() != self.registry.type_void_ptr
                && lhs_qt.ty() != self.registry.type_bool
                && rhs_qt.ty() != self.registry.type_nullptr_t
            {
                self.push_conversion(
                    rhs,
                    Conversion::PointerCast {
                        from: self.registry.type_void_ptr,
                        to: lhs_qt.ty(),
                    },
                );
            }
            return;
        }

        // 2. Array/Function-to-pointer decay
        if lhs_qt.is_pointer() && (rhs_qt.is_array() || rhs_qt.is_function()) {
            rhs_qt = self.decay(rhs, rhs_qt);
        }

        // 3. Qualifier adjustment
        if lhs_qt.ty() == rhs_qt.ty() && lhs_qt.qualifiers() != rhs_qt.qualifiers() {
            self.push_conversion(
                rhs,
                Conversion::QualifierAdjust {
                    from: rhs_qt.qualifiers(),
                    to: lhs_qt.qualifiers(),
                },
            );
        }

        // 4. Casts (Integer or Pointer)
        if lhs_qt.ty() == rhs_qt.ty() {
            return;
        }

        if lhs_qt.is_pointer() && rhs_qt.is_pointer() {
            self.push_conversion(
                rhs,
                Conversion::PointerCast {
                    from: rhs_qt.ty(),
                    to: lhs_qt.ty(),
                },
            );
        } else if lhs_qt.is_arithmetic() && rhs_qt.is_arithmetic() {
            // If it's a constant literal, check if conversion changes value
            if self.is_numeric_literal(rhs)
                && !lhs_qt.ty().builtin().is_some_and(|b| b == BuiltinType::Bool)
                && let Some(val) = self.const_ctx().eval_int(rhs)
            {
                let truncated = self.registry.get(lhs_qt.ty()).as_ref().truncate_int(val);
                if truncated != val {
                    self.report_warning(
                        rhs,
                        SemanticError::ImplicitConstantConversion {
                            from: rhs_qt,
                            to: lhs_qt,
                            from_val: val,
                            to_val: truncated,
                        },
                    );
                }
            }

            self.push_arithmetic_cast(rhs, rhs_qt.ty(), lhs_qt.ty());
        }
    }

    fn check_string_array_init(&mut self, init: NodeRef, target_qt: QualType, init_qt: QualType) {
        let lhs_elem = self.registry.get_array_element(target_qt.ty()).unwrap();
        let rhs_elem = self.registry.get_array_element(init_qt.ty()).unwrap();

        let compatible = if rhs_elem == self.registry.type_char {
            [
                self.registry.type_char,
                self.registry.type_schar,
                self.registry.type_char_unsigned,
            ]
            .contains(&lhs_elem)
        } else {
            self.registry
                .is_compatible(QualType::unqualified(lhs_elem), QualType::unqualified(rhs_elem))
        };

        if !compatible {
            self.report_error(
                init,
                SemanticError::TypeMismatch {
                    expected: target_qt,
                    found: init_qt,
                },
            );
            return;
        }

        // Excess elements check: C11 §6.7.9p14
        if let TypeKind::Array {
            size: ArraySizeType::Constant(target_size),
            ..
        } = self.registry.get(target_qt.ty()).kind
            && let TypeKind::Array {
                size: ArraySizeType::Constant(init_size),
                ..
            } = self.registry.get(init_qt.ty()).kind
            && init_size.saturating_sub(1) > target_size
        {
            self.report_warning(init, SemanticError::ExcessElements { kind: "array" });
        }

        let is_npc = self.is_null_pointer_constant(init);
        self.record_implicit_conversions(target_qt, init_qt, init, is_npc);
    }

    fn find_member_index(&self, members: &[RecordMember], name: NameId) -> Option<usize> {
        members.iter().position(|m| {
            m.name == Some(name)
                || (m.name.is_none()
                    && self
                        .registry
                        .get(m.member_type.ty())
                        .find_member(self.registry, name)
                        .is_some())
        })
    }

    fn visit_init(&mut self, init: NodeRef, target_qt: QualType) {
        match self.ast.get_kind(init) {
            NodeKind::InitializerList(list) => {
                self.semantic_info.types[init.index()] = Some(target_qt);
                let list = *list;
                self.visit_init_list(&list, target_qt);
            }
            _ if self.is_string_literal(init) && target_qt.is_array() => {
                if let Some(init_qt) = self.visit_node(init) {
                    self.check_string_array_init(init, target_qt, init_qt);
                }
            }
            _ => {
                if let Some(init_qt) = self.visit_node(init) {
                    self.apply_lvalue_conversion(init);
                    self.validate_assignment(init, target_qt, init_qt, init);
                }
            }
        }
    }

    fn visit_init_list(&mut self, list: &InitializerList, target_qt: QualType) {
        if target_qt.is_complex() {
            self.visit_complex_init(list, target_qt);
            return;
        }

        if target_qt.is_scalar() {
            self.visit_scalar_init(list, target_qt);
            return;
        }

        // Bolt ⚡: Avoid cloning the entire TypeKind by extracting only the necessary parts.
        // We use a scoped block to ensure the Cow<Type> is dropped before calling other methods.
        let task = self.get_analysis_task(target_qt);

        match task {
            TypeAnalysisTask::Record(members, is_union) => self.visit_record_init(list, target_qt, &members, is_union),
            TypeAnalysisTask::Array(element_type, size) => self.visit_array_init(list, target_qt, element_type, &size),
            _ => {
                for item in list.init_start.range(list.init_len) {
                    self.visit_node(self.unwrap_init_item(item).0);
                }
            }
        }
    }

    fn report_excess_elements<I>(&mut self, iter: I, kind: &'static str)
    where
        I: Iterator<Item = NodeRef>,
    {
        for (i, item) in iter.enumerate() {
            if i == 0 {
                self.report_warning(item, SemanticError::ExcessElements { kind });
            }
            self.visit_node(self.unwrap_init_item(item).0);
        }
    }

    fn visit_complex_init(&mut self, list: &InitializerList, target_qt: QualType) {
        let base_type = if let TypeKind::Complex { base_type } = self.registry.get(target_qt.ty()).kind {
            base_type
        } else {
            unreachable!()
        };
        let base_qt = QualType::unqualified(base_type);

        let mut items = list.init_start.range(list.init_len);
        for _ in 0..2 {
            if let Some(item) = items.next() {
                let (expr, _, _) = self.unwrap_init_item(item);
                if let Some(init_qt) = self.visit_node(expr) {
                    self.apply_lvalue_conversion(expr);
                    self.validate_assignment(expr, base_qt, init_qt, expr);
                }
            }
        }
        self.report_excess_elements(items, "complex");
    }

    fn visit_scalar_init(&mut self, list: &InitializerList, target_qt: QualType) {
        let mut items = list.init_start.range(list.init_len);
        if let Some(first) = items.next() {
            let (expr, _, _) = self.unwrap_init_item(first);
            if let Some(init_qt) = self.visit_node(expr) {
                self.apply_lvalue_conversion(expr);
                self.validate_assignment(expr, target_qt, init_qt, expr);
            }
        }
        self.report_excess_elements(items, "scalar");
    }

    fn visit_record_init(
        &mut self,
        list: &InitializerList,
        target_qt: QualType,
        members: &[RecordMember],
        is_union: bool,
    ) {
        let mut iter = list.init_start.range(list.init_len).peekable();
        let mut member_idx = 0;
        let mut excess_reported = false;

        while let Some(item) = iter.peek().copied() {
            let mut designed = false;
            let (_expr, d_start, d_len) = self.unwrap_init_item(item);

            if d_len > 0 {
                let designator = d_start;
                if let NodeKind::Designator(Designator::FieldName(name)) = self.ast.get_kind(designator) {
                    if let Some(idx) = self.find_member_index(members, *name) {
                        member_idx = idx;
                        designed = true;
                    } else {
                        self.report_error(
                            designator,
                            SemanticError::MemberNotFound {
                                name: *name,
                                ty: target_qt,
                            },
                        );
                    }
                }
            }

            while member_idx < members.len()
                && members[member_idx].name.is_none()
                && members[member_idx].bit_field_size.is_some()
            {
                member_idx += 1;
            }

            if member_idx >= members.len() {
                if !excess_reported {
                    self.report_warning(item, SemanticError::ExcessElements { kind: "record" });
                    excess_reported = true;
                }
                self.visit_node(self.unwrap_init_item(item).0);
                iter.next();
                continue;
            }

            self.consume_inits(members[member_idx].member_type, &mut iter, if designed { 1 } else { 0 });
            member_idx = if is_union && !designed {
                members.len()
            } else {
                member_idx + 1
            };
        }
    }

    fn visit_array_init(
        &mut self,
        list: &InitializerList,
        target_qt: QualType,
        element_type: TypeRef,
        array_size: &ArraySizeType,
    ) {
        let element_qt = QualType::new(element_type, target_qt.qualifiers());

        // Special case for char array initialized by string literal (C11 §6.7.9p14)
        if (element_qt.is_char() || element_qt.is_wchar_t() || element_qt.is_char16() || element_qt.is_char32())
            && list.init_len == 1
        {
            let (expr, _, d_len) = self.unwrap_init_item(list.init_start);
            if d_len == 0 && self.is_string_literal(expr) {
                self.visit_node(expr);
                return;
            }
        }

        let max_index = if let ArraySizeType::Constant(n) = array_size {
            Some(*n)
        } else {
            None
        };
        let mut current_idx = 0;
        let mut iter = list.init_start.range(list.init_len).peekable();

        while let Some(item) = iter.peek().copied() {
            let (_, d_start, d_len) = self.unwrap_init_item(item);
            if d_len > 0 {
                let designator = d_start;
                if let NodeKind::Designator(d) = self.ast.get_kind(designator) {
                    match d {
                        Designator::ArrayIndex(e) => {
                            self.check_array_designator(*e);
                            if let Some(idx) = self.const_ctx().eval_int(*e) {
                                current_idx = idx;
                            }
                        }
                        Designator::ArrayRange(s, e) => {
                            self.check_array_designator(*s);
                            self.check_array_designator(*e);
                            if let Some(idx) = self.const_ctx().eval_int(*e) {
                                current_idx = idx;
                            }
                        }
                        Designator::FieldName(_) => {}
                    }
                }
            }

            if let Some(max) = max_index
                && current_idx >= max as i64
            {
                self.report_warning(item, SemanticError::ExcessElements { kind: "array" });
            }

            self.consume_inits(element_qt, &mut iter, 1);
            current_idx += 1;
        }
    }

    fn handle_designated_init<I>(
        &mut self,
        target_qt: QualType,
        iter: &mut std::iter::Peekable<I>,
        designator_idx: usize,
        designator: Designator,
    ) -> bool
    where
        I: Iterator<Item = NodeRef>,
    {
        // Bolt ⚡: Extract needed info without cloning the entire TypeKind.
        let task = self.get_analysis_task(target_qt);

        match designator {
            Designator::FieldName(name) => {
                let TypeAnalysisTask::Record(members, is_union) = task else {
                    return false;
                };

                let Some(idx) = self.find_member_index(&members, name) else {
                    return false;
                };

                self.consume_inits(members[idx].member_type, iter, designator_idx + 1);

                if !is_union {
                    for i in (idx + 1)..members.len() {
                        if iter.peek().is_none() || self.unwrap_init_item(*iter.peek().unwrap()).2 > 0 {
                            break;
                        }
                        self.consume_inits(members[i].member_type, iter, 0);
                    }
                }
                true
            }
            Designator::ArrayIndex(e) | Designator::ArrayRange(e, _) => {
                let TypeAnalysisTask::Array(element_type, size) = task else {
                    return false;
                };

                let mut end_idx = 0;
                if let Designator::ArrayRange(s, end) = designator {
                    self.check_array_designator(s);
                    self.check_array_designator(end);
                    if let Some(idx) = self.const_ctx().eval_int(end) {
                        end_idx = idx;
                    }
                } else {
                    self.check_array_designator(e);
                    if let Some(idx) = self.const_ctx().eval_int(e) {
                        end_idx = idx;
                    }
                }
                self.consume_inits(
                    QualType::new(element_type, target_qt.qualifiers()),
                    iter,
                    designator_idx + 1,
                );

                let max_len = if let ArraySizeType::Constant(len) = size {
                    Some(len)
                } else {
                    None
                };
                let mut current_idx = end_idx + 1;
                while max_len.is_none() || current_idx < max_len.unwrap() as i64 {
                    if iter.peek().is_none() || self.unwrap_init_item(*iter.peek().unwrap()).2 > 0 {
                        break;
                    }
                    self.consume_inits(QualType::new(element_type, target_qt.qualifiers()), iter, 0);
                    current_idx += 1;
                }
                true
            }
        }
    }

    fn handle_brace_elision_or_assignment<I>(
        &mut self,
        target_qt: QualType,
        iter: &mut std::iter::Peekable<I>,
        expr: NodeRef,
    ) where
        I: Iterator<Item = NodeRef>,
    {
        // Bolt ⚡: Optimized to avoid cloning TypeKind.
        let task = self.get_analysis_task(target_qt);

        match task {
            TypeAnalysisTask::Record(members, is_union) => {
                for member in members.iter() {
                    self.consume_inits(member.member_type, iter, 0);
                    if iter.peek().is_none() || self.unwrap_init_item(*iter.peek().unwrap()).2 > 0 || is_union {
                        break;
                    }
                }
            }
            TypeAnalysisTask::Array(element_type, size) => {
                let element_qt = QualType::new(element_type, target_qt.qualifiers());
                let max_len = if let ArraySizeType::Constant(len) = size {
                    Some(len)
                } else {
                    None
                };
                let mut count = 0;
                while max_len.is_none() || count < max_len.unwrap() {
                    self.consume_inits(element_qt, iter, 0);
                    if iter.peek().is_none() || self.unwrap_init_item(*iter.peek().unwrap()).2 > 0 {
                        break;
                    }
                    count += 1;
                }
            }
            _ => {
                if let Some(init_ty) = self.visit_node(expr) {
                    self.apply_lvalue_conversion(expr);
                    self.validate_assignment(expr, target_qt, init_ty, expr);
                }
                iter.next();
            }
        }
    }

    fn consume_inits<I>(&mut self, target_qt: QualType, iter: &mut std::iter::Peekable<I>, designator_idx: usize)
    where
        I: Iterator<Item = NodeRef>,
    {
        let Some(item) = iter.peek().copied() else { return };
        let (expr, d_start, d_len) = self.unwrap_init_item(item);
        let has_more_designators = (designator_idx as u16) < d_len;

        if has_more_designators {
            let designator_node = d_start.add_offset(designator_idx as u16);
            let kind = *self.ast.get_kind(designator_node);
            if let NodeKind::Designator(d) = kind
                && self.handle_designated_init(target_qt, iter, designator_idx, d)
            {
                return;
            }
        }

        // C11 §6.7.9p14: Character array initialized by string literal
        if target_qt.is_array()
            && !has_more_designators
            && let Some(element_ty) = self.registry.get_array_element(target_qt.ty())
            && (element_ty.is_char() || element_ty.is_wchar_t())
            && self.is_string_literal(expr)
        {
            self.visit_node(expr);
            iter.next();
            return;
        }

        // C11 §6.7.9p13: Struct/Union initialization by compatible expression
        if target_qt.is_record()
            && !has_more_designators
            && let Some(init_ty) = self.visit_node(expr)
        {
            self.apply_lvalue_conversion(expr);
            let is_npc = self.is_null_pointer_constant(expr);
            if self.check_assignment_constraints(target_qt, init_ty, expr, is_npc) {
                self.record_implicit_conversions(target_qt, init_ty, expr, is_npc);
                iter.next();
                return;
            }
        }

        // Braced initializer list or Brace elision
        if !has_more_designators && matches!(self.ast.get_kind(expr), NodeKind::InitializerList(_)) {
            self.visit_init(expr, target_qt);
            iter.next();
        } else {
            self.handle_brace_elision_or_assignment(target_qt, iter, expr);
        }
    }

    fn visit_function_call(&mut self, call_expr: &CallExpr) -> Option<QualType> {
        let (builtin_kind, atomic_op) = self.identify_builtin(call_expr.callee);
        let func_qt = self.visit_node(call_expr.callee)?;
        let actual_func_qt = self.resolve_actual_function_type(func_qt);

        let task = self.get_analysis_task(actual_func_qt);
        match task {
            TypeAnalysisTask::Function {
                return_type,
                parameters,
                is_variadic,
            } => {
                let mut atomic_pointee = None;
                let arg_count = call_expr.arg_len as usize;

                if let Some(op) = atomic_op {
                    let expected_args = match op {
                        AtomicOp::LoadN => 2,
                        AtomicOp::CompareExchangeN => 6,
                        _ => 3,
                    };

                    if arg_count != expected_args {
                        self.report_error(
                            call_expr.callee,
                            SemanticError::InvalidNumberOfArguments {
                                expected: expected_args,
                                found: arg_count,
                            },
                        );
                    }
                } else if !is_variadic && arg_count != parameters.len() {
                    self.report_error(
                        call_expr.callee,
                        SemanticError::InvalidNumberOfArguments {
                            expected: parameters.len(),
                            found: arg_count,
                        },
                    );
                }

                for (i, arg_node) in call_expr.arg_start.range(call_expr.arg_len).enumerate() {
                    let Some(arg_qt) = self.visit_node(arg_node) else {
                        continue;
                    };
                    self.apply_lvalue_conversion(arg_node);

                    if let Some(kind) = builtin_kind {
                        self.validate_builtin_arg(kind, i, arg_node, arg_qt, &mut atomic_pointee);
                    }

                    if i < parameters.len() {
                        let actual_arg_qt = self.decay(arg_node, arg_qt);
                        self.validate_assignment(arg_node, parameters[i].param_type, actual_arg_qt, arg_node);
                    } else if is_variadic {
                        self.handle_variadic_argument(arg_node, arg_qt);
                    }
                }

                Some(self.resolve_call_return_type(builtin_kind, atomic_pointee, return_type))
            }
            _ => {
                // This is not a function or function pointer, report an error.
                self.report_error(
                    call_expr.callee,
                    SemanticError::CalledNonFunctionType { ty: actual_func_qt },
                );

                // Still visit arguments to catch other potential errors within them.
                for arg_node in call_expr.arg_start.range(call_expr.arg_len) {
                    self.visit_node(arg_node);
                }
                None // Return None as the call is invalid
            }
        }
    }

    fn identify_builtin(&self, callee: NodeRef) -> (Option<BuiltinFunctionKind>, Option<AtomicOp>) {
        if let NodeKind::Ident(_, sym_ref) = self.ast.get_kind(callee) {
            let sym = self.symbol_table.get_symbol(*sym_ref);
            if let SymbolKind::Function(f) = &sym.kind {
                return (f.builtin_kind, f.builtin_kind.and_then(|k| k.to_atomic_op()));
            }
        }
        (None, None)
    }

    fn resolve_actual_function_type(&self, func_qt: QualType) -> QualType {
        if func_qt.is_pointer() {
            self.registry.get_pointee(func_qt.ty()).unwrap_or(func_qt)
        } else {
            func_qt
        }
    }

    fn handle_variadic_argument(&mut self, arg_node: NodeRef, arg_qt: QualType) {
        let mut actual_arg_qt = arg_qt;
        if arg_qt.is_array() || arg_qt.is_function() {
            actual_arg_qt = self.registry.decay(arg_qt, TypeQualifiers::empty());
            self.push_conversion(arg_node, Conversion::PointerDecay { to: actual_arg_qt.ty() });
        }

        let promoted_qt = crate::semantic::conversions::default_argument_promotions(self.registry, actual_arg_qt);

        if promoted_qt.ty() != actual_arg_qt.ty() {
            let is_npc = self.is_null_pointer_constant(arg_node);
            self.record_implicit_conversions(promoted_qt, actual_arg_qt, arg_node, is_npc);
        }
    }

    fn validate_builtin_arg(
        &mut self,
        kind: BuiltinFunctionKind,
        i: usize,
        arg_node: NodeRef,
        arg_qt: QualType,
        atomic_pointee: &mut Option<QualType>,
    ) {
        if kind.is_bitwise() && i == 0 {
            let check_qt = if arg_qt.is_array() || arg_qt.is_function() {
                self.registry.decay(arg_qt, TypeQualifiers::empty())
            } else {
                arg_qt
            };
            if !check_qt.is_integer() {
                self.report_error(arg_node, SemanticError::ExpectedIntegerType { found: check_qt });
            }
        } else if kind.is_fabs() && i == 0 {
            let check_qt = if arg_qt.is_array() || arg_qt.is_function() {
                self.registry.decay(arg_qt, TypeQualifiers::empty())
            } else {
                arg_qt
            };
            if !check_qt.is_floating() {
                self.report_error(arg_node, SemanticError::ExpectedFloatingType { found: check_qt });
            }
        }

        match kind {
            BuiltinFunctionKind::Memcpy | BuiltinFunctionKind::Memmove | BuiltinFunctionKind::Memcmp => {
                let void_ptr = QualType::unqualified(self.registry.type_void_ptr);
                let const_void = QualType::new(self.registry.type_void, TypeQualifiers::CONST);
                let const_void_ptr = QualType::unqualified(self.registry.pointer_to(const_void));
                let size_t = QualType::unqualified(self.registry.type_long_unsigned);

                if i == 0 {
                    self.validate_assignment(
                        arg_node,
                        if kind == BuiltinFunctionKind::Memcmp {
                            const_void_ptr
                        } else {
                            void_ptr
                        },
                        arg_qt,
                        arg_node,
                    );
                } else if i == 1 {
                    self.validate_assignment(arg_node, const_void_ptr, arg_qt, arg_node);
                } else if i == 2 {
                    self.validate_assignment(arg_node, size_t, arg_qt, arg_node);
                }
            }
            BuiltinFunctionKind::Memset => {
                let void_ptr = QualType::unqualified(self.registry.type_void_ptr);
                let int_ty = QualType::unqualified(self.registry.type_int);
                let size_t = QualType::unqualified(self.registry.type_long_unsigned);

                if i == 0 {
                    self.validate_assignment(arg_node, void_ptr, arg_qt, arg_node);
                } else if i == 1 {
                    self.validate_assignment(arg_node, int_ty, arg_qt, arg_node);
                } else if i == 2 {
                    self.validate_assignment(arg_node, size_t, arg_qt, arg_node);
                }
            }
            BuiltinFunctionKind::Prefetch => {
                if i == 0 {
                    let void_ptr = QualType::unqualified(self.registry.type_void_ptr);
                    self.validate_assignment(arg_node, void_ptr, arg_qt, arg_node);
                } else if i == 1 {
                    // rw
                    if !arg_qt.is_integer() {
                        self.report_error(arg_node, SemanticError::ExpectedIntegerType { found: arg_qt });
                    } else if let Some(v) = self.const_ctx().eval_int(arg_node) {
                        if v != 0 && v != 1 {
                            self.report_error(arg_node, SemanticError::BuiltinPrefetchOutOfRange { arg: "rw" });
                        }
                    } else {
                        self.report_error(arg_node, SemanticError::BuiltinPrefetchNotConstant { arg: "rw" });
                    }
                } else if i == 2 {
                    // locality
                    if !arg_qt.is_integer() {
                        self.report_error(arg_node, SemanticError::ExpectedIntegerType { found: arg_qt });
                    } else if let Some(v) = self.const_ctx().eval_int(arg_node) {
                        if !(0..=3).contains(&v) {
                            self.report_error(arg_node, SemanticError::BuiltinPrefetchOutOfRange { arg: "locality" });
                        }
                    } else {
                        self.report_error(arg_node, SemanticError::BuiltinPrefetchNotConstant { arg: "locality" });
                    }
                }
            }
            BuiltinFunctionKind::AddOverflow | BuiltinFunctionKind::SubOverflow | BuiltinFunctionKind::MulOverflow => {
                if i == 0 || i == 1 {
                    if !arg_qt.is_integer() {
                        self.report_error(arg_node, SemanticError::ExpectedIntegerType { found: arg_qt });
                    }
                } else if i == 2 {
                    if let Some(pointee) = self.registry.get_pointee(arg_qt.ty()) {
                        if !pointee.is_integer() {
                            self.report_error(arg_node, SemanticError::ExpectedIntegerType { found: pointee });
                        }
                    } else {
                        self.report_error(arg_node, SemanticError::IndirectionRequiresPointer { ty: arg_qt });
                    }
                }
            }
            _ => {
                if let Some(op) = kind.to_atomic_op() {
                    self.validate_atomic_arg(op, i, arg_node, arg_qt, atomic_pointee);
                }
            }
        }
    }

    fn validate_atomic_arg(
        &mut self,
        op: AtomicOp,
        i: usize,
        arg_node: NodeRef,
        arg_qt: QualType,
        atomic_pointee: &mut Option<QualType>,
    ) {
        if i == 0 {
            if let Some(p) = self.registry.get_pointee(arg_qt.ty()) {
                *atomic_pointee = Some(p);
            } else {
                self.report_error(arg_node, SemanticError::IndirectionRequiresPointer { ty: arg_qt });
            }
        }

        let is_memorder = match op {
            AtomicOp::LoadN => i == 1,
            AtomicOp::CompareExchangeN => i == 4 || i == 5,
            _ => i == 2,
        };

        if is_memorder {
            self.require_integer(arg_node, arg_qt);
        }

        if let Some(pointee) = *atomic_pointee {
            match op {
                AtomicOp::StoreN if i == 1 => {
                    self.validate_assignment(arg_node, pointee, arg_qt, arg_node);
                }
                AtomicOp::ExchangeN if i == 1 => {
                    self.validate_assignment(arg_node, pointee, arg_qt, arg_node);
                }
                AtomicOp::CompareExchangeN => {
                    if i == 1 {
                        if let Some(expected_pointee) = self.registry.get_pointee(arg_qt.ty()) {
                            if !self.registry.is_compatible(pointee.strip_all(), expected_pointee) {
                                let expected_ptr_ty = self.registry.pointer_to(pointee);
                                self.report_error(
                                    arg_node,
                                    SemanticError::IncompatiblePointerTypes {
                                        expected: QualType::unqualified(expected_ptr_ty),
                                        found: arg_qt,
                                    },
                                );
                            }
                        } else {
                            self.report_error(arg_node, SemanticError::IndirectionRequiresPointer { ty: arg_qt });
                        }
                    } else if i == 2 {
                        self.validate_assignment(arg_node, pointee, arg_qt, arg_node);
                    }
                }
                AtomicOp::FetchAdd
                | AtomicOp::FetchSub
                | AtomicOp::FetchAnd
                | AtomicOp::FetchOr
                | AtomicOp::FetchXor
                | AtomicOp::AddFetch
                | AtomicOp::SubFetch
                | AtomicOp::AndFetch
                | AtomicOp::OrFetch
                | AtomicOp::XorFetch
                    if i == 1 =>
                {
                    if matches!(
                        op,
                        AtomicOp::FetchAnd
                            | AtomicOp::FetchOr
                            | AtomicOp::FetchXor
                            | AtomicOp::AndFetch
                            | AtomicOp::OrFetch
                            | AtomicOp::XorFetch
                    ) && !pointee.is_integer()
                    {
                        self.report_error(arg_node, SemanticError::ExpectedIntegerType { found: pointee });
                    }
                    if pointee.is_integer() {
                        self.validate_assignment(arg_node, pointee, arg_qt, arg_node);
                    }
                }
                _ => {}
            }
        }
    }

    fn resolve_call_return_type(
        &self,
        builtin_kind: Option<BuiltinFunctionKind>,
        atomic_pointee: Option<QualType>,
        default_ret: TypeRef,
    ) -> QualType {
        if let (Some(op), Some(pointee)) = (builtin_kind.and_then(|k| k.to_atomic_op()), atomic_pointee) {
            match op {
                AtomicOp::LoadN
                | AtomicOp::ExchangeN
                | AtomicOp::FetchAdd
                | AtomicOp::FetchSub
                | AtomicOp::FetchAnd
                | AtomicOp::FetchOr
                | AtomicOp::FetchXor
                | AtomicOp::AddFetch
                | AtomicOp::SubFetch
                | AtomicOp::AndFetch
                | AtomicOp::OrFetch
                | AtomicOp::XorFetch => pointee,
                AtomicOp::StoreN => QualType::unqualified(self.registry.type_void),
                AtomicOp::CompareExchangeN => QualType::unqualified(self.registry.type_bool),
            }
        } else {
            QualType::unqualified(default_ret)
        }
    }

    fn visit_member_access(&mut self, node: NodeRef, field_name: NameId, is_arrow: bool) -> Option<QualType> {
        let NodeKind::MemberAccess(obj, _, _) = self.ast.get_kind(node) else {
            unreachable!()
        };
        let obj_qt = self.visit_node(*obj)?;

        let (record_ty, base_quals) = if is_arrow {
            // Decay array/function to pointer if needed
            let actual_qt = self.decay(*obj, obj_qt);

            let pointee = self.registry.get_pointee(actual_qt.ty());

            match pointee {
                Some(p) => (p.ty(), p.qualifiers()),
                None => {
                    self.report_error(node, SemanticError::MemberAccessOnNonRecord { ty: actual_qt });
                    return None;
                }
            }
        } else {
            (obj_qt.ty(), obj_qt.qualifiers())
        };

        // Ensure layout is computed for the record type
        let _ = self.registry.ensure_layout(record_ty);

        // Recursive helper to find member (handling anonymous structs/unions)
        if !record_ty.is_record() {
            self.report_error(
                node,
                SemanticError::MemberAccessOnNonRecord {
                    ty: QualType::unqualified(record_ty),
                },
            );
            return None;
        }

        if let TypeKind::Record { is_complete: false, .. } = &self.registry.get(record_ty).kind {
            self.report_error(
                node,
                SemanticError::IncompleteType {
                    ty: QualType::unqualified(record_ty),
                },
            );
            return None;
        }

        if let Some(mut ty) = self
            .registry
            .get(record_ty)
            .find_member(self.registry, field_name)
            .map(|m| m.member_type)
        {
            // C11 6.5.2.3p4: if the first expression has qualified type, the result has the so-qualified
            // version of the type of the designated member.
            if !base_quals.is_empty() {
                ty = ty.merge_qualifiers(base_quals);
            }

            // Bolt ⚡: Eagerly set value category to LValue if arrow or base is LValue.
            if is_arrow || self.semantic_info.value_categories[obj.index()] == ValueCategory::LValue {
                self.semantic_info.value_categories[node.index()] = ValueCategory::LValue;
            }

            return Some(ty);
        }

        self.report_error(
            node,
            SemanticError::MemberNotFound {
                name: field_name,
                ty: QualType::unqualified(record_ty),
            },
        );
        None
    }

    fn visit_index_access(&mut self, arr: NodeRef, idx: NodeRef, node: NodeRef) -> Option<QualType> {
        let arr_ty = self.visit_node(arr)?;
        self.apply_lvalue_conversion(arr);
        let arr_ty = self.decay(arr, arr_ty);
        let idx_ty = self.visit_node(idx)?;
        self.apply_lvalue_conversion(idx);
        let idx_ty = self.decay(idx, idx_ty);

        // Handle both arr[idx] and idx[arr] (subscripting is commutative in C)
        // C11 6.5.2.1p1: "one of the expressions shall have type 'pointer to complete object type',
        // and the other shall have integer type."
        let (sequence_qt, index_ty, sequence, index) = if arr_ty.is_pointer() {
            (arr_ty, idx_ty, arr, idx)
        } else if idx_ty.is_pointer() {
            (idx_ty, arr_ty, idx, arr)
        } else {
            self.report_error(arr, SemanticError::ExpectedArrayType { found: arr_ty });
            return None;
        };

        if !index_ty.is_integer() {
            self.report_error(index, SemanticError::ExpectedIntegerType { found: index_ty });
        }

        // Bolt ⚡: Eagerly set value category to LValue for index access.
        self.semantic_info.value_categories[node.index()] = ValueCategory::LValue;

        let pointee = self.registry.get_pointee(sequence_qt.ty()).unwrap();

        // C11 6.5.2.1p1: pointee must be a complete object type.
        // A function type is not an object type.
        if !self.registry.is_complete(pointee.ty()) || pointee.is_function() {
            self.report_error(sequence, SemanticError::SubscriptIncompleteType { ty: pointee });
        }

        Some(pointee)
    }

    fn visit_declaration_node(&mut self, node: NodeRef, kind: &NodeKind) -> Option<QualType> {
        match kind {
            NodeKind::TranslationUnit(tu_data) => {
                for decl in tu_data.decl_start.range(tu_data.decl_len) {
                    self.visit_node(decl);
                }
                None
            }
            NodeKind::FunctionDef(data) => self.visit_function_definition(data, node),
            NodeKind::Param(data) => {
                self.visit_type_exprs(data.qt);
                Some(data.qt)
            }
            NodeKind::VarDecl(data) => self.visit_var_declaration(data, node),
            NodeKind::EnumDecl(data) => {
                for member in data.member_start.range(data.member_len) {
                    self.visit_node(member);
                }
                None
            }
            NodeKind::EnumMember(data) => {
                if let Some(expr) = data.init_expr {
                    self.visit_node(expr);
                }
                Some(QualType::unqualified(self.registry.type_int))
            }
            NodeKind::RecordDecl(_) => None,
            NodeKind::FieldDecl(data) => {
                self.visit_type_exprs(data.qt);
                None
            }
            NodeKind::TypedefDecl(data) => {
                let sym = self.symbol_table.get_symbol(data.symbol);
                self.visit_type_exprs(sym.type_info);
                None
            }
            NodeKind::FunctionDecl(data) => {
                let sym = self.symbol_table.get_symbol(data.symbol);
                self.visit_type_exprs(sym.type_info);

                if let TypeAnalysisTask::Function { parameters, .. } = self.get_analysis_task(sym.type_info) {
                    // Bolt ⚡: Iterate directly over the parameters Arc to avoid redundant Vec allocation.
                    // This is safe because parameters is a local Arc clone and doesn't borrow from self.
                    for p in parameters.iter() {
                        let _ = self.registry.ensure_layout(p.param_type.ty());
                    }
                }

                None
            }
            _ => None,
        }
    }

    fn visit_function_definition(&mut self, data: &FunctionDef, node: NodeRef) -> Option<QualType> {
        let symbol = self.symbol_table.get_symbol(data.symbol);
        let ret_type = if let TypeAnalysisTask::Function { return_type, .. } = self.get_analysis_task(symbol.type_info)
        {
            return_type
        } else {
            self.registry.type_error
        };

        if !self.registry.is_complete(ret_type) && ret_type != self.registry.type_void {
            self.report_error(node, SemanticError::IncompleteReturnType);
        }

        let SymbolKind::Function(f) = &symbol.kind else {
            unreachable!("ICE: Function node refers to non-function symbol")
        };
        let param_len = f.param_len;
        let is_noreturn = f.is_noreturn;

        let prev_ctx = self.current_function.take();
        self.current_function = Some(FunctionCtx {
            ret_type: QualType::unqualified(ret_type),
            name: symbol.name,
            is_noreturn,
        });

        for param in data.child_start.range(param_len) {
            self.visit_node(param);
        }

        let body_node = data.child_start.add_offset(param_len);
        self.visit_node(body_node);

        if let Some(ctx) = self.current_function
            && ctx.is_noreturn
            && self.can_fall_through(body_node)
        {
            self.report_error(node, SemanticError::NoreturnFunctionFallsOff { name: ctx.name });
        }

        // Validate goto statements
        for (goto_node, source_vlas) in std::mem::take(&mut self.goto_vla_state) {
            let NodeKind::Goto(_, sym) = self.ast.get_kind(goto_node) else {
                continue;
            };
            let Some(&(label_span, ref target_vlas)) = self.label_vla_state.get(sym) else {
                continue;
            };

            // If there's a VLA in target_vlas that is NOT in source_vlas, it's a jump into scope.
            let Some(&vla) = target_vlas.iter().find(|v| !source_vlas.contains(v)) else {
                continue;
            };

            let mut notes = vec![];

            // Note where label is defined
            let label_name = self.symbol_table.get_symbol(*sym).name;
            notes.push((label_span, SemanticError::NoteLabelDefinedHere { name: label_name }));

            // Note where VLA is declared
            if let NodeKind::VarDecl(var_data) = self.ast.get_kind(vla) {
                let name = self.symbol_table.get_symbol(var_data.symbol).name;
                notes.push((self.ast.get_span(vla), SemanticError::NoteVLADeclaredHere { name }));
            }

            self.report_error_with_notes(goto_node, SemanticError::JumpIntoScopeVLA { is_switch: false }, notes);
        }
        self.goto_vla_state.clear();
        self.label_vla_state.clear();

        self.current_function = prev_ctx;
        None
    }

    fn visit_var_declaration(&mut self, data: &VarDecl, node: NodeRef) -> Option<QualType> {
        let sym = self.symbol_table.get_symbol(data.symbol);
        let qt = sym.type_info;
        let storage = if let SymbolKind::Variable(v) = &sym.kind {
            v.storage
        } else {
            None
        };

        if self.registry.is_variably_modified(qt.ty()) {
            self.active_vlas.push(node);
        }
        if qt.is_void() {
            self.report_error(node, SemanticError::VariableOfVoidType);
        }
        self.visit_type_exprs(qt);
        let _ = self.registry.ensure_layout(qt.ty());
        if data.init.is_some() && matches!(storage, Some(StorageClass::Extern)) && self.current_function.is_some() {
            self.report_error(node, SemanticError::InvalidInitializer);
        }

        if let Some(init) = data.init {
            // C11 6.7.9p3: VLA may not be initialized
            if self.registry.is_vla_type(qt.ty()) {
                let is_empty_init = if let NodeKind::InitializerList(list) = self.ast.get_kind(init) {
                    list.init_len == 0
                } else {
                    false
                };

                if !is_empty_init || self.lang_opts.c_standard < CStandard::C23 {
                    self.report_error(node, SemanticError::VlaInitializerNotAllowed);
                }
            }
            self.visit_init(init, qt);
        }
        Some(qt)
    }

    fn visit_statement_node(&mut self, node: NodeRef, kind: &NodeKind) -> Option<QualType> {
        match kind {
            NodeKind::CompoundStmt(cs) => {
                let prev_vla_count = self.active_vlas.len();
                for item in cs.stmt_start.range(cs.stmt_len) {
                    self.visit_node(item);
                }
                self.active_vlas.truncate(prev_vla_count);
                self.process_deferred_checks();
                None
            }

            NodeKind::DeclList(dl) => {
                for item in dl.stmt_start.range(dl.stmt_len) {
                    self.visit_node(item);
                }
                None
            }

            NodeKind::If(stmt) => {
                self.visit_if_statement(stmt);
                None
            }
            NodeKind::While(stmt) => {
                self.visit_while_statement(stmt);
                None
            }
            NodeKind::For(stmt) => {
                self.visit_for_statement(stmt);
                None
            }
            NodeKind::DoWhile(body, condition) => {
                self.loop_depth += 1;
                self.visit_node(*body);
                self.loop_depth -= 1;
                self.check_scalar_condition(*condition);
                None
            }
            NodeKind::Switch(cond, body) => self.visit_switch_statement(*cond, *body, node),
            NodeKind::Case(expr, stmt) => self.visit_case_statement(Some(*expr), None, *stmt, node),
            NodeKind::CaseRange(start, end, stmt) => self.visit_case_statement(Some(*start), Some(*end), *stmt, node),
            NodeKind::Default(stmt) => self.visit_default_statement(*stmt, node),
            NodeKind::Return(expr) => {
                self.visit_return_statement(node, expr);
                None
            }
            NodeKind::ExpressionStmt(expr) => {
                if let Some(expr) = expr {
                    self.visit_node(*expr);
                    self.apply_lvalue_conversion(*expr);
                }
                None
            }
            NodeKind::AsmStmt(data) => {
                for op_node in data.output_start.range(data.output_len) {
                    if let NodeKind::AsmConstraint(c) = self.ast.get_kind(op_node) {
                        self.visit_node(c.expr);
                        if !self.is_lvalue(c.expr) {
                            self.report_error(c.expr, SemanticError::NotAnLvalue);
                        }
                    }
                }
                for op_node in data.input_start.range(data.input_len) {
                    if let NodeKind::AsmConstraint(c) = self.ast.get_kind(op_node) {
                        self.visit_node(c.expr);
                        self.apply_lvalue_conversion(c.expr);
                    }
                }
                None
            }
            NodeKind::StaticAssert(_expr, _msg) => {
                self.deferred_checks.push(DeferredCheck::StaticAssert(node));
                None
            }
            NodeKind::Break => {
                if self.loop_depth == 0 && self.switch_stack.is_empty() {
                    self.report_error(node, SemanticError::BreakNotInLoop);
                }
                None
            }
            NodeKind::Continue => {
                if self.loop_depth == 0 {
                    self.report_error(node, SemanticError::ContinueNotInLoop);
                }
                None
            }
            NodeKind::Goto(_, _) => {
                self.goto_vla_state.push((node, self.active_vlas.clone()));
                None
            }
            NodeKind::ComputedGoto(expr) => {
                self.goto_vla_state.push((node, self.active_vlas.clone()));
                let ty = self.visit_node(*expr);
                if let Some(t) = ty
                    && !t.is_pointer()
                {
                    self.report_error(node, SemanticError::ExpectedPointerType { found: t });
                }
                None
            }
            NodeKind::Label(_, stmt, sym) => {
                let span = self.ast.get_span(node);
                self.label_vla_state.insert(*sym, (span, self.active_vlas.clone()));
                self.visit_node(*stmt);
                None
            }
            _ => None,
        }
    }

    fn visit_switch_statement(&mut self, cond: NodeRef, body: NodeRef, node: NodeRef) -> Option<QualType> {
        let cond_ty = self.visit_node(cond);
        self.apply_lvalue_conversion(cond);

        let (orig_ty, promoted_ty) = if let Some(ty) = cond_ty {
            let effective_ty = if !ty.is_integer() {
                self.report_error(cond, SemanticError::InvalidSwitchCondition { ty });
                QualType::unqualified(self.registry.type_int)
            } else {
                ty
            };
            let promoted = self.apply_integer_promotion(cond, effective_ty);
            (effective_ty, promoted)
        } else {
            let int_ty = QualType::unqualified(self.registry.type_int);
            (int_ty, int_ty)
        };

        self.switch_stack.push(SwitchCtx {
            cases: SmallVec::new(),
            default_seen: false,
            cond_type: promoted_ty,
            orig_cond_type: orig_ty,
            vla_state: (node, self.active_vlas.len()),
        });

        self.visit_node(body);

        self.switch_stack.pop();
        None
    }

    fn evaluate_case_value(&mut self, node: NodeRef) -> Option<i64> {
        let ty = self.visit_node(node);
        let val = self.const_ctx().eval_int(node);
        if !self.switch_stack.is_empty() && (val.is_none() || ty.is_none_or(|t| !t.is_integer())) {
            self.report_error(node, SemanticError::NonConstantCaseValue);
        }
        val
    }

    fn truncate_case_value(&mut self, val: i64, node: NodeRef) -> i64 {
        let Some(ctx) = self.switch_stack.last() else {
            return val;
        };
        let truncated = self.registry.get(ctx.cond_type.ty()).truncate_int(val);

        let orig_truncated = self.registry.get(ctx.orig_cond_type.ty()).truncate_int(val);
        if orig_truncated != val {
            self.report_warning(
                node,
                SemanticError::SwitchCaseOverflow {
                    from_val: val,
                    to_val: orig_truncated,
                },
            );
        }
        truncated
    }

    fn check_switch_vla_jump(&mut self, node: NodeRef) {
        let Some(ctx) = self.switch_stack.last() else {
            return;
        };

        let (switch_node, switch_vla_count) = ctx.vla_state;
        if self.active_vlas.len() <= switch_vla_count {
            return;
        }

        // We jumped into the scope of a VLA that wasn't in scope at the switch header.
        // C11 6.8.4.2p4: "A switch statement ... shall not jump into the scope of an identifier
        // with a variably modified type."
        let vla = self.active_vlas[switch_vla_count];
        let switch_span = self.ast.get_span(switch_node);

        let mut notes = vec![];
        notes.push((switch_span, SemanticError::NoteSwitchStartsHere));

        // Also note where the VLA was declared
        if let NodeKind::VarDecl(var_data) = self.ast.get_kind(vla) {
            let name = self.symbol_table.get_symbol(var_data.symbol).name;
            notes.push((self.ast.get_span(vla), SemanticError::NoteVLADeclaredHere { name }));
        }

        self.report_error_with_notes(node, SemanticError::JumpIntoScopeVLA { is_switch: true }, notes);
    }

    fn visit_case_statement(
        &mut self,
        start: Option<NodeRef>,
        end: Option<NodeRef>,
        stmt: NodeRef,
        node: NodeRef,
    ) -> Option<QualType> {
        if self.switch_stack.is_empty() {
            self.report_error(node, SemanticError::CaseNotInSwitch);
        }

        let mut start_val = start.and_then(|s| self.evaluate_case_value(s));
        let mut end_val = end.and_then(|e| self.evaluate_case_value(e)).or(start_val);

        if !self.switch_stack.is_empty() && start.is_some() {
            start_val = start_val.map(|v| self.truncate_case_value(v, start.unwrap()));
            end_val = if let Some(end_node) = end {
                end_val.map(|v| self.truncate_case_value(v, end_node))
            } else {
                start_val
            };

            if let (Some(s_v), Some(e_v)) = (start_val, end_val)
                && let Some(ctx) = self.switch_stack.last_mut()
            {
                let range = CaseRangeInterval { start: s_v, end: e_v };

                // Bolt ⚡: Binary search for overlap and insertion position.
                // ctx.cases is maintained in sorted order by start value.
                // partition_point finds the first element whose start is >= range.start.
                let idx = ctx.cases.partition_point(|c| c.start < range.start);

                // Check overlap with the found element (it's the first one that could overlap from the right)
                let mut overlapped = ctx.cases.get(idx).filter(|c| c.overlaps(&range));

                // Check overlap with the previous element (it's the only one that could overlap from the left)
                if overlapped.is_none() && idx > 0 {
                    overlapped = ctx.cases.get(idx - 1).filter(|c| c.overlaps(&range));
                }

                if let Some(existing) = overlapped {
                    let duplicate = std::cmp::max(existing.start, range.start);
                    self.report_error(stmt, SemanticError::DuplicateCase { value: duplicate });
                } else {
                    ctx.cases.insert(idx, range);
                }
            }
        }

        self.check_switch_vla_jump(stmt);
        self.visit_node(stmt);
        None
    }

    fn visit_default_statement(&mut self, stmt: NodeRef, node: NodeRef) -> Option<QualType> {
        if self.switch_stack.is_empty() {
            self.report_error(node, SemanticError::CaseNotInSwitch);
        } else {
            let is_duplicate = self
                .switch_stack
                .last_mut()
                .map(|ctx| std::mem::replace(&mut ctx.default_seen, true))
                .unwrap_or(false);
            if is_duplicate {
                self.report_error(node, SemanticError::MultipleDefaultLabels);
            }
        }

        self.check_switch_vla_jump(node);
        self.visit_node(stmt);
        None
    }

    fn visit_expression_node(&mut self, node: NodeRef, kind: &NodeKind) -> Option<QualType> {
        match kind {
            NodeKind::Literal(l) => self.visit_literal(*l, node),
            NodeKind::Ident(_, sym) => {
                let symbol = self.symbol_table.get_symbol(*sym);
                // Bolt ⚡: Eagerly set value category to LValue for variables and functions.
                if matches!(symbol.kind, SymbolKind::Variable(_) | SymbolKind::Function(_)) {
                    self.semantic_info.value_categories[node.index()] = ValueCategory::LValue;
                }
                // Use symbol.type_info for all symbols including enum constants.
                // For enum constants, type_info is set to the enum's underlying integer type
                // during lowering, matching GCC's extension (not always plain 'int' per strict C11).
                Some(symbol.type_info)
            }
            NodeKind::UnaryOp(op, operand) => self.visit_unary_op(node, *op, *operand),
            NodeKind::BinaryOp(op, lhs, rhs) => self.visit_binary_op(*op, *lhs, *rhs),
            NodeKind::TernaryOp(cond, then, else_expr) => self.visit_ternary_op(*cond, *then, *else_expr),
            NodeKind::StatementExpr(stmt, result_expr) => self.visit_statement_expr(*stmt, *result_expr),
            NodeKind::PostIncrement(expr) | NodeKind::PostDecrement(expr) => self.visit_post_inc_dec(node, *expr),
            NodeKind::Assignment(op, lhs, rhs) => self.visit_assignment(node, *op, *lhs, *rhs),
            NodeKind::FunctionCall(call_expr) => self.visit_function_call(call_expr),
            NodeKind::MemberAccess(_, field_name, is_arrow) => self.visit_member_access(node, *field_name, *is_arrow),
            NodeKind::IndexAccess(arr, idx) => self.visit_index_access(*arr, *idx, node),
            NodeKind::Cast(ty, expr) | NodeKind::BuiltinVaArg(ty, expr) => {
                self.visit_cast_or_va_arg(node, kind, *ty, *expr)
            }
            NodeKind::SizeOfExpr(_) | NodeKind::SizeOfType(_) | NodeKind::AlignOfExpr(_) | NodeKind::AlignOfType(_) => {
                let (expr, ty, is_alignof) = match kind {
                    NodeKind::SizeOfExpr(e) => (Some(*e), None, false),
                    NodeKind::SizeOfType(t) => (None, Some(*t), false),
                    NodeKind::AlignOfExpr(e) => (Some(*e), None, true),
                    NodeKind::AlignOfType(t) => (None, Some(*t), true),
                    _ => unreachable!(),
                };
                self.visit_sizeof_alignof(expr, ty, is_alignof, node)
            }
            NodeKind::CompoundLiteral(qt, init) => self.visit_compound_literal(node, *qt, *init),
            NodeKind::GenericSelection(gs) => self.visit_generic_selection(gs, node),
            NodeKind::GenericAssociation(ga) => {
                if let Some(ty) = ga.ty {
                    self.visit_type_exprs(ty);
                }
                self.visit_node(ga.result_expr)
            }
            NodeKind::InitializerList(list) => {
                for item in list.init_start.range(list.init_len) {
                    self.visit_node(item);
                }
                None
            }
            NodeKind::InitializerItem(init) => self.visit_initializer_item_node(init),
            NodeKind::BuiltinBitCast(ty, expr) => {
                self.visit_node(*expr);
                Some(*ty)
            }
            NodeKind::BuiltinConvertVector(expr, ty) => {
                self.visit_node(*expr);
                Some(*ty)
            }
            NodeKind::BuiltinComplex(real, imag) => self.visit_builtin_complex_expr(*real, *imag),
            NodeKind::BuiltinOffsetof(ty, expr) => self.visit_builtin_offsetof(*ty, *expr, node),
            NodeKind::BuiltinTypesCompatibleP(t1, t2) => {
                self.visit_type_exprs(*t1);
                self.visit_type_exprs(*t2);
                Some(QualType::unqualified(self.registry.type_int))
            }
            NodeKind::BuiltinChooseExpr(cond, true_expr, false_expr) => {
                self.visit_builtin_choose_expr(*cond, *true_expr, *false_expr, node)
            }
            NodeKind::LabelAddr(_, _) => Some(QualType::unqualified(self.registry.type_void_ptr)),
            _ => None,
        }
    }

    fn visit_builtin_choose_expr(
        &mut self,
        cond: NodeRef,
        true_expr: NodeRef,
        false_expr: NodeRef,
        node: NodeRef,
    ) -> Option<QualType> {
        self.visit_node(cond);

        let const_ctx = self.const_ctx();
        let cond_val = const_ctx.eval_int(cond);

        if cond_val.is_none() {
            self.report_error(cond, SemanticError::BuiltinChooseExprNotConstant);
        }

        let selected = if cond_val.is_some_and(|v| v != 0) {
            true_expr
        } else {
            false_expr
        };

        self.semantic_info.choose_expressions.insert(node.index(), selected);

        // GCC behavior: only the selected branch is semantically analyzed
        let res = self.visit_node(selected);

        // Bolt ⚡: Propagate value category from the selected expression.
        self.semantic_info.value_categories[node.index()] = self.semantic_info.value_categories[selected.index()];

        res
    }

    fn prepare_ternary_operand(&mut self, node: NodeRef, qt: QualType) -> QualType {
        self.apply_lvalue_conversion(node);
        let mut qt = qt;
        if qt.is_array() || qt.is_function() {
            let decayed = self.decay(node, qt);
            qt = decayed;
        } else if !qt.qualifiers().is_empty() {
            self.push_conversion(
                node,
                Conversion::QualifierAdjust {
                    from: qt.qualifiers(),
                    to: TypeQualifiers::empty(),
                },
            );
            qt = qt.strip_all();
        }

        if qt.is_integer() {
            qt = self.apply_integer_promotion(node, qt);
        }
        qt
    }

    fn common_pointer_type(&mut self, t: QualType, e: QualType) -> Option<QualType> {
        let p_t = self.registry.get_pointee(t.ty())?;
        let p_e = self.registry.get_pointee(e.ty())?;

        if p_t.is_void() || p_e.is_void() {
            let res_quals = p_t.qualifiers() | p_e.qualifiers();
            let void_ptr = self
                .registry
                .pointer_to(QualType::new(self.registry.type_void, res_quals));
            Some(QualType::unqualified(void_ptr))
        } else if self.registry.is_compatible(p_t.strip_all(), p_e.strip_all()) {
            let res_p_quals = p_t.qualifiers() | p_e.qualifiers();
            let p_composite = self.registry.composite_type(p_t.strip_all(), p_e.strip_all())?;
            let res_p_ty = QualType::new(p_composite.ty(), res_p_quals);
            Some(QualType::unqualified(self.registry.pointer_to(res_p_ty)))
        } else {
            None
        }
    }

    fn visit_ternary_op(&mut self, cond: NodeRef, then: NodeRef, else_expr: NodeRef) -> Option<QualType> {
        let cond_qt = self.visit_node(cond)?;
        self.apply_lvalue_conversion(cond);
        self.require_scalar(cond, cond_qt);
        let then_ty = self.visit_node(then);
        let else_ty = self.visit_node(else_expr);

        let (mut t, mut e) = (then_ty?, else_ty?);

        t = self.prepare_ternary_operand(then, t);
        e = self.prepare_ternary_operand(else_expr, e);

        let then_is_npc = self.is_null_pointer_constant(then);
        let else_is_npc = self.is_null_pointer_constant(else_expr);

        let result_ty = match (t, e) {
            (t, e) if t.is_arithmetic() && e.is_arithmetic() => usual_arithmetic_conversions(self.registry, t, e),
            (t, e) if t.ty() == e.ty() => self.registry.composite_type(t, e),
            (t, _) if t.is_void() => Some(t),
            (_, e) if e.is_void() => Some(e),
            (t, _) if t.is_pointer() && else_is_npc => Some(t),
            (_, e) if e.is_pointer() && then_is_npc => Some(e),
            (t, e) if t.is_pointer() && e.is_pointer() => self.common_pointer_type(t, e),
            _ => usual_arithmetic_conversions(self.registry, t, e),
        };

        if let Some(res) = result_ty {
            if !res.is_void() {
                self.record_implicit_conversions(res, t, then, then_is_npc);
                self.record_implicit_conversions(res, e, else_expr, else_is_npc);
            }
            return Some(res);
        }

        self.report_error(cond, SemanticError::TypeMismatch { expected: t, found: e });
        None
    }

    fn visit_sizeof_alignof(
        &mut self,
        expr: Option<NodeRef>,
        qt: Option<QualType>,
        is_alignof: bool,
        node: NodeRef,
    ) -> Option<QualType> {
        let ty = if let Some(qt) = qt {
            self.visit_type_exprs(qt);
            qt.ty()
        } else if let Some(e) = expr {
            self.visit_node(e)?.ty()
        } else {
            return Some(QualType::unqualified(self.registry.type_long_unsigned));
        };

        if is_alignof && expr.is_some() && self.lang_opts.is_pedantic() {
            self.report_warning(node, SemanticError::AlignOfExpression);
        }

        if ty.is_function() {
            let err = if is_alignof {
                SemanticError::AlignOfFunctionType
            } else {
                SemanticError::SizeOfFunctionType
            };
            self.report_error(node, err);
        } else if !self.registry.is_complete(ty) {
            let err = if is_alignof {
                SemanticError::AlignOfIncompleteType { ty }
            } else {
                SemanticError::SizeOfIncompleteType { ty }
            };
            self.report_error(node, err);
        } else if let Some(e) = expr
            && self.get_bitfield_width(e).is_some()
            && self.is_lvalue(e)
        {
            let err = if is_alignof {
                SemanticError::AlignOfBitfield
            } else {
                SemanticError::SizeOfBitfield
            };
            self.report_error(node, err);
        } else if !self.registry.is_variably_modified(ty)
            && let Err(e) = self.registry.ensure_layout(ty)
        {
            self.report_error(node, e.to_semantic_kind());
        }

        Some(QualType::unqualified(self.registry.type_long_unsigned))
    }

    fn visit_literal(&mut self, lid: LitRef, node: NodeRef) -> Option<QualType> {
        let val = lid.get_val();
        match val {
            LitVal::Int { value, suffix, radix } => {
                let is_decimal = radix == 10;
                for ty in suffix.get_candidates(self.registry, is_decimal) {
                    let _ = self.registry.ensure_layout(ty);
                    if self.registry.is_literal_fitting(value, ty) {
                        return Some(QualType::unqualified(ty));
                    }
                }

                // If no type fits, use the widest unsigned type as fallback (C11 allows implementation-defined behavior here,
                // but usually it's the widest supported type)
                Some(QualType::unqualified(self.registry.type_long_long_unsigned))
            }
            LitVal::Float { suffix, .. } => {
                let ty = suffix.get_type(self.registry);
                Some(QualType::unqualified(ty))
            }
            LitVal::Char(_, prefix) => {
                let ty = prefix.get_type(self.registry);
                Some(QualType::unqualified(ty))
            }
            LitVal::String { value, prefix } => {
                // Bolt ⚡: Use metadata-only accessors to avoid full literal lowering.
                let builtin_type = get_string_builtin_type(prefix);
                let size = get_string_literal_size(&value, prefix);
                let element_type = self.registry.get_builtin_type(builtin_type);

                let array_type = self.registry.array_of(element_type, ArraySizeType::Constant(size));
                let _ = self.registry.ensure_layout(array_type);

                // Bolt ⚡: Eagerly set value category to LValue for string literals.
                self.semantic_info.value_categories[node.index()] = ValueCategory::LValue;

                Some(QualType::new(array_type, TypeQualifiers::empty()))
            }
            LitVal::Nullptr => Some(QualType::unqualified(self.registry.type_nullptr_t)),
            LitVal::True | LitVal::False => Some(QualType::unqualified(self.registry.type_bool)),
        }
    }
    fn visit_node(&mut self, node: NodeRef) -> Option<QualType> {
        // Bolt ⚡: Memoization - skip analysis if node was already visited.
        // This avoids O(N^2) complexity in constructs like StatementExpr and GenericSelection.
        if let Some(qt) = self.semantic_info.types[node.index()] {
            return Some(qt);
        }

        let node_kind = self.ast.get_kind(node);

        let result_type = match node_kind {
            // Declarations
            NodeKind::TranslationUnit(_)
            | NodeKind::FunctionDef(_)
            | NodeKind::VarDecl(_)
            | NodeKind::RecordDecl(_)
            | NodeKind::FieldDecl(_)
            | NodeKind::EnumDecl(_)
            | NodeKind::EnumMember(_)
            | NodeKind::TypedefDecl(_)
            | NodeKind::Param(_)
            | NodeKind::FunctionDecl(_) => self.visit_declaration_node(node, node_kind),

            // Statements
            NodeKind::CompoundStmt(_)
            | NodeKind::DeclList(_)
            | NodeKind::If(_)
            | NodeKind::While(_)
            | NodeKind::DoWhile(..)
            | NodeKind::For(_)
            | NodeKind::Return(_)
            | NodeKind::ExpressionStmt(_)
            | NodeKind::AsmStmt(_)
            | NodeKind::StaticAssert(..)
            | NodeKind::Switch(..)
            | NodeKind::Case(..)
            | NodeKind::CaseRange(..)
            | NodeKind::Default(_)
            | NodeKind::Break
            | NodeKind::Continue
            | NodeKind::Goto(..)
            | NodeKind::Label(..) => self.visit_statement_node(node, node_kind),

            // Expressions (Catch-all)
            _ => self.visit_expression_node(node, node_kind),
        };

        if let Some(ty) = result_type {
            // set resolved type for this node
            self.semantic_info.types[node.index()] = Some(ty);
        }
        result_type
    }

    fn process_deferred_checks(&mut self) {
        if self.deferred_checks.is_empty() {
            return;
        }

        // Bolt ⚡: Use std::mem::take and iterate to avoid heap allocation and copy from collect()
        let checks = std::mem::take(&mut self.deferred_checks);
        for check in checks {
            match check {
                DeferredCheck::StaticAssert(node) => self.visit_static_assert(node),
            }
        }
    }

    fn visit_static_assert(&mut self, node: NodeRef) {
        let NodeKind::StaticAssert(cond, msg) = *self.ast.get_kind(node) else {
            return;
        };

        if let Some(cond_ty) = self.visit_node(cond)
            && !cond_ty.is_integer()
        {
            self.report_error(cond, SemanticError::ExpectedIntegerType { found: cond_ty });
        }

        match self.const_ctx().eval_int(cond) {
            Some(0) => {
                let message = msg.and_then(|m| self.ast.try_string_literal(m)).unwrap_or_default();

                self.report_error(node, SemanticError::StaticAssertFailed { message });
            }
            None => self.report_error(node, SemanticError::StaticAssertNotConstant),
            _ => {}
        }
    }

    fn visit_generic_selection(&mut self, gs: &GenericSelection, node: NodeRef) -> Option<QualType> {
        // First, visit the controlling expression to determine its type.
        let ctrl = self.visit_node(gs.control)?;

        // Before comparison, array and function types decay to pointers.
        let decayed_ctrl = if ctrl.is_array() || ctrl.is_function() {
            self.decay(gs.control, ctrl)
        } else {
            ctrl
        };

        // After decay, top-level qualifiers are removed for the compatibility check.
        let unqualified_ctrl = decayed_ctrl.strip_all();

        // The completeness check applies to the DECAYED type.
        if !decayed_ctrl.is_void() && !self.registry.is_complete(decayed_ctrl.ty()) {
            self.report_error(gs.control, SemanticError::GenericIncompleteControl { ty: ctrl });
        }

        let mut selected_expr = None;
        let mut selected_span = None;
        let mut default_expr = None;
        let mut default_first_span = None;
        let mut seen_types: SmallVec<[(QualType, SourceSpan); 8]> = SmallVec::new();

        for assoc_node in gs.assoc_start.range(gs.assoc_len) {
            let span = self.ast.get_span(assoc_node);
            self.visit_node(assoc_node);

            let NodeKind::GenericAssociation(ga) = *self.ast.get_kind(assoc_node) else {
                continue;
            };

            let Some(assoc_qt) = ga.ty else {
                // Constraint 2: If a generic selection has a default association, there shall be only one such association.
                if let Some(first_span) = default_first_span {
                    self.report_error(
                        assoc_node,
                        SemanticError::GenericMultipleDefault { first_def: first_span },
                    );
                } else {
                    default_first_span = Some(span);
                    default_expr = Some(ga.result_expr);
                }
                continue;
            };

            // C11 6.5.1.1p2: The type name in a generic association shall specify a complete object type other than a VLA.
            if assoc_qt.is_function() {
                self.report_error(assoc_node, SemanticError::GenericFunctionAssociation { ty: assoc_qt });
            } else if !self.registry.is_complete(assoc_qt.ty()) {
                self.report_error(assoc_node, SemanticError::GenericIncompleteAssociation { ty: assoc_qt });
            } else if self.registry.is_variably_modified(assoc_qt.ty()) {
                self.report_error(assoc_node, SemanticError::GenericVlaAssociation { ty: assoc_qt });
            }

            // Constraint 2: No two generic associations in the same generic selection shall specify compatible types.
            if let Some(&(prev_ty, prev_span)) = seen_types
                .iter()
                .find(|(prev_ty, _)| self.registry.is_compatible(assoc_qt, *prev_ty))
            {
                self.report_error(
                    assoc_node,
                    SemanticError::GenericDuplicateMatch {
                        ty: assoc_qt,
                        prev_ty,
                        first_def: prev_span,
                    },
                );
            } else {
                seen_types.push((assoc_qt, span));
            }

            // Constraint 1: The controlling expression shall have type compatible with at most one association type.
            if self.registry.is_compatible(unqualified_ctrl, assoc_qt) {
                if let Some(first_match) = selected_span {
                    self.report_error(assoc_node, SemanticError::GenericMultipleMatches { first_match });
                } else {
                    selected_expr = Some(ga.result_expr);
                    selected_span = Some(span);
                    self.semantic_info
                        .generic_selections
                        .insert(node.index(), ga.result_expr);
                }
            }
        }

        // If no specific type matches, use the default association if it exists.
        let selected = selected_expr.or(default_expr);
        if let Some(expr) = selected {
            if selected_expr.is_none() {
                self.semantic_info.generic_selections.insert(node.index(), expr);
            }

            // Bolt ⚡: Propagate value category from the selected expression.
            self.semantic_info.value_categories[node.index()] = self.semantic_info.value_categories[expr.index()];

            self.semantic_info.types.get(expr.index()).and_then(|t| *t)
        } else {
            self.report_error(node, SemanticError::GenericNoMatch { ty: ctrl });
            None
        }
    }

    fn visit_builtin_offsetof(&mut self, qt: QualType, expr: NodeRef, node: NodeRef) -> Option<QualType> {
        self.visit_type_exprs(qt);

        let mut current_ty = qt;
        let mut offset = 0i64;
        let res_ty = QualType::unqualified(self.registry.type_long_unsigned);

        if !self.registry.is_complete(qt.ty()) {
            self.report_error(node, SemanticError::OffsetofIncompleteType { ty: qt });
            return Some(res_ty);
        }

        if !self.compute_offsetof(expr, &mut current_ty, &mut offset) {
            return Some(res_ty);
        }

        self.semantic_info.offsetof_results.insert(node.index(), offset);
        Some(res_ty)
    }

    fn compute_offsetof(&mut self, node: NodeRef, current_ty: &mut QualType, offset: &mut i64) -> bool {
        match *self.ast.get_kind(node) {
            NodeKind::Dummy => true,
            NodeKind::MemberAccess(base, member_name, _) => {
                self.compute_offsetof(base, current_ty, offset)
                    && self.apply_offsetof_member(node, member_name, current_ty, offset)
            }
            NodeKind::IndexAccess(base, index) => {
                self.compute_offsetof(base, current_ty, offset)
                    && self.apply_offsetof_index(node, index, current_ty, offset)
            }
            _ => {
                self.report_error(node, SemanticError::InvalidOffsetofDesignator);
                false
            }
        }
    }

    fn apply_offsetof_member(
        &mut self,
        node: NodeRef,
        member_name: NameId,
        current_qt: &mut QualType,
        offset: &mut i64,
    ) -> bool {
        let record_ty = current_qt.ty();

        if !record_ty.is_record() {
            self.report_error(
                node,
                SemanticError::MemberAccessOnNonRecord {
                    ty: QualType::unqualified(record_ty),
                },
            );
            return false;
        }

        let mut base_index = 0;
        let Some((member, field, _)) =
            self.registry
                .get(record_ty)
                .find_member_with_offset(self.registry, member_name, 0, &mut base_index)
        else {
            self.report_error(
                node,
                SemanticError::MemberNotFound {
                    name: member_name,
                    ty: QualType::unqualified(record_ty),
                },
            );
            return false;
        };

        if member.bit_field_size.is_some() {
            self.report_error(node, SemanticError::OffsetofBitfield);
            return false;
        }

        *offset += field.offset as i64;
        *current_qt = member.member_type;
        true
    }

    fn apply_offsetof_index(
        &mut self,
        node: NodeRef,
        index: NodeRef,
        current_qt: &mut QualType,
        offset: &mut i64,
    ) -> bool {
        let Some(elem_ty) = self.registry.get_array_element(current_qt.ty()) else {
            self.report_error(node, SemanticError::ExpectedArrayType { found: *current_qt });
            return false;
        };

        self.visit_node(index);
        let Some(index_val) = self.const_ctx().eval_int(index) else {
            // C11 7.19p3: "integer constant expression"
            self.report_error(index, SemanticError::NonConstantInitializer);
            return false;
        };

        let _ = self.registry.ensure_layout(elem_ty);
        let layout = self.registry.get_layout(elem_ty);
        *offset += index_val * (layout.size as i64);
        *current_qt = QualType::unqualified(elem_ty);
        true
    }

    fn visit_statement_expr(&mut self, stmt: NodeRef, result_expr: NodeRef) -> Option<QualType> {
        self.visit_node(stmt);

        if let NodeKind::Dummy = self.ast.get_kind(result_expr) {
            Some(QualType::unqualified(self.registry.type_void))
        } else {
            self.apply_lvalue_conversion(result_expr);
            let mut ty = self.visit_node(result_expr);
            if let Some(t) = ty
                && (t.is_array() || t.is_function())
            {
                let decayed = self.decay(result_expr, t);
                ty = Some(decayed);
            }
            ty
        }
    }

    fn visit_post_inc_dec(&mut self, node: NodeRef, expr: NodeRef) -> Option<QualType> {
        let ty = self.visit_node(expr);
        if let Some(t) = ty {
            self.check_lvalue_and_modifiable(expr, t);
            if self.check_increment_decrement_operand(node, t) {
                Some(t)
            } else {
                None
            }
        } else {
            None
        }
    }

    fn visit_cast_or_va_arg(
        &mut self,
        node: NodeRef,
        kind: &NodeKind,
        ty: QualType,
        expr: NodeRef,
    ) -> Option<QualType> {
        self.visit_type_exprs(ty);
        let expr_qt = self.visit_node(expr);
        self.apply_lvalue_conversion(expr);

        if let NodeKind::Cast(..) = kind
            && !ty.is_void()
        {
            let scalar_target = ty.is_scalar();
            let mut scalar_operand = true;

            let mut eqt_decayed = None;
            if let Some(mut eqt) = expr_qt {
                if eqt.is_array() || eqt.is_function() {
                    eqt = self.decay(expr, eqt);
                }
                eqt_decayed = Some(eqt);
                if !eqt.is_scalar() {
                    scalar_operand = false;
                }
            }

            // C11 6.5.4p2: "Unless the type name specifies a void type, then both the named type
            // and the expression shall have scalar types."
            // However, as an extension, some compilers allow casting a struct to itself (identity cast).
            // We strictly follow C11 here unless it's an identity cast of compatible types.
            let is_identity_cast = if let Some(eqt) = eqt_decayed {
                self.registry.is_compatible(ty, eqt)
            } else {
                false
            };

            let is_union_cast = if let TypeKind::Record {
                members,
                is_union: true,
                ..
            } = &self.registry.get(ty.ty()).kind
            {
                if let Some(eqt) = eqt_decayed {
                    members.iter().any(|m| {
                        self.registry.is_compatible(
                            QualType::unqualified(m.member_type.ty()),
                            QualType::unqualified(eqt.ty()),
                        )
                    })
                } else {
                    false
                }
            } else {
                false
            };

            if !is_identity_cast && !is_union_cast {
                if !scalar_target {
                    self.report_error(node, SemanticError::ExpectedScalarType { found: ty });
                }
                if !scalar_operand && let Some(eqt) = eqt_decayed {
                    self.report_error(expr, SemanticError::ExpectedScalarType { found: eqt });
                }
            }
        }

        Some(ty.strip_all())
    }

    fn visit_compound_literal(&mut self, node: NodeRef, qt: QualType, init: NodeRef) -> Option<QualType> {
        self.visit_type_exprs(qt);

        // C11 6.5.2.5p1: The type name shall specify a complete object type
        // or an array of unknown size, but not a variably modified type.
        let resolved = self.registry.get(qt.ty());
        if let TypeKind::Function { .. } = &resolved.kind {
            self.report_error(node, SemanticError::CompoundLiteralFunction { ty: qt });
        } else if self.registry.is_vla_type(qt.ty()) {
            self.report_error(node, SemanticError::CompoundLiteralVla { ty: qt });
        } else if !self.registry.is_complete(qt.ty()) {
            // Exception: array of unknown size is allowed.
            let is_incomplete_array = matches!(
                resolved.kind,
                TypeKind::Array {
                    size: ArraySizeType::Incomplete,
                    ..
                }
            );
            if !is_incomplete_array {
                self.report_error(node, SemanticError::CompoundLiteralIncomplete { ty: qt });
            }
        }

        let _ = self.registry.ensure_layout(qt.ty());
        self.visit_init(init, qt);

        // Bolt ⚡: Eagerly set value category to LValue for compound literals.
        self.semantic_info.value_categories[node.index()] = ValueCategory::LValue;

        Some(qt)
    }

    fn check_array_designator(&mut self, expr: NodeRef) {
        let ty = self.visit_node(expr);
        let val = self.const_ctx().eval_int(expr);
        if val.is_none() || ty.is_none_or(|t| !t.is_integer()) {
            self.report_error(expr, SemanticError::NonConstantDesignator);
        }
    }

    fn visit_initializer_item_node(&mut self, init: &DesignatedInitializer) -> Option<QualType> {
        for designator in init.designator_start.range(init.designator_len) {
            if let NodeKind::Designator(d) = self.ast.get_kind(designator) {
                match d {
                    Designator::ArrayIndex(expr) => {
                        self.check_array_designator(*expr);
                    }
                    Designator::ArrayRange(start, end) => {
                        self.check_array_designator(*start);
                        self.check_array_designator(*end);
                    }
                    Designator::FieldName(_) => {}
                }
            }
        }
        self.visit_node(init.initializer);
        None
    }

    fn visit_builtin_complex_expr(&mut self, real: NodeRef, imag: NodeRef) -> Option<QualType> {
        let real_ty = self.visit_node(real)?;
        let imag_ty = self.visit_node(imag)?;
        self.apply_lvalue_conversion(real);
        self.apply_lvalue_conversion(imag);

        if !real_ty.is_real() {
            self.report_error(real, SemanticError::InvalidUnaryOperand { ty: real_ty });
            return None;
        }
        if !imag_ty.is_real() {
            self.report_error(imag, SemanticError::InvalidUnaryOperand { ty: imag_ty });
            return None;
        }

        let common_real = usual_arithmetic_conversions(self.registry, real_ty, imag_ty)?;
        Some(QualType::unqualified(self.registry.complex_type(common_real.ty())))
    }
}
