//! SemanticLowering
//!
//! Responsibility
//! -> VarDecl/RecordDecl/EnumDecl/TypedefDecl, FunctionDef -> Function)
//! - Scope Construction
//! - Symbol Insertion to Symbol Table
//! - Name lookup
//! - Making Sure Struct with body is is_complete = true
//!
//! This module implements the semantic lowering phase that bridges the gap between the
//! grammar-oriented parser AST and the type-resolved semantic AST (HIR). The lowering
//! phase handles all C-style declaration forms

use hashbrown::HashMap;
use smallvec::{SmallVec, smallvec};

use crate::ast::literal::{LitKind, LitRef, LitVal, StrPrefix};
use crate::ast::parsed::{ParsedDecl, ParsedFunctionDef, ParsedNodeKind, ParsedNodeRef, TypeSpec};
use crate::ast::*;
use crate::diagnostic::{DiagnosticEngine, DiagnosticLevel};
use crate::lang_options::CStandard;
use crate::semantic::const_eval::ConstEvalCtx;
use crate::semantic::errors::{SemanticDiag, SemanticError};
use crate::semantic::literal_utils::{get_string_builtin_type, get_string_literal_size};
use crate::semantic::symbol_table::{DefinitionState, SymbolTableError};
use crate::semantic::{
    ArraySizeType, BuiltinFunctionKind, BuiltinType, EnumConstant, Namespace, RecordMember, ScopeId, SymbolKind,
    SymbolRef, SymbolTable, TypeKind, TypeQualifiers, TypeRef, TypeRegistry, Variable,
};
use crate::semantic::{FunctionParam, QualType};
use crate::source_manager::SourceSpan;
use std::sync::Arc;

/// Context for the semantic lowering phase
pub(crate) struct LowerCtx<'a, 'src> {
    pub(crate) parsed_ast: &'a ParsedAst,
    pub(crate) ast: &'a mut Ast,
    pub(crate) diag: &'src mut DiagnosticEngine,
    pub(crate) symbol_table: &'a mut SymbolTable,
    pub(crate) registry: &'a mut TypeRegistry,
    /// If Some, the next CompoundStatement lowering will use this scope instead of pushing a new one.
    /// This is used for function bodies to share the parameter scope.
    pub(crate) next_compound_uses_scope: Option<ScopeId>,
    pub(crate) pragma_pack_stack: Vec<Option<u8>>,
    pub(crate) current_packing: Option<u8>,
    pub(crate) in_prototype: bool,
    pub(crate) lang_opts: &'a crate::lang_options::LangOptions,
    pub(crate) anon_counter: u32,
    pub(crate) type_to_tag_sym: HashMap<TypeRef, SymbolRef>,
    pub(crate) keywords: LoweringKeywords,
}

pub(crate) struct LoweringKeywords {
    builtins: HashMap<NameId, BuiltinFunctionKind>,
}

impl LoweringKeywords {
    fn new() -> Self {
        let mut builtins = HashMap::with_capacity(BuiltinFunctionKind::ALL_VARIANTS.len());
        for &kind in BuiltinFunctionKind::ALL_VARIANTS {
            builtins.insert(NameId::new(kind.name()), kind);
        }
        LoweringKeywords { builtins }
    }

    pub(crate) fn identify(&self, name: NameId) -> Option<BuiltinFunctionKind> {
        self.builtins.get(&name).copied()
    }
}

#[derive(Clone, Copy)]
struct DeclaratorContext {
    in_parameter: bool,
}

impl<'a, 'src> LowerCtx<'a, 'src> {
    /// Create a new lowering context
    fn new(
        parsed_ast: &'a ParsedAst,
        ast: &'a mut Ast,
        diag: &'src mut DiagnosticEngine,
        symbol_table: &'a mut SymbolTable,
        registry: &'a mut TypeRegistry,
        lang_opts: &'a crate::lang_options::LangOptions,
    ) -> Self {
        Self {
            parsed_ast,
            ast,
            diag,
            symbol_table,
            registry,
            next_compound_uses_scope: None,
            pragma_pack_stack: Vec::new(),
            current_packing: None,
            in_prototype: false,
            lang_opts,
            anon_counter: 0,
            type_to_tag_sym: HashMap::new(),
            keywords: LoweringKeywords::new(),
        }
    }

    fn gen_anon_name(&mut self) -> NameId {
        let name = format!("$anon{}", self.anon_counter);
        self.anon_counter += 1;
        NameId::new(&name)
    }

    /// Report a semantic error and mark context as having errors
    /// Report a semantic error
    pub(crate) fn report_error(&mut self, span: SourceSpan, kind: SemanticError) {
        let error = SemanticDiag::new(span, kind);
        for diag in error.into_diagnostic(self.registry) {
            self.diag.report_diagnostic(diag);
        }
    }

    pub(crate) fn report_warning(&mut self, span: SourceSpan, kind: SemanticError) {
        if kind.is_pedantic() && self.lang_opts.pedantic_errors {
            self.report_error(span, kind);
        } else {
            let mut error = SemanticDiag::new(span, kind);
            error.level = Some(DiagnosticLevel::Warning);
            for diag in error.into_diagnostic(self.registry) {
                self.diag.report_diagnostic(diag);
            }
        }
    }

    fn check_function_specs(&mut self, info: &DeclSpecInfo, span: SourceSpan) {
        if info.is_inline {
            self.report_error(span, SemanticError::InvalidFunctionSpec { spec: "inline" });
        }
        if info.is_noreturn {
            self.report_error(span, SemanticError::InvalidFunctionSpec { spec: "_Noreturn" });
        }
    }

    fn merge_qualifiers_with_check(&mut self, base: QualType, add: TypeQualifiers, span: SourceSpan) -> QualType {
        if add.contains(TypeQualifiers::RESTRICT) {
            let is_valid = if let TypeKind::Pointer { pointee } = &self.registry.get(base.ty()).kind {
                !pointee.is_function()
            } else {
                false
            };

            if !is_valid {
                self.report_error(span, SemanticError::InvalidRestrict);
            }
        }
        if add.contains(TypeQualifiers::ATOMIC) {
            if base.is_array() {
                self.report_error(span, SemanticError::InvalidAtomicQualifier { type_kind: "array" });
            } else if base.is_function() {
                self.report_error(span, SemanticError::InvalidAtomicQualifier { type_kind: "function" });
            } else if base.is_void() {
                self.report_error(span, SemanticError::InvalidAtomicQualifier { type_kind: "void" });
            }
        }
        base.merge_qualifiers(add)
    }

    fn check_static_assert(&mut self, cond: ParsedNodeRef, msg: Option<ParsedNodeRef>, span: SourceSpan) {
        let cond_node = self.visit_expression(cond);
        let msg_node = msg.map(|m| self.visit_expression(m));

        if let Some(cond_ty) = self.ast.get_resolved_type(cond_node)
            && !cond_ty.is_integer()
        {
            // The condition of _Static_assert must be an integer constant expression.
            self.report_error(span, SemanticError::ExpectedIntegerType { found: cond_ty });
        }

        let const_ctx = self.const_ctx();
        match const_ctx.eval_int(cond_node) {
            Some(0) => {
                let message = msg_node
                    .and_then(|m| match self.ast.get_kind(m) {
                        NodeKind::Literal(literal_id) => {
                            if let LitVal::String { value: s, .. } = literal_id.get_val() {
                                Some(s.as_str().to_string())
                            } else {
                                None
                            }
                        }
                        _ => None,
                    })
                    .unwrap_or_default();

                self.report_error(span, SemanticError::StaticAssertFailed { message });
            }
            None => self.report_error(span, SemanticError::StaticAssertNotConstant),
            _ => {
                // Static assert succeeded (non-zero)
            }
        }
    }

    fn validate_member_layout(
        &mut self,
        member_type: QualType,
        bit_field_size: Option<u16>,
        alignment: Option<u16>,
        name: Option<NameId>,
        span: SourceSpan,
        is_union: bool,
        is_explicitly_packed: bool,
    ) {
        let layout_info = self
            .registry
            .ensure_layout(member_type.ty())
            .ok()
            .map(|l| (l.size, l.alignment));

        if let Some(width) = bit_field_size {
            if !member_type.is_integer() {
                self.report_error(span, SemanticError::InvalidBitfieldType { ty: member_type });
            } else if member_type.qualifiers().contains(TypeQualifiers::ATOMIC) {
                self.report_error(span, SemanticError::BitfieldHasAtomicType);
            } else if let Some((size, _)) = layout_info {
                let type_width = size * 8;
                if (width as u64) > type_width {
                    self.report_error(span, SemanticError::BitfieldWidthExceedsType { width, type_width });
                }
            }
            if width == 0 && name.is_some() {
                self.report_error(span, SemanticError::NamedZeroWidthBitfield);
            }
            return;
        }

        // C11 6.7.2.1p3: If the containing record is a union, we allow struct-with-FMA members.
        if !is_union && self.registry.has_flexible_array_member(member_type.ty()) {
            self.report_error(span, SemanticError::FlexibleArrayMemberInStruct);
        }

        if !is_explicitly_packed
            && let Some(req_align) = alignment
            && let Some((_, natural)) = layout_info
            && req_align < natural
        {
            self.report_error(
                span,
                SemanticError::AlignmentTooLoose {
                    requested: req_align as u64,
                    natural: natural as u64,
                },
            );
        }
    }

    fn resolve_alignment(&mut self, align: &ParsedAlignmentSpec, span: SourceSpan) -> Option<u16> {
        match align {
            ParsedAlignmentSpec::Type(parsed_ty) => {
                let qt = self.visit_type(*parsed_ty, span);
                match self.registry.ensure_layout(qt.ty()) {
                    Ok(layout) => Some(layout.alignment),
                    Err(e) => {
                        self.report_error(span, e.to_semantic_kind());
                        None
                    }
                }
            }
            ParsedAlignmentSpec::Expr(expr) => {
                let lowered_expr = self.visit_expression(*expr);
                let const_ctx = self.const_ctx();
                if let Some(val) = const_ctx.eval_int(lowered_expr) {
                    if val > 0 && (val as u64).is_power_of_two() {
                        if val > 65535 {
                            self.report_error(span, SemanticError::InvalidAlignment { value: val });
                            None
                        } else {
                            Some(val as u16)
                        }
                    } else if val == 0 {
                        None
                    } else {
                        self.report_error(span, SemanticError::InvalidAlignment { value: val });
                        None
                    }
                } else {
                    self.report_error(span, SemanticError::NonConstantAlignment);
                    None
                }
            }
        }
    }

    fn lower_array_declarator(
        &mut self,
        base: DeclaratorRef,
        size: &ParsedArraySize,
        element_qt: QualType,
        span: SourceSpan,
        decl_ctx: DeclaratorContext,
    ) -> QualType {
        // C11 6.7.6.2 Array declarators
        if !self.registry.is_complete(element_qt.ty()) || element_qt.is_function() {
            self.report_error(span, SemanticError::IncompleteType { ty: element_qt });
        }

        if self.registry.has_flexible_array_member(element_qt.ty()) {
            self.report_error(span, SemanticError::FlexibleArrayElementInArray);
        }

        if size.is_star() && !self.in_prototype {
            self.report_error(span, SemanticError::VlaStarOutsidePrototype);
        }

        let has_static = size.is_static();
        let quals = size.qualifiers();

        if (has_static || !quals.is_empty()) && !decl_ctx.in_parameter {
            if has_static {
                self.report_error(span, SemanticError::ArrayStaticOutsideParameter);
            }
            if !quals.is_empty() {
                self.report_error(span, SemanticError::ArrayQualifierOutsideParameter);
            }
        } else if (has_static || !quals.is_empty())
            && !matches!(
                self.parsed_ast.parsed_types.get_decl(base),
                ParsedDeclarator::Identifier(..)
            )
        {
            if has_static {
                self.report_error(span, SemanticError::ArrayStaticNotOutermost);
            }
            if !quals.is_empty() {
                self.report_error(span, SemanticError::ArrayQualifierNotOutermost);
            }
        }

        let array_size = self.convert_parsed_array_size(size);
        let ty = self.registry.array_of(element_qt.ty(), array_size);
        QualType::new(ty, element_qt.qualifiers())
    }

    fn resolve_atomic_specifier(
        &mut self,
        parsed_type: ParsedType,
        span: SourceSpan,
    ) -> Result<QualType, SemanticDiag> {
        let qt = self.lower_type(parsed_type, span, false)?;

        let reason = if qt.is_array() {
            Some("array type")
        } else if qt.is_function() {
            Some("function type")
        } else if qt.is_void() {
            Some("void type")
        } else if qt.qualifiers().contains(TypeQualifiers::ATOMIC) {
            Some("atomic type")
        } else if !qt.qualifiers().is_empty() {
            Some("qualified type")
        } else {
            None
        };

        if let Some(reason) = reason {
            self.report_error(span, SemanticError::InvalidAtomicSpec { reason });
        }

        Ok(qt.merge_qualifiers(TypeQualifiers::ATOMIC))
    }

    fn resolve_record_specifier(
        &mut self,
        is_union: bool,
        tag: Option<NameId>,
        definition: &Option<Vec<ParsedNodeRef>>,
        attributes: &[DeclSpec],
        span: SourceSpan,
    ) -> Result<QualType, SemanticDiag> {
        let is_definition = definition.is_some();
        let ty = self.resolve_record_tag(tag, is_union, is_definition, span)?;

        if let Some(decls) = definition {
            let mut packing = None;
            let mut alignment = None;
            for attr in attributes {
                match attr {
                    DeclSpec::AttributePacked => packing = Some(1),
                    DeclSpec::AlignmentSpec(aspec, _) => {
                        if let Some(val) = self.resolve_alignment(aspec, span) {
                            alignment = Some(std::cmp::max(alignment.unwrap_or(0), val));
                        }
                    }
                    DeclSpec::AttributeCleanup(_) => {
                        self.report_warning(span, SemanticError::AttributeCleanupOnType);
                    }
                    _ => {}
                }
            }
            let members = self.visit_record_members(decls, span, is_union);
            self.complete_record_symbol(tag, ty, members, packing, alignment, span)?;
        }

        Ok(QualType::unqualified(ty))
    }

    fn resolve_enum_specifier(
        &mut self,
        tag: Option<NameId>,
        enumerators: &Option<Vec<ParsedNodeRef>>,
        underlying_type: Option<ParsedType>,
        span: SourceSpan,
    ) -> Result<QualType, SemanticDiag> {
        let underlying_qt = underlying_type
            .map(|ut| {
                let qt = self.lower_type(ut, span, false)?;
                if !qt.is_integer() || qt.is_enum() {
                    self.report_error(span, SemanticError::InvalidEnumUnderlyingType { ty: qt });
                }
                Ok(qt)
            })
            .transpose()?;

        let is_definition = enumerators.is_some() || underlying_qt.is_some();
        let ty = self.resolve_enum_tag(tag, is_definition, underlying_qt.is_some(), span)?;

        if let Some(enums) = enumerators {
            let mut next_value = 0i64;
            let mut enumerators_list = Vec::with_capacity(enums.len());
            let mut constant_syms: Vec<SymbolRef> = Vec::with_capacity(enums.len());

            for &enum_node in enums {
                let node = self.parsed_ast.get_node(enum_node);
                let ParsedNodeKind::EnumConstant(name, value_expr) = &node.kind else {
                    unreachable!()
                };

                let (value, init_expr) = value_expr
                    .map(|v| {
                        let expr = self.visit_expression(v);
                        let val = self.const_ctx().eval_int(expr).unwrap_or_else(|| {
                            self.report_error(node.span, SemanticError::NonConstantInitializer);
                            0i64
                        });
                        (val, Some(expr))
                    })
                    .unwrap_or((next_value, None));

                // C11 6.7.2.2p2: The expression that defines the value of an enumeration
                // constant shall be an integer constant expression.
                // C23 6.7.2.2p4: If there is an underlying type, the value must be representable by it.
                // Otherwise, it must be representable as an int (or wider implementing type).

                let is_representable = if let Some(uqt) = underlying_qt {
                    self.registry.get(uqt.ty()).truncate_int(value) == value
                } else {
                    (i32::MIN as i64..=i32::MAX as i64).contains(&value)
                };

                if !is_representable {
                    let err = SemanticError::EnumeratorValueNotRepresentable {
                        name: *name,
                        value,
                        target_ty: underlying_qt,
                    };
                    self.report_error(node.span, err);
                }

                next_value = value.wrapping_add(1);

                match self.symbol_table.define_enum_constant(*name, value, ty, node.span) {
                    Ok(sym) => {
                        constant_syms.push(sym);
                    }
                    Err(SymbolTableError::InvalidRedefinition { existing, .. }) => {
                        let first_def = self.symbol_table.get_symbol(existing).def_span;
                        self.report_error(node.span, SemanticError::Redefinition { name: *name, first_def });
                        constant_syms.push(existing); // keep a reference so index stays aligned
                    }
                }

                enumerators_list.push(EnumConstant {
                    name: *name,
                    value,
                    span: node.span,
                    init_expr,
                });
            }

            self.complete_enum_symbol(
                tag,
                ty,
                enumerators_list,
                underlying_qt.map(|q| q.ty()),
                underlying_qt.is_some(),
                span,
            )?;

            // After completion, the underlying type is determined.
            // GCC extension: enum constants have the enum's underlying integer type for _Generic matching.
            // Update the type_info of each enum constant symbol to the underlying integer type.
            let resolved_underlying_type = match &self.registry.get(ty).kind {
                TypeKind::Enum { base_type, .. } => *base_type,
                _ => self.registry.type_int,
            };
            let resolved_underlying_type = QualType::unqualified(resolved_underlying_type);
            for sym in constant_syms {
                self.symbol_table.get_symbol_mut(sym).type_info = resolved_underlying_type;
            }
        } else if let Some(uqt) = underlying_qt {
            // C23: definition with underlying type but no enumerators
            self.complete_enum_symbol(tag, ty, Vec::new(), Some(uqt.ty()), true, span)?;
        }
        Ok(QualType::unqualified(ty))
    }

    fn resolve_typedef_name(&mut self, name: NameId, span: SourceSpan) -> Result<QualType, SemanticDiag> {
        match self
            .symbol_table
            .lookup_symbol(name)
            .map(|r| self.symbol_table.get_symbol(r))
        {
            Some(entry) => {
                if let SymbolKind::Typedef { aliased_type } = entry.kind {
                    Ok(aliased_type)
                } else {
                    Err(SemanticDiag::new(
                        span,
                        SemanticError::ExpectedTypedefName { found: name },
                    ))
                }
            }
            None => Ok(QualType::unqualified(self.registry.declare_record(Some(name), false))),
        }
    }

    fn push_dummy(&mut self, span: SourceSpan) -> NodeRef {
        self.ast.push_dummy(span)
    }

    /// Get the first slot from target_slots if available, otherwise push a new dummy node.
    /// Also ensures scope is set on the node.
    fn get_or_push_slot(&mut self, target_slots: Option<&[NodeRef]>, span: SourceSpan) -> NodeRef {
        if let Some(target) = target_slots.and_then(|t| t.first()) {
            self.ast.set_span(*target, span);
            *target
        } else {
            self.push_dummy(span)
        }
    }

    fn count_semantic_nodes(&self, node: ParsedNodeRef) -> usize {
        let node = self.parsed_ast.get_node(node);
        match &node.kind {
            ParsedNodeKind::Declaration(decl) => {
                if decl.init_declarators.is_empty() {
                    1
                } else {
                    decl.init_declarators.len()
                }
            }
            ParsedNodeKind::TranslationUnit(decls) => decls.len(),
            _ => 1,
        }
    }

    fn const_ctx(&self) -> ConstEvalCtx<'_> {
        ConstEvalCtx {
            ast: self.ast,
            symbol_table: self.symbol_table,
            registry: self.registry,
            semantic_info: &self.ast.semantic_info,
        }
    }
}

/// Information about declaration specifiers after processing
#[derive(Debug, Clone, Default)]
pub(crate) struct DeclSpecInfo {
    pub(crate) storage: Option<StorageClass>,
    pub(crate) is_thread_local: bool,
    pub(crate) is_constexpr: bool,
    pub(crate) qualifiers: TypeQualifiers,
    pub(crate) base_type: Option<QualType>,
    pub(crate) is_typedef: bool,
    pub(crate) is_inline: bool,
    pub(crate) is_noreturn: bool,
    pub(crate) alignment: Option<u16>,
    pub(crate) is_gnu_aligned: bool,
    pub(crate) has_c11_alignment: bool,
    pub(crate) has_auto: bool,
    pub(crate) is_packed: bool,
    pub(crate) cleanup_func: Option<ParsedNodeRef>,
}

/// Finalize tentative definitions by converting them to defined state
fn finalize_tentative_definitions(
    symbol_table: &mut SymbolTable,
    registry: &TypeRegistry,
    diag: &mut DiagnosticEngine,
) {
    for entry in &mut symbol_table.entries {
        if entry.scope_id == ScopeId::GLOBAL
            && matches!(entry.kind, SymbolKind::Variable { .. })
            && entry.def_state == DefinitionState::Tentative
            && !registry.is_complete(entry.type_info.ty())
        {
            // Incomplete arrays at file scope are conceptually completed to have one element (C11 6.9.2p3)
            if matches!(
                registry.get(entry.type_info.ty()).kind,
                TypeKind::Array {
                    size: ArraySizeType::Incomplete,
                    ..
                }
            ) {
                continue;
            }

            let kind = if entry.type_info.ty().builtin() == Some(BuiltinType::Void) {
                SemanticError::VariableOfVoidType
            } else {
                SemanticError::IncompleteType { ty: entry.type_info }
            };
            let error = SemanticDiag::new(entry.def_span, kind);
            for d in error.into_diagnostic(registry) {
                diag.report_diagnostic(d);
            }
        }
    }
}

/// Main entry point for semantic lowering on ParsedAst
pub(crate) fn visit_ast(
    parsed_ast: &ParsedAst,
    ast: &mut Ast,
    diag: &mut DiagnosticEngine,
    symbol_table: &mut SymbolTable,
    registry: &mut TypeRegistry,
    lang_opts: &crate::lang_options::LangOptions,
) {
    // Create lowering context
    let mut lower_ctx = LowerCtx::new(parsed_ast, ast, diag, symbol_table, registry, lang_opts);

    // Perform recursive scope-aware lowering starting from root
    let root = parsed_ast.get_root();
    lower_ctx.visit_node(root);

    // Finalize tentative definitions
    finalize_tentative_definitions(lower_ctx.symbol_table, lower_ctx.registry, lower_ctx.diag);
}

impl<'a, 'src> LowerCtx<'a, 'src> {
    fn visit_node(&mut self, node: ParsedNodeRef) -> SmallVec<[NodeRef; 1]> {
        self.visit_node_entry(node, None)
    }

    fn visit_node_entry(&mut self, node: ParsedNodeRef, target_slots: Option<&[NodeRef]>) -> SmallVec<[NodeRef; 1]> {
        let parsed_node = self.parsed_ast.get_node(node);
        let span = parsed_node.span;

        match &parsed_node.kind {
            ParsedNodeKind::TranslationUnit(children) => {
                smallvec![self.visit_translation_unit(children, span)]
            }
            ParsedNodeKind::CompoundStmt(stmts) => {
                smallvec![self.visit_compound_statement(stmts, target_slots, span)]
            }
            ParsedNodeKind::Declaration(decl) => self.visit_declaration(decl, span, target_slots),
            ParsedNodeKind::FunctionDef(func_def) => {
                let res_node = self.get_or_push_slot(target_slots, span);
                self.visit_function_definition(func_def, res_node, span);
                smallvec![res_node]
            }
            ParsedNodeKind::PragmaPack(kind) => {
                self.handle_pragma_pack(*kind);
                smallvec![]
            }
            // ... other top level kinds ...
            _ => self.visit_node_rest(node, target_slots),
        }
    }

    fn handle_pragma_pack(&mut self, kind: PragmaPackKind) {
        match kind {
            PragmaPackKind::Push => self.pragma_pack_stack.push(self.current_packing),
            PragmaPackKind::PushSet(n) => {
                self.pragma_pack_stack.push(self.current_packing);
                self.current_packing = Some(n);
            }
            PragmaPackKind::Pop => {
                if let Some(prev) = self.pragma_pack_stack.pop() {
                    self.current_packing = prev;
                }
            }
            PragmaPackKind::Set(n) => self.current_packing = n,
        }
    }

    fn visit_translation_unit(&mut self, children: &[ParsedNodeRef], span: SourceSpan) -> NodeRef {
        self.symbol_table.set_current_scope(ScopeId::GLOBAL);
        let tu_node = self.push_dummy(span);

        let mut semantic_node_counts = Vec::with_capacity(children.len());
        let mut total_semantic_nodes = 0;

        for &child in children {
            let child = self.parsed_ast.get_node(child);
            let count = match &child.kind {
                ParsedNodeKind::PragmaPack(..) => 0,
                ParsedNodeKind::FunctionDef(..) | ParsedNodeKind::StaticAssert(..) => 1,
                ParsedNodeKind::Declaration(decl) => {
                    if !decl.init_declarators.is_empty() {
                        decl.init_declarators.len()
                    } else if let Some(DeclSpec::TypeSpec(ts)) =
                        decl.specifiers.iter().find(|s| matches!(s, DeclSpec::TypeSpec(..)))
                    {
                        match ts {
                            TypeSpec::Record(.., is_def, _) if is_def.is_some() => 1,
                            TypeSpec::Enum(_, is_def, underlying_type)
                                if is_def.is_some() || underlying_type.is_some() =>
                            {
                                1
                            }
                            _ => 0,
                        }
                    } else {
                        0
                    }
                }
                _ => 0,
            };
            semantic_node_counts.push(count);
            total_semantic_nodes += count;
        }

        let decl_len = total_semantic_nodes as u16;
        let mut reserved_slots = Vec::with_capacity(decl_len as usize);
        for _ in 0..decl_len {
            reserved_slots.push(self.push_dummy(span));
        }

        let mut current_slot_idx = 0;
        for (i, child) in children.iter().enumerate() {
            let count = semantic_node_counts[i];
            if count > 0 {
                let target_slots = &reserved_slots[current_slot_idx..current_slot_idx + count];
                self.visit_top_level_node(*child, target_slots);
                current_slot_idx += count;
            } else {
                self.visit_node_entry(*child, None);
            }
        }

        let decl_start = if decl_len > 0 { reserved_slots[0] } else { NodeRef::ROOT };
        self.ast.set_kind(
            tu_node,
            NodeKind::TranslationUnit(TranslationUnit {
                decl_start,
                decl_len,
                scope_id: ScopeId::GLOBAL,
            }),
        );
        tu_node
    }

    fn visit_compound_statement(
        &mut self,
        stmts: &[ParsedNodeRef],
        target_slots: Option<&[NodeRef]>,
        span: SourceSpan,
    ) -> NodeRef {
        let (scope_id, pushed) = if let Some(sid) = self.next_compound_uses_scope.take() {
            (sid, false)
        } else {
            (self.symbol_table.push_scope(), true)
        };

        let node = self.get_or_push_slot(target_slots, span);

        let mut total_stmt_nodes = 0;
        for &stmt in stmts {
            total_stmt_nodes += self.count_semantic_nodes(stmt);
        }

        let mut stmt_slots = Vec::with_capacity(total_stmt_nodes);
        for _ in 0..total_stmt_nodes {
            stmt_slots.push(self.push_dummy(span));
        }

        let stmt_start = stmt_slots.first().copied().unwrap_or(NodeRef::ROOT);
        let stmt_len = stmt_slots.len() as u16;

        let old_scope = self.symbol_table.current_scope();
        self.symbol_table.set_current_scope(scope_id);

        let mut current_slot_idx = 0;
        for &stmt in stmts {
            let count = self.count_semantic_nodes(stmt);
            if count > 0 {
                let target = &stmt_slots[current_slot_idx..current_slot_idx + count];
                self.visit_node_entry(stmt, Some(target));
                current_slot_idx += count;
            } else {
                self.visit_node_entry(stmt, None);
            }
        }

        if pushed {
            self.symbol_table.pop_scope();
        } else {
            self.symbol_table.set_current_scope(old_scope);
        }

        self.ast.set_kind(
            node,
            NodeKind::CompoundStmt(CompoundStmt {
                stmt_start,
                stmt_len,
                scope_id,
            }),
        );
        node
    }

    fn visit_top_level_node(&mut self, node: ParsedNodeRef, target_slots: &[NodeRef]) {
        let node = self.parsed_ast.get_node(node);
        let span = node.span;

        match &node.kind {
            ParsedNodeKind::Declaration(decl) => {
                self.visit_declaration(decl, span, Some(target_slots));
            }
            ParsedNodeKind::FunctionDef(func_def) => {
                if let Some(target) = target_slots.first() {
                    self.visit_function_definition(func_def, *target, span);
                }
            }
            _ => {
                if let ParsedNodeKind::StaticAssert(expr, msg) = &node.kind
                    && let Some(target) = target_slots.first()
                {
                    let lowered_expr = self.visit_expression(*expr);
                    let lowered_msg = msg.map(|m| self.visit_expression(m));
                    self.ast
                        .set_kind(*target, NodeKind::StaticAssert(lowered_expr, lowered_msg));
                    self.ast.set_span(*target, span);
                }
            }
        }
    }

    fn check_redeclaration_compatibility(
        &mut self,
        name: NameId,
        new_ty: QualType,
        span: SourceSpan,
        storage: Option<StorageClass>,
    ) -> QualType {
        let Some((sym, existing_scope)) = self.symbol_table.lookup_symbol_and_scope(name) else {
            return new_ty;
        };

        let current_scope = self.symbol_table.current_scope();
        let symbol = self.symbol_table.get_symbol(sym);
        let symbol_type_info = symbol.type_info;
        let symbol_def_span = symbol.def_span;
        let symbol_has_linkage = symbol.has_linkage();

        let is_global = current_scope == ScopeId::GLOBAL;
        let is_func = new_ty.is_function();
        let new_has_linkage = is_global || storage == Some(StorageClass::Extern) || is_func;

        // Skip if not in same scope and no linkage conflict
        if existing_scope != current_scope && !(new_has_linkage && symbol_has_linkage) {
            return new_ty;
        }

        // Check for linkage conflict (C11 6.2.2)
        if matches!(&symbol.kind, SymbolKind::Variable(_) | SymbolKind::Function { .. }) {
            let existing_is_static = match &symbol.kind {
                SymbolKind::Variable(v) => v.storage == Some(StorageClass::Static),
                SymbolKind::Function(f) => f.storage == Some(StorageClass::Static),
                _ => false,
            };
            let new_is_static = storage == Some(StorageClass::Static);

            // static followed by extern/plain is OK and inherits internal linkage.
            // extern/plain followed by static is an error.
            if !existing_is_static && new_is_static {
                self.report_error(
                    span,
                    SemanticError::ConflictingLinkage {
                        name,
                        first_def: symbol_def_span,
                    },
                );
            }
        }

        // C11 6.7p3: If an identifier has no linkage, there shall be no more than one declaration
        // in the same scope and name space.
        if existing_scope == current_scope && (!symbol_has_linkage || !new_has_linkage) {
            self.report_error(
                span,
                SemanticError::Redefinition {
                    name,
                    first_def: symbol_def_span,
                },
            );
            return new_ty;
        }

        let Some(composite) = self.registry.composite_type(symbol_type_info, new_ty) else {
            self.report_error(
                span,
                SemanticError::ConflictingTypes {
                    name,
                    first_def: symbol_def_span,
                },
            );
            return new_ty;
        };

        // Update the existing symbol's type with the composite type
        self.symbol_table.get_symbol_mut(sym).type_info = composite;

        if new_ty.is_function() {
            self.check_function_redeclaration(name, new_ty, span, symbol_def_span, symbol_type_info);
        }

        composite
    }

    fn check_function_redeclaration(
        &mut self,
        name: NameId,
        new_ty: QualType,
        span: SourceSpan,
        first_def: SourceSpan,
        existing_ty: QualType,
    ) {
        // Check for _Noreturn mismatch
        let get_noreturn = |qt: QualType, registry: &TypeRegistry| {
            if let TypeKind::Function { is_noreturn, .. } = &registry.get(qt.ty()).kind {
                *is_noreturn
            } else {
                false
            }
        };

        let existing_is_noreturn = get_noreturn(existing_ty, self.registry);
        let new_is_noreturn = get_noreturn(new_ty, self.registry);

        if existing_is_noreturn != new_is_noreturn {
            self.report_error(span, SemanticError::ConflictingTypes { name, first_def });
        }
    }

    fn check_function_constraints(
        &mut self,
        name: NameId,
        spec_info: &DeclSpecInfo,
        span: SourceSpan,
        is_global: bool,
    ) {
        let specifier = match spec_info.storage {
            Some(StorageClass::Auto) => Some("auto"),
            Some(StorageClass::Register) => Some("register"),
            Some(StorageClass::Static) if !is_global => Some("static"),
            _ => None,
        };

        if let Some(specifier) = specifier {
            self.report_error(span, SemanticError::InvalidStorageClassForFunction { name, specifier });
        }

        if spec_info.is_thread_local {
            self.report_error(span, SemanticError::ThreadLocalNotAllowed);
        }

        if spec_info.alignment.is_some() {
            self.report_error(span, SemanticError::AlignmentNotAllowed { context: "function" });
        }
    }

    fn visit_function_definition(&mut self, func_def: &ParsedFunctionDef, node: NodeRef, span: SourceSpan) {
        let mut spec_info = self.visit_decl_specs(&func_def.specifiers, span);
        let mut base_qt = spec_info
            .base_type
            .unwrap_or_else(|| QualType::unqualified(self.registry.type_int));
        base_qt = self.merge_qualifiers_with_check(base_qt, spec_info.qualifiers, span);

        let mut final_qt = self.apply_declarator(
            base_qt,
            func_def.declarator,
            span,
            Some(&mut spec_info),
            DeclaratorContext { in_parameter: false },
        );
        let func_name = self
            .extract_name(func_def.declarator)
            .expect("Function definition must have a name");

        let is_global = self.symbol_table.current_scope() == ScopeId::GLOBAL;

        self.check_function_constraints(func_name, &spec_info, span, is_global);

        final_qt = self.check_redeclaration_compatibility(func_name, final_qt, span, spec_info.storage);

        // Check for _Noreturn on existing declarations
        let existing_symbol_is_noreturn = if let Some(sym) = self.symbol_table.lookup_symbol(func_name) {
            let existing = self.symbol_table.get_symbol(sym);
            if let TypeKind::Function { is_noreturn, .. } = &self.registry.get(existing.type_info.ty()).kind {
                *is_noreturn
            } else {
                false
            }
        } else {
            false
        };

        let final_is_noreturn = spec_info.is_noreturn || existing_symbol_is_noreturn;

        let parameters = self.get_definition_params(func_def.declarator).unwrap_or_default();

        // Get parameters calculated earlier
        let param_len = parameters.len() as u16;

        let func_sym = match self.symbol_table.define_function(
            func_name,
            final_qt.ty(),
            span,
            crate::semantic::symbol_table::Function {
                storage: spec_info.storage,
                is_noreturn: final_is_noreturn,
                param_len,
                builtin_kind: None,
            },
            true,
        ) {
            Ok(sym) => sym,
            Err(SymbolTableError::InvalidRedefinition { existing, .. }) => {
                let entry = self.symbol_table.get_symbol(existing);
                if entry.def_state == DefinitionState::Defined {
                    let first_def = entry.def_span;
                    self.report_error(
                        span,
                        SemanticError::Redefinition {
                            name: func_name,
                            first_def,
                        },
                    );
                }
                existing
            }
        };

        let scope_id = self.symbol_table.push_scope();

        // Implement __func__ (C11 6.4.2.2)
        {
            let func_name_str = func_name.to_string();
            let name_len = func_name_str.len();

            // Create string literal for initializer
            let func_name_id = NameId::new(&func_name_str);
            let init_literal = LitRef::from_string(std::borrow::Cow::Borrowed(func_name_id.as_str()), StrPrefix::None);
            let init_node = self.push_dummy(span);
            self.ast.set_kind(init_node, NodeKind::Literal(init_literal));

            // Create type: const char[N]
            let char_type = self.registry.type_char;
            let array_size = ArraySizeType::Constant(name_len + 1);
            let array_type = self.registry.array_of(char_type, array_size);

            let qt = QualType::new(array_type, TypeQualifiers::CONST);
            let _ = self.registry.ensure_layout(array_type);

            // Define __func__
            let func_id = NameId::new("__func__");
            let storage = Some(StorageClass::Static);

            // We define it in the current scope (function body).
            // Note: If the user declares __func__ explicitly, it will be caught as a redefinition
            // by the standard variable declaration logic because this one is inserted first.
            let _ = self.symbol_table.define_variable(
                func_id,
                qt,
                span,
                Variable {
                    is_global: self.symbol_table.current_scope() == ScopeId::GLOBAL,
                    storage,
                    is_thread_local: false,
                    initializer: Some(init_node),
                    alignment: None,
                    cleanup_func: None,
                },
            );

            // Also define __FUNCTION__ (GCC extension)
            let function_id = NameId::new("__FUNCTION__");
            let _ = self.symbol_table.define_variable(
                function_id,
                qt,
                span,
                Variable {
                    is_global: self.symbol_table.current_scope() == ScopeId::GLOBAL,
                    storage,
                    is_thread_local: false,
                    initializer: Some(init_node),
                    alignment: None,
                    cleanup_func: None,
                },
            );

            // Also define __PRETTY_FUNCTION__ (GCC extension)
            let pretty_func_id = NameId::new("__PRETTY_FUNCTION__");
            let _ = self.symbol_table.define_variable(
                pretty_func_id,
                qt,
                span,
                Variable {
                    is_global: self.symbol_table.current_scope() == ScopeId::GLOBAL,
                    storage,
                    is_thread_local: false,
                    initializer: Some(init_node),
                    alignment: None,
                    cleanup_func: None,
                },
            );
        }

        // Pre-scan labels for forward goto support
        self.collect_labels(func_def.body);

        let parameters = self.get_definition_params(func_def.declarator).unwrap_or_default();
        let param_len = parameters.len() as u16;

        let mut child_dummies = Vec::with_capacity(param_len as usize + 1);
        for _ in 0..=param_len {
            child_dummies.push(self.push_dummy(span));
        }
        let child_start = child_dummies[0];

        // 1. Visit parameters and copy to [0..param_len]
        for (i, param) in parameters.iter().enumerate() {
            let pname = param.name.unwrap_or_else(|| NameId::new("<unnamed>"));
            let sym = match self.symbol_table.fetch_current(pname, Namespace::Ordinary) {
                Some(s) => s,
                None => self
                    .symbol_table
                    .define_variable(
                        pname,
                        param.param_type,
                        span,
                        Variable {
                            is_global: self.symbol_table.current_scope() == ScopeId::GLOBAL,
                            storage: param.storage,
                            is_thread_local: false,
                            initializer: None,
                            alignment: None,
                            cleanup_func: None,
                        },
                    )
                    .expect("Failed to define parameter"),
            };

            let param_dummy = child_dummies[i];
            self.ast.set_kind(
                param_dummy,
                NodeKind::Param(Param {
                    symbol: sym,
                    qt: param.param_type,
                }),
            );
            self.ast.set_span(param_dummy, span);
        }

        // 2. Visit body directly into the last dummy slot
        self.next_compound_uses_scope = Some(scope_id);
        let body_dummy = child_dummies[param_len as usize];
        self.visit_single_statement_into(func_def.body, body_dummy);
        self.next_compound_uses_scope = None;

        self.symbol_table.pop_scope();

        self.ast.set_kind(
            node,
            NodeKind::FunctionDef(FunctionDef {
                symbol: func_sym,
                child_start,
                param_len,
            }),
        );
        self.ast.set_span(node, span);
    }

    fn visit_declaration(
        &mut self,
        decl: &ParsedDecl,
        span: SourceSpan,
        target_slots: Option<&[NodeRef]>,
    ) -> SmallVec<[NodeRef; 1]> {
        let mut spec_info = self.visit_decl_specs(&decl.specifiers, span);
        let mut base_qt = spec_info
            .base_type
            .unwrap_or(QualType::unqualified(self.registry.type_int));
        base_qt = self.merge_qualifiers_with_check(base_qt, spec_info.qualifiers, span);

        if decl.init_declarators.is_empty() {
            return self.visit_tag_definition(&spec_info, span, target_slots);
        }

        let is_auto_type = self.registry.get(base_qt.ty()).kind == TypeKind::AutoType;
        let mut first_deduced_type: Option<QualType> = None;

        let mut nodes = SmallVec::new();
        for (i, init) in decl.init_declarators.iter().enumerate() {
            let target_slot = target_slots.and_then(|slots| slots.get(i)).copied();
            if let Some(node) = self.visit_single_declarator(init, base_qt, &mut spec_info, span, target_slot) {
                nodes.push(node);

                if is_auto_type && let NodeKind::VarDecl(var_decl) = self.ast.get_kind(node) {
                    let qt = self.symbol_table.get_symbol(var_decl.symbol).type_info;
                    let deduced = qt.strip_all();
                    if let Some(first) = first_deduced_type {
                        if !self.registry.is_compatible(first, deduced) {
                            self.report_error(
                                init.span,
                                SemanticError::AutoTypeIncompatibleDeduction { first, new: deduced },
                            );
                        }
                    } else {
                        first_deduced_type = Some(deduced);
                    }
                }
            }
        }
        nodes
    }

    fn visit_tag_definition(
        &mut self,
        spec_info: &DeclSpecInfo,
        span: SourceSpan,
        target_slots: Option<&[NodeRef]>,
    ) -> SmallVec<[NodeRef; 1]> {
        let Some(qt) = spec_info.base_type else {
            return smallvec![];
        };

        // Extract needed data from registry to avoid borrowing self.registry during node creation
        enum AggType {
            Record(Option<NameId>, Arc<[RecordMember]>),
            Enum(Option<NameId>, Arc<[EnumConstant]>),
        }

        let type_info = self.registry.get(qt.ty());
        let type_kind = match &type_info.kind {
            TypeKind::Record { tag, members, .. } => Some(AggType::Record(*tag, members.clone())),
            TypeKind::Enum { tag, enumerators, .. } => Some(AggType::Enum(*tag, enumerators.clone())),
            _ => None,
        };

        if let Some(data) = type_kind {
            let node = self.get_or_push_slot(target_slots, span);
            self.check_function_specs(spec_info, span);

            match data {
                AggType::Record(tag, members) => {
                    let member_start = self.ast.next_node_ref();
                    let member_len = members.len() as u16;

                    for m in members.iter() {
                        self.ast.push_node(
                            NodeKind::FieldDecl(FieldDecl {
                                name: m.name,
                                qt: m.member_type,
                                alignment: m.alignment,
                            }),
                            m.span,
                        );
                    }

                    // Find/create symbol for this record tag
                    let symbol = self
                        .type_to_tag_sym
                        .get(&qt.ty())
                        .copied()
                        .or_else(|| tag.and_then(|t| self.symbol_table.fetch_current(t, Namespace::Tag)))
                        .expect("ICE: Record tag symbol not found during lowering");

                    self.ast.set_kind(
                        node,
                        NodeKind::RecordDecl(RecordDecl {
                            symbol,
                            member_start,
                            member_len,
                        }),
                    );
                }
                AggType::Enum(tag, enumerators) => {
                    let mut member_start = NodeRef::ROOT;
                    let member_len = enumerators.len() as u16;

                    for (i, e) in enumerators.iter().enumerate() {
                        // Find symbol for enum constant
                        let symbol = self
                            .symbol_table
                            .fetch_current(e.name, Namespace::Ordinary)
                            .expect("ICE: Enum constant symbol not found during lowering");

                        let member = self.ast.push_node(
                            NodeKind::EnumMember(EnumMember {
                                symbol,
                                init_expr: e.init_expr,
                            }),
                            e.span,
                        );
                        if i == 0 {
                            member_start = member;
                        }
                    }

                    // Find/create symbol for this enum tag
                    let symbol = self
                        .type_to_tag_sym
                        .get(&qt.ty())
                        .copied()
                        .or_else(|| tag.and_then(|t| self.symbol_table.fetch_current(t, Namespace::Tag)))
                        .expect("ICE: Enum tag symbol not found during lowering");

                    self.ast.set_kind(
                        node,
                        NodeKind::EnumDecl(EnumDecl {
                            symbol,
                            member_start,
                            member_len,
                        }),
                    );
                }
            }
            return smallvec![node];
        }

        smallvec![]
    }

    fn visit_single_declarator(
        &mut self,
        init: &ParsedInitDeclarator,
        base_qt: QualType,
        spec_info: &mut DeclSpecInfo,
        span: SourceSpan,
        target_slot: Option<NodeRef>,
    ) -> Option<NodeRef> {
        if self.registry.get(base_qt.ty()).kind == TypeKind::AutoType {
            let decl = self.parsed_ast.parsed_types.get_decl(init.declarator);
            if !matches!(decl, ParsedDeclarator::Identifier(..)) {
                self.report_error(
                    init.span,
                    SemanticError::AutoTypeNotAllowed {
                        context: "complex declarator",
                    },
                );
            }
        }

        let final_ty = self.apply_declarator(
            base_qt,
            init.declarator,
            init.span,
            Some(spec_info),
            DeclaratorContext { in_parameter: false },
        );

        // Check if declarator has an identifier
        let Some(name) = self.extract_name(init.declarator) else {
            // Declaration without identifier (e.g., "int;") - emit warning and skip
            self.report_error(init.span, SemanticError::EmptyDeclaration);
            return None;
        };

        let node = if let Some(slot) = target_slot {
            self.ast.set_span(slot, span);
            slot
        } else {
            self.push_dummy(span)
        };

        if spec_info.is_typedef {
            if spec_info.cleanup_func.is_some() {
                self.report_warning(span, SemanticError::AttributeCleanupOnType);
            }
            if spec_info.alignment.is_some() {
                self.report_error(init.span, SemanticError::AlignmentNotAllowed { context: "typedef" });
            }

            if let Some(base) = spec_info.base_type
                && self.registry.get(base.ty()).kind == TypeKind::AutoType
            {
                self.report_error(init.span, SemanticError::AutoTypeNotAllowed { context: "typedef" });
            }

            self.check_function_specs(spec_info, init.span);

            let symbol = if let Err(SymbolTableError::InvalidRedefinition { existing, .. }) =
                self.symbol_table.define_typedef(name, final_ty, span)
            {
                let existing_symbol = self.symbol_table.get_symbol(existing);
                if let SymbolKind::Typedef { aliased_type } = existing_symbol.kind {
                    if aliased_type != final_ty {
                        self.report_error(
                            span,
                            SemanticError::RedefinitionWithDifferentType {
                                name,
                                first_def: existing_symbol.def_span,
                            },
                        );
                    }
                } else {
                    self.report_error(
                        span,
                        SemanticError::Redefinition {
                            name,
                            first_def: existing_symbol.def_span,
                        },
                    );
                }
                existing
            } else {
                self.symbol_table.fetch_current(name, Namespace::Ordinary).unwrap()
            };

            self.ast.set_kind(node, NodeKind::TypedefDecl(TypedefDecl { symbol }));
            return Some(node);
        }

        let is_func = final_ty.is_function();

        if !is_func {
            self.check_function_specs(spec_info, span);
        }

        if is_func {
            self.visit_function_decl(node, name, final_ty, spec_info, span)
        } else {
            self.visit_variable_decl(node, name, final_ty, spec_info, init.initializer, span)
        }
        Some(node)
    }

    fn visit_function_decl(
        &mut self,
        node: NodeRef,
        name: NameId,
        final_ty: QualType,
        spec_info: &DeclSpecInfo,
        span: SourceSpan,
    ) {
        let is_global = self.symbol_table.current_scope() == ScopeId::GLOBAL;

        if spec_info.cleanup_func.is_some() {
            self.report_warning(span, SemanticError::AttributeCleanupOnNonLocal);
        }

        self.check_function_constraints(name, spec_info, span, is_global);

        let final_qt = self.check_redeclaration_compatibility(name, final_ty, span, spec_info.storage);
        let param_len = if let TypeKind::Function { parameters, .. } = &self.registry.get(final_qt.ty()).kind {
            parameters.len() as u16
        } else {
            0
        };
        let final_qt = final_ty; // compatibility with existing code below

        let func_sym = match self.symbol_table.define_function(
            name,
            final_qt.ty(),
            span,
            crate::semantic::symbol_table::Function {
                storage: spec_info.storage,
                is_noreturn: spec_info.is_noreturn,
                param_len,
                builtin_kind: None,
            },
            false,
        ) {
            Ok(sym) => sym,
            Err(SymbolTableError::InvalidRedefinition { existing, .. }) => {
                let first_def = self.symbol_table.get_symbol(existing).def_span;
                self.report_error(span, SemanticError::Redefinition { name, first_def });
                existing
            }
        };
        self.ast.set_kind(
            node,
            NodeKind::FunctionDecl(FunctionDecl {
                symbol: func_sym,
                scope_id: self.symbol_table.current_scope(),
            }),
        );
    }

    fn visit_variable_decl(
        &mut self,
        node: NodeRef,
        name: NameId,
        mut qt: QualType,
        spec_info: &DeclSpecInfo,
        init: Option<ParsedNodeRef>,
        span: SourceSpan,
    ) {
        let is_global = self.symbol_table.current_scope() == ScopeId::GLOBAL;

        if spec_info.cleanup_func.is_some() && (is_global || spec_info.storage == Some(StorageClass::Extern)) {
            self.report_warning(span, SemanticError::AttributeCleanupOnNonLocal);
        }

        if spec_info.is_constexpr {
            if init.is_none() {
                self.report_error(span, SemanticError::ConstexprRequiresInitializer);
            }
            qt = self.merge_qualifiers_with_check(qt.strip_all(), qt.qualifiers() | TypeQualifiers::CONST, span);
        }

        if self.registry.get(qt.ty()).kind == TypeKind::AutoType {
            if let Some(init_node) = init {
                let ie = self.visit_expression(init_node);
                if let NodeKind::InitializerList(_) = self.ast.get_kind(ie) {
                    self.report_error(
                        span,
                        SemanticError::AutoTypeNotAllowed {
                            context: "initializer list",
                        },
                    );
                    qt = QualType::unqualified(self.registry.type_error);
                } else if let Some(mut deduced) = self.try_infer_type(ie) {
                    // C11 decay rules apply to __auto_type
                    if deduced.is_array() || deduced.is_function() {
                        deduced = self.registry.decay(deduced, TypeQualifiers::empty());
                    }
                    // Strip top-level qualifiers for non-record types (standard GCC behavior)
                    if !deduced.is_record() {
                        deduced = deduced.strip_all();
                    }
                    qt = deduced.merge_qualifiers(qt.qualifiers());
                } else {
                    // Type could not be inferred yet (e.g. circular dependency or complex expr)
                    // We'll use error type for now.
                    qt = QualType::unqualified(self.registry.type_error);
                }
            } else {
                self.report_error(span, SemanticError::AutoTypeRequiresInitializer);
                qt = QualType::unqualified(self.registry.type_error);
            }
        }

        let is_global = self.symbol_table.current_scope() == ScopeId::GLOBAL;

        // Storage class validation
        if is_global {
            if let Some(st @ (StorageClass::Auto | StorageClass::Register)) = spec_info.storage {
                self.report_error(
                    span,
                    SemanticError::FileScopeSpecifiesStorageClass {
                        name,
                        specifier: st.as_str(),
                    },
                );
            }
        } else if spec_info.is_thread_local
            && !matches!(spec_info.storage, Some(StorageClass::Static | StorageClass::Extern))
        {
            self.report_error(span, SemanticError::ThreadLocalBlockScopeRequiresStaticOrExtern);
        }

        // C11 6.7.6.2p2: "If an identifier is declared to be an object with static or thread storage duration,
        // it shall not have a variably modified type. If an identifier is declared as having a variably
        // modified type, it shall ... have no linkage"
        if self.registry.is_variably_modified(qt.ty()) {
            // Note: GCC and Clang allow variably modified types that are NOT arrays (e.g. pointers to VLAs)
            // to have static storage duration in block scope, despite a literal reading of 6.7.6.2p2.
            // However, 6.7.6.2p2 also says VM types shall have no linkage.
            // 6.7p7: "If an identifier for an object is declared with no linkage, the type for the object
            // shall be complete by the end of its declarator, or by the end of its init-declarator if it has
            // an initializer; in the case of a function variation, the type shall be the same as that of
            // some other declaration of the identifier with no linkage."
            // Wait, 6.7.6.2p2 is very explicit. But let's follow major compilers for block-scope static pointers.

            if spec_info.is_thread_local {
                self.report_error(span, SemanticError::VmThreadStorage);
            } else if (is_global || spec_info.storage == Some(StorageClass::Static)) && qt.is_array() {
                // Static VLAs are definitely prohibited (storage size isn't constant).
                self.report_error(span, SemanticError::VmStaticStorage);
            }

            let has_linkage = if is_global {
                spec_info.storage != Some(StorageClass::Static)
            } else {
                spec_info.storage == Some(StorageClass::Extern)
            };

            if has_linkage {
                self.report_error(span, SemanticError::VmHasLinkage);
            }
        }

        if spec_info.storage == Some(StorageClass::Register) && spec_info.alignment.is_some() {
            self.report_error(
                span,
                SemanticError::AlignmentNotAllowed {
                    context: "register object",
                },
            );
        }

        if spec_info.alignment.is_some() && self.registry.is_variably_modified(qt.ty()) {
            self.report_error(span, SemanticError::AlignasOnVla);
        }

        qt = self.check_redeclaration_compatibility(name, qt, span, spec_info.storage);

        let mut alignment = spec_info.alignment;
        if spec_info.is_packed && alignment.is_none() {
            alignment = Some(1);
        }

        let mut cleanup_sym = None;
        if let Some(cleanup_node) = spec_info.cleanup_func {
            let cleanup_name = if let ParsedNodeKind::Ident(name) = self.parsed_ast.get_node(cleanup_node).kind {
                name
            } else {
                unreachable!()
            };
            match self
                .symbol_table
                .lookup(cleanup_name, self.symbol_table.current_scope(), Namespace::Ordinary)
            {
                Some((sym, _)) => {
                    let sym_entry = self.symbol_table.get_symbol(sym);
                    if let SymbolKind::Function { .. } = sym_entry.kind {
                        cleanup_sym = Some(sym);
                    } else {
                        self.report_error(
                            self.parsed_ast.get_node(cleanup_node).span,
                            SemanticError::CleanupNotAFunction,
                        );
                    }
                }
                None => {
                    self.report_error(
                        self.parsed_ast.get_node(cleanup_node).span,
                        SemanticError::UndeclaredIdentifier { name: cleanup_name },
                    );
                }
            }
        }

        // Define variable in symbol table early so it's visible in its own initializer
        let sym_res = self.symbol_table.define_variable(
            name,
            qt,
            span,
            Variable {
                is_global: self.symbol_table.current_scope() == ScopeId::GLOBAL,
                storage: spec_info.storage,
                is_thread_local: spec_info.is_thread_local,
                initializer: None,
                alignment,
                cleanup_func: cleanup_sym,
            },
        );

        let init_expr = init.map(|n| {
            let ie = self.visit_expression(n);
            if (is_global || spec_info.storage == Some(StorageClass::Static)) && !self.is_constant_expr(ie) {
                self.report_error(self.ast.get_span(ie), SemanticError::NonConstantInitializer);
            }
            if let Ok(sym) = sym_res {
                let (already_defined, first_def) = {
                    let symbol = self.symbol_table.get_symbol(sym);
                    (symbol.def_state == DefinitionState::Defined, symbol.def_span)
                };

                if already_defined {
                    self.report_error(span, SemanticError::Redefinition { name, first_def });
                }

                let symbol = self.symbol_table.get_symbol_mut(sym);
                if let SymbolKind::Variable(v) = &mut symbol.kind {
                    v.initializer = Some(ie);
                }
                symbol.def_state = DefinitionState::Defined;
            }
            ie
        });

        // Deduced array size from initializer
        let element_type = if let TypeKind::Array {
            element_type,
            size: ArraySizeType::Incomplete,
        } = &self.registry.get(qt.ty()).kind
        {
            Some(*element_type)
        } else {
            None
        };

        if let Some(ie) = init_expr
            && let Some(et) = element_type
            && let Some(len) = self.deduce_array_size_full(ie, et)
        {
            if len == 0 && self.lang_opts.c_standard >= CStandard::C23 {
                self.report_error(span, SemanticError::ZeroOrNegativeSizeArray { name });
            }
            qt = QualType::new(
                self.registry.array_of(et, ArraySizeType::Constant(len)),
                qt.qualifiers(),
            );
            if let Ok(sym) = sym_res {
                self.symbol_table.get_symbol_mut(sym).type_info = qt;
            }
        }

        // Linkage and completeness checks
        let has_internal_linkage = is_global && spec_info.storage == Some(StorageClass::Static);
        let has_no_linkage = !is_global && spec_info.storage != Some(StorageClass::Extern);
        if (has_internal_linkage || has_no_linkage) && !self.registry.is_complete(qt.ty()) {
            self.report_error(span, SemanticError::IncompleteType { ty: qt });
        }

        // Finalize AST node
        let var_decl = VarDecl {
            symbol: match sym_res {
                Ok(sym) => sym,
                Err(SymbolTableError::InvalidRedefinition { existing, .. }) => existing,
            },
            init: init_expr,
        };
        self.ast.set_kind(node, NodeKind::VarDecl(var_decl));

        // Validation against redefinition or alignment issues
        if let Err(SymbolTableError::InvalidRedefinition { existing, .. }) = sym_res {
            let first_def = self.symbol_table.get_symbol(existing).def_span;
            self.report_error(span, SemanticError::Redefinition { name, first_def });
        }

        if !spec_info.is_packed
            && let Ok(layout) = self.registry.ensure_layout(qt.ty())
            && let Some(req_align) = spec_info.alignment
        {
            let natural_align = layout.alignment as u64;
            if (req_align as u64) < natural_align {
                self.report_error(
                    span,
                    SemanticError::AlignmentTooLoose {
                        requested: req_align as u64,
                        natural: natural_align,
                    },
                );
            }
        }
    }

    fn visit_node_rest(&mut self, node: ParsedNodeRef, target_slots: Option<&[NodeRef]>) -> SmallVec<[NodeRef; 1]> {
        let node = self.parsed_ast.get_node(node);
        let span = node.span;
        macro_rules! lower_simple {
            ($kind:expr) => {{
                let res_node = self.get_or_push_slot(target_slots, span);
                let kind = $kind;
                self.ast.set_kind(res_node, kind);
                smallvec![res_node]
            }};
        }

        match &node.kind {
            // Simple leaves
            ParsedNodeKind::Literal(l) => {
                lower_simple!(NodeKind::Literal(*l))
            }
            ParsedNodeKind::Ident(name) => {
                lower_simple!(NodeKind::Ident(*name, self.resolve_ident(*name, span)))
            }
            ParsedNodeKind::Break => lower_simple!(NodeKind::Break),
            ParsedNodeKind::Continue => lower_simple!(NodeKind::Continue),
            ParsedNodeKind::EmptyStmt => smallvec![],

            // Unary expressions
            ParsedNodeKind::UnaryOp(op, e) => {
                let mut e = *e;
                let res_node = self.get_or_push_slot(target_slots, span);
                let mut ops = Vec::new();
                ops.push((*op, span, res_node));

                loop {
                    let child = self.parsed_ast.get_node(e);
                    if let ParsedNodeKind::UnaryOp(child_op, child_e) = &child.kind {
                        let inner_node = self.push_dummy(child.span);
                        ops.push((*child_op, child.span, inner_node));
                        e = *child_e;
                    } else {
                        break;
                    }
                }

                let mut current_inner = self.visit_expression(e);

                for (op, span, node_ref) in ops.into_iter().rev() {
                    self.ast.set_kind(node_ref, NodeKind::UnaryOp(op, current_inner));
                    self.ast.set_span(node_ref, span);
                    current_inner = node_ref;
                }

                smallvec![res_node]
            }
            ParsedNodeKind::PostIncrement(e) => {
                lower_simple!(NodeKind::PostIncrement(self.visit_expression(*e)))
            }
            ParsedNodeKind::PostDecrement(e) => {
                lower_simple!(NodeKind::PostDecrement(self.visit_expression(*e)))
            }
            ParsedNodeKind::SizeOfExpr(e) => {
                lower_simple!(NodeKind::SizeOfExpr(self.visit_expression(*e)))
            }
            ParsedNodeKind::Default(s) => {
                lower_simple!(NodeKind::Default(self.visit_single_statement(*s)))
            }

            // Binary expressions
            ParsedNodeKind::BinaryOp(op, l, r) => lower_simple!(NodeKind::BinaryOp(
                *op,
                self.visit_expression(*l),
                self.visit_expression(*r)
            )),
            ParsedNodeKind::Assignment(op, l, r) => lower_simple!(NodeKind::Assignment(
                *op,
                self.visit_expression(*l),
                self.visit_expression(*r)
            )),
            ParsedNodeKind::IndexAccess(l, r) => lower_simple!(NodeKind::IndexAccess(
                self.visit_expression(*l),
                self.visit_expression(*r)
            )),
            ParsedNodeKind::MemberAccess(b, m, a) => {
                lower_simple!(NodeKind::MemberAccess(self.visit_expression(*b), *m, *a))
            }
            ParsedNodeKind::BuiltinComplex(real, imag) => lower_simple!(NodeKind::BuiltinComplex(
                self.visit_expression(*real),
                self.visit_expression(*imag)
            )),
            ParsedNodeKind::DoWhile(b, c) => lower_simple!(NodeKind::DoWhile(
                self.visit_single_statement(*b),
                self.visit_expression(*c)
            )),
            ParsedNodeKind::Switch(c, b) => lower_simple!(NodeKind::Switch(
                self.visit_expression(*c),
                self.visit_single_statement(*b)
            )),
            ParsedNodeKind::Case(e, s) => lower_simple!(NodeKind::Case(
                self.visit_expression(*e),
                self.visit_single_statement(*s)
            )),
            ParsedNodeKind::StaticAssert(c, m) => lower_simple!(NodeKind::StaticAssert(
                self.visit_expression(*c),
                m.map(|msg| self.visit_expression(msg))
            )),

            // Ternary expressions
            ParsedNodeKind::TernaryOp(c, t, e) => lower_simple!(NodeKind::TernaryOp(
                self.visit_expression(*c),
                self.visit_expression(*t),
                self.visit_expression(*e)
            )),
            ParsedNodeKind::CaseRange(s, e, stmt) => {
                self.report_warning(span, SemanticError::GnuCaseRange);
                lower_simple!(NodeKind::CaseRange(
                    self.visit_expression(*s),
                    self.visit_expression(*e),
                    self.visit_single_statement(*stmt)
                ))
            }
            ParsedNodeKind::BuiltinChooseExpr(c, t, e) => {
                let res_node = self.get_or_push_slot(target_slots, span);

                let lowered_cond = self.visit_expression(*c);
                let ctx = crate::semantic::const_eval::ConstEvalCtx {
                    ast: self.ast,
                    symbol_table: self.symbol_table,
                    registry: self.registry,
                    semantic_info: &self.ast.semantic_info,
                };

                let (lowered_true, lowered_false) = match ctx.eval_int(lowered_cond) {
                    Some(val) if val != 0 => (
                        self.visit_expression(*t),
                        self.push_dummy(self.parsed_ast.get_node(*e).span),
                    ),
                    Some(_) => (
                        self.push_dummy(self.parsed_ast.get_node(*t).span),
                        self.visit_expression(*e),
                    ),
                    None => (self.visit_expression(*t), self.visit_expression(*e)),
                };

                self.ast.set_kind(
                    res_node,
                    NodeKind::BuiltinChooseExpr(lowered_cond, lowered_true, lowered_false),
                );
                smallvec![res_node]
            }

            // Control flow with scopes
            ParsedNodeKind::If(stmt) => lower_simple!(NodeKind::If(IfStmt {
                condition: self.visit_expression(stmt.condition),
                then_branch: self.visit_single_statement(stmt.then_branch),
                else_branch: stmt.else_branch.map(|b| self.visit_single_statement(b)),
            })),
            ParsedNodeKind::While(stmt) => lower_simple!(NodeKind::While(WhileStmt {
                condition: self.visit_expression(stmt.condition),
                body: self.visit_single_statement(stmt.body),
            })),
            ParsedNodeKind::For(stmt) => {
                let res_node = self.get_or_push_slot(target_slots, span);
                let scope_id = self.symbol_table.push_scope();
                let child_start = self.push_dummy(span);
                let condition_dummy = self.push_dummy(span);
                let increment_dummy = self.push_dummy(span);

                if let Some(init) = stmt.init {
                    self.visit_node_entry(init, Some(&[child_start]));
                }
                if let Some(cond) = stmt.condition {
                    self.visit_node_entry(cond, Some(&[condition_dummy]));
                }
                if let Some(inc) = stmt.increment {
                    self.visit_node_entry(inc, Some(&[increment_dummy]));
                }

                let body = self.visit_single_statement(stmt.body);

                self.ast.set_kind(
                    res_node,
                    NodeKind::For(ForStmt {
                        child_start,
                        body,
                        scope_id,
                    }),
                );
                self.symbol_table.pop_scope();
                smallvec![res_node]
            }

            // Type-related expressions
            ParsedNodeKind::Cast(t, e) => {
                lower_simple!(NodeKind::Cast(self.visit_type(*t, span), self.visit_expression(*e)))
            }
            ParsedNodeKind::BuiltinVaArg(t, e) => lower_simple!(NodeKind::BuiltinVaArg(
                self.visit_type(*t, span),
                self.visit_expression(*e)
            )),
            ParsedNodeKind::BuiltinOffsetof(t, e) => lower_simple!(NodeKind::BuiltinOffsetof(
                self.visit_type(*t, span),
                self.visit_expression(*e)
            )),
            ParsedNodeKind::BuiltinBitCast(t, e) => lower_simple!(NodeKind::BuiltinBitCast(
                self.visit_type(*t, span),
                self.visit_expression(*e)
            )),
            ParsedNodeKind::BuiltinConvertVector(e, t) => lower_simple!(NodeKind::BuiltinConvertVector(
                self.visit_expression(*e),
                self.visit_type(*t, span)
            )),
            ParsedNodeKind::SizeOfType(t) => lower_simple!(NodeKind::SizeOfType(self.visit_type(*t, span))),
            ParsedNodeKind::AlignOfType(t) => lower_simple!(NodeKind::AlignOfType(self.visit_type(*t, span))),
            ParsedNodeKind::AlignOfExpr(e) => lower_simple!(NodeKind::AlignOfExpr(self.visit_expression(*e))),
            ParsedNodeKind::BuiltinTypesCompatibleP(boxed) => {
                let (t1, t2) = &**boxed;
                lower_simple!(NodeKind::BuiltinTypesCompatibleP(
                    self.visit_type(*t1, span),
                    self.visit_type(*t2, span)
                ))
            }

            // Statement wrappers
            ParsedNodeKind::Return(e) => {
                lower_simple!(NodeKind::Return(e.map(|x| self.visit_expression(x))))
            }
            ParsedNodeKind::ExpressionStmt(e) => {
                lower_simple!(NodeKind::ExpressionStmt(e.map(|x| self.visit_expression(x))))
            }
            ParsedNodeKind::AsmStmt(e) => {
                lower_simple!(NodeKind::AsmStmt(self.visit_expression(*e)))
            }
            ParsedNodeKind::Goto(n) => {
                lower_simple!(NodeKind::Goto(*n, self.resolve_label(*n, span)))
            }
            ParsedNodeKind::Label(n, i) => {
                let sym = self.define_label(*n, span);
                lower_simple!(NodeKind::Label(*n, self.visit_single_statement(*i), sym))
            }

            // Declarations
            ParsedNodeKind::Declaration(decl) => self.visit_declaration(decl, span, target_slots),

            // Complex variants extracted to helpers
            ParsedNodeKind::GnuStatementExpr(stmt, _) => {
                if self.lang_opts.pedantic || self.lang_opts.pedantic_errors {
                    self.report_warning(span, SemanticError::GnuStatementExpression);
                }
                lower_simple!(self.visit_gnu_statement_expr(*stmt, span))
            }
            ParsedNodeKind::FunctionCall(func, args) => {
                let node = self.get_or_push_slot(target_slots, span);
                let kind = self.visit_function_call(*func, args.as_ref(), span);
                self.ast.set_kind(node, kind);
                smallvec![node]
            }
            ParsedNodeKind::CompoundLiteral(ty, init) => {
                lower_simple!(self.visit_compound_literal(*ty, *init, span))
            }
            ParsedNodeKind::GenericSelection(ctrl, assocs) => {
                let node = self.get_or_push_slot(target_slots, span);
                let kind = self.visit_generic_selection(*ctrl, assocs.as_ref(), span);
                self.ast.set_kind(node, kind);
                smallvec![node]
            }
            ParsedNodeKind::InitializerList(inits) => {
                let node = self.get_or_push_slot(target_slots, span);
                let kind = self.visit_initializer_list(inits.as_ref(), span);
                self.ast.set_kind(node, kind);
                smallvec![node]
            }

            _ => smallvec![self.push_dummy(span)],
        }
    }

    fn visit_expression(&mut self, node: ParsedNodeRef) -> NodeRef {
        self.visit_node(node)
            .first()
            .copied()
            .unwrap_or_else(|| self.push_dummy(SourceSpan::default()))
    }

    fn visit_expression_into(&mut self, node: ParsedNodeRef, target: NodeRef) -> NodeRef {
        self.visit_node_entry(node, Some(&[target]))
            .first()
            .copied()
            .unwrap_or(target)
    }

    fn visit_single_statement(&mut self, node: ParsedNodeRef) -> NodeRef {
        self.visit_expression(node)
    }

    fn visit_single_statement_into(&mut self, node: ParsedNodeRef, target: NodeRef) -> NodeRef {
        self.visit_expression_into(node, target)
    }

    fn visit_type(&mut self, ty: ParsedType, span: SourceSpan) -> QualType {
        self.lower_type(ty, span, false)
            .unwrap_or_else(|_| QualType::unqualified(self.registry.type_error))
    }

    fn lower_type(
        &mut self,
        parsed_type: ParsedType,
        span: SourceSpan,
        in_parameter: bool,
    ) -> Result<QualType, SemanticDiag> {
        let base_type_node = {
            let parsed_types = &self.parsed_ast.parsed_types;
            parsed_types.get_base_type(parsed_type.base)
        };

        let declarator = parsed_type.declarator;
        let qualifiers = parsed_type.qualifiers;

        let qbase = self.convert_to_qual_type(base_type_node, span)?;
        let qbase = self.merge_qualifiers_with_check(qbase, qualifiers, span);

        let final_type = self.apply_declarator(qbase, declarator, span, None, DeclaratorContext { in_parameter });

        if in_parameter {
            let ptr_quals = self.extract_array_param_qualifiers(declarator);
            Ok(self.registry.decay(final_type, ptr_quals))
        } else {
            Ok(final_type)
        }
    }

    fn extract_array_param_qualifiers(&self, declarator: DeclaratorRef) -> TypeQualifiers {
        let declarator = self.parsed_ast.parsed_types.get_decl(declarator);
        match declarator {
            ParsedDeclarator::Identifier(..) => TypeQualifiers::empty(),
            ParsedDeclarator::Pointer { .. } => TypeQualifiers::empty(),
            ParsedDeclarator::Function { .. } => TypeQualifiers::empty(),
            ParsedDeclarator::Array { inner, size } => {
                let inner_quals = self.extract_array_param_qualifiers(*inner);
                if !inner_quals.is_empty() {
                    return inner_quals;
                }
                size.qualifiers()
            }
            ParsedDeclarator::BitField { inner, .. } => self.extract_array_param_qualifiers(*inner),
            ParsedDeclarator::Attribute { inner, .. } => self.extract_array_param_qualifiers(*inner),
        }
    }

    fn extract_name(&self, declarator: DeclaratorRef) -> Option<NameId> {
        let declarator = self.parsed_ast.parsed_types.get_decl(declarator);
        match declarator {
            ParsedDeclarator::Identifier(name) => *name,
            ParsedDeclarator::Pointer { inner, .. } => self.extract_name(*inner),
            ParsedDeclarator::Array { inner, .. } => self.extract_name(*inner),
            ParsedDeclarator::Function { inner, .. } => self.extract_name(*inner),
            ParsedDeclarator::BitField { inner, .. } => self.extract_name(*inner),
            ParsedDeclarator::Attribute { inner, .. } => self.extract_name(*inner),
        }
    }

    fn visit_gnu_statement_expr(&mut self, stmt: ParsedNodeRef, span: SourceSpan) -> NodeKind {
        let s = self.visit_single_statement(stmt);
        let result_expr = if let NodeKind::CompoundStmt(data) = self.ast.get_kind(s) {
            data.stmt_start
                .range(data.stmt_len)
                .last()
                .and_then(|stmt| {
                    if let NodeKind::ExpressionStmt(Some(e)) = self.ast.get_kind(stmt) {
                        Some(*e)
                    } else {
                        None
                    }
                })
                .unwrap_or_else(|| self.push_dummy(span))
        } else {
            self.push_dummy(span)
        };

        NodeKind::StatementExpr(s, result_expr)
    }

    fn visit_function_call(&mut self, func: ParsedNodeRef, args: &[ParsedNodeRef], span: SourceSpan) -> NodeKind {
        let f = self.visit_expression(func);
        let mut arg_dummies = Vec::with_capacity(args.len());
        for _ in 0..args.len() {
            arg_dummies.push(self.push_dummy(span));
        }
        for (i, &arg) in args.iter().enumerate() {
            self.visit_expression_into(arg, arg_dummies[i]);
        }
        let arg_start = arg_dummies.first().copied().unwrap_or(NodeRef::ROOT);

        NodeKind::FunctionCall(CallExpr {
            callee: f,
            arg_start,
            arg_len: args.len() as u16,
        })
    }

    fn visit_compound_literal(&mut self, ty_name: ParsedType, init: ParsedNodeRef, span: SourceSpan) -> NodeKind {
        let mut qt = self.visit_type(ty_name, span);
        let i = self.visit_expression(init);

        if let TypeKind::Array {
            element_type,
            size: ArraySizeType::Incomplete,
        } = &self.registry.get(qt.ty()).kind
        {
            let element_type = *element_type;
            if let Some(deduced_size) = self.deduce_array_size_full(i, element_type) {
                let new_ty = self
                    .registry
                    .array_of(element_type, ArraySizeType::Constant(deduced_size));
                qt = QualType::new(new_ty, qt.qualifiers());
            }
        }
        NodeKind::CompoundLiteral(qt, i)
    }

    fn visit_generic_selection(
        &mut self,
        control: ParsedNodeRef,
        associations: &[ParsedGenericAssociation],
        span: SourceSpan,
    ) -> NodeKind {
        let c = self.visit_expression(control);
        let assoc_len = associations.len() as u16;
        let mut assoc_dummies = Vec::with_capacity(associations.len());
        for _ in 0..assoc_len {
            assoc_dummies.push(self.push_dummy(span));
        }

        for (i, a) in associations.iter().enumerate() {
            let ty = a.type_name.map(|t| self.visit_type(t, span));
            let expr = self.visit_expression(a.result_expr);
            self.ast.set_kind(
                assoc_dummies[i],
                NodeKind::GenericAssociation(GenericAssociation { ty, result_expr: expr }),
            );
        }

        let assoc_start = assoc_dummies.first().copied().unwrap_or(NodeRef::ROOT);
        NodeKind::GenericSelection(GenericSelection {
            control: c,
            assoc_start,
            assoc_len,
        })
    }

    fn visit_initializer_list(&mut self, inits: &[ParsedDesignatedInitializer], span: SourceSpan) -> NodeKind {
        let mut init_dummies = Vec::with_capacity(inits.len());
        for _ in 0..inits.len() {
            init_dummies.push(self.push_dummy(span));
        }

        for (i, init) in inits.iter().enumerate() {
            let expr = self.visit_expression(init.initializer);
            let designator_count = init.designation.len() as u16;
            let mut designator_dummies = Vec::with_capacity(designator_count as usize);

            for _ in 0..designator_count {
                designator_dummies.push(self.push_dummy(span));
            }

            for (j, d) in init.designation.iter().enumerate() {
                let node_kind = match d {
                    ParsedDesignator::FieldName(name) => Designator::FieldName(*name),
                    ParsedDesignator::ArrayIndex(idx) => Designator::ArrayIndex(self.visit_expression(*idx)),
                    ParsedDesignator::ArrayRange(start, end) => {
                        self.report_warning(
                            self.parsed_ast.nodes[start.get() as usize].span,
                            SemanticError::GnuDesignatedInitializerRange,
                        );
                        Designator::ArrayRange(self.visit_expression(*start), self.visit_expression(*end))
                    }
                };
                self.ast
                    .set_kind(designator_dummies[j], NodeKind::Designator(node_kind));
            }

            let designator_start = designator_dummies.first().copied().unwrap_or(NodeRef::ROOT);
            let di = DesignatedInitializer {
                designator_start,
                designator_len: designator_count,
                initializer: expr,
            };
            self.ast.set_kind(init_dummies[i], NodeKind::InitializerItem(di));
        }

        let init_start = init_dummies.first().copied().unwrap_or(NodeRef::ROOT);
        NodeKind::InitializerList(InitializerList {
            init_start,
            init_len: inits.len() as u16,
        })
    }

    /// Convert ParsedArraySize to ArraySizeType
    fn convert_parsed_array_size(&mut self, size: &ParsedArraySize) -> ArraySizeType {
        if size.is_star() {
            ArraySizeType::Star
        } else {
            self.resolve_array_size(size.size_expr())
        }
    }

    /// Helper function to resolve array size logic
    fn resolve_array_size(&mut self, size: Option<ParsedNodeRef>) -> ArraySizeType {
        let Some(node) = size else {
            return ArraySizeType::Incomplete;
        };

        let expr = self.visit_expression(node);

        // C11 6.7.6.2p1: Check if the expression is a float literal (non-integer type)
        if let NodeKind::Literal(literal_id) = self.ast.get_kind(expr)
            && literal_id.kind() == LitKind::Float
        {
            self.report_error(self.ast.get_span(expr), SemanticError::ArraySizeNotInteger);
            return ArraySizeType::Incomplete;
        }

        match self.const_ctx().eval_int(expr) {
            Some(val) => {
                // C11 6.7.6.2p1: the expression shall have a value greater than zero
                // Extension: allow zero-sized arrays unless pedantic-errors is set
                if val < 0 {
                    self.report_error(self.ast.get_span(expr), SemanticError::InvalidArraySize);
                    return ArraySizeType::Incomplete;
                } else if val == 0 {
                    self.report_warning(self.ast.get_span(expr), SemanticError::GnuZeroLengthArray);
                }
                ArraySizeType::Constant(val as usize)
            }
            None => ArraySizeType::Variable(expr),
        }
    }

    fn resolve_ident(&mut self, name: NameId, span: SourceSpan) -> SymbolRef {
        if let Some(sym) = self.symbol_table.lookup_symbol(name) {
            sym
        } else {
            if let Some(sym) = self.handle_builtin_implicit_decl(name, span) {
                return sym;
            }
            self.report_error(span, SemanticError::UndeclaredIdentifier { name });
            SymbolRef::new(1).expect("SymbolRef 1 creation failed")
        }
    }

    fn handle_builtin_implicit_decl(&mut self, name: NameId, _span: SourceSpan) -> Option<SymbolRef> {
        let kind = self.keywords.identify(name)?;

        let func_ty = self.registry.builtin_function_type(kind);
        let param_len = if let TypeKind::Function { parameters, .. } = &self.registry.get(func_ty).kind {
            parameters.len() as u16
        } else {
            0
        };
        self.symbol_table
            .define_builtin_function(
                name,
                func_ty,
                crate::semantic::symbol_table::Function {
                    storage: Some(StorageClass::Extern),
                    is_noreturn: false,
                    param_len,
                    builtin_kind: Some(kind),
                },
            )
            .ok()
    }

    fn define_label(&mut self, name: NameId, span: SourceSpan) -> SymbolRef {
        match self.symbol_table.define_label(name, self.registry.type_void, span) {
            Ok(sym) => sym,
            Err(_) => {
                // If already defined (e.g. by pre-scan), look it up
                self.symbol_table
                    .lookup_label(name)
                    .map(|(s, _)| s)
                    .unwrap_or_else(|| SymbolRef::new(1).unwrap())
            }
        }
    }

    fn resolve_label(&mut self, name: NameId, span: SourceSpan) -> SymbolRef {
        if let Some((sym, _)) = self.symbol_table.lookup_label(name) {
            sym
        } else {
            // Forward references are okay because of pre-scan
            // But if NOT even in pre-scan, then it's undeclared
            self.report_error(span, SemanticError::UndeclaredIdentifier { name });
            SymbolRef::new(1).unwrap()
        }
    }

    fn collect_labels(&mut self, node: ParsedNodeRef) {
        let parsed_node = self.parsed_ast.get_node(node);
        if let ParsedNodeKind::Label(name, _) = &parsed_node.kind
            && let Err(SymbolTableError::InvalidRedefinition { existing, .. }) =
                self.symbol_table
                    .define_label(*name, self.registry.type_void, parsed_node.span)
        {
            let first_def = self.symbol_table.get_symbol(existing).def_span;
            self.report_error(parsed_node.span, SemanticError::Redefinition { name: *name, first_def });
        }
        let mut f = |child| self.collect_labels(child);
        parsed_node.kind.for_each_child(&mut f);
    }

    /// Try to infer the type of an expression node during lowering.
    /// This is limited because full semantic analysis hasn't run yet.
    fn is_constant_expr(&self, node: NodeRef) -> bool {
        match self.ast.get_kind(node) {
            NodeKind::Literal(_) => true,
            NodeKind::Ident(_, sym) => {
                let symbol = self.symbol_table.get_symbol(*sym);
                if matches!(symbol.kind, SymbolKind::EnumConstant { .. }) {
                    return true;
                }
                // Function designators and array names are effectively constants (pointers)
                if symbol.is_function() || symbol.type_info.is_array() {
                    return symbol.has_static_duration();
                }
                false
            }
            NodeKind::UnaryOp(UnaryOp::AddrOf, expr) => self.is_static_duration_object(*expr),
            NodeKind::BinaryOp(op, l, r) => {
                if *op == BinaryOp::Comma {
                    return false;
                }
                self.is_constant_expr(*l) && self.is_constant_expr(*r)
            }
            NodeKind::UnaryOp(op, e) => match op {
                UnaryOp::AddrOf => unreachable!(),
                UnaryOp::Deref => false,
                _ => self.is_constant_expr(*e),
            },
            NodeKind::Cast(_, e) => self.is_constant_expr(*e),
            NodeKind::TernaryOp(c, t, e) => {
                self.is_constant_expr(*c) && self.is_constant_expr(*t) && self.is_constant_expr(*e)
            }
            NodeKind::InitializerList(list) => {
                for item in list.init_start.range(list.init_len) {
                    if let NodeKind::InitializerItem(ii) = self.ast.get_kind(item)
                        && !self.is_constant_expr(ii.initializer)
                    {
                        return false;
                    }
                }
                true
            }
            NodeKind::CompoundLiteral(_, init_list) => {
                if self.symbol_table.current_scope() != ScopeId::GLOBAL {
                    return false;
                }
                if let NodeKind::InitializerList(list) = self.ast.get_kind(*init_list) {
                    for item in list.init_start.range(list.init_len) {
                        if let NodeKind::InitializerItem(ii) = self.ast.get_kind(item)
                            && !self.is_constant_expr(ii.initializer)
                        {
                            return false;
                        }
                    }
                }
                true
            }
            NodeKind::SizeOfExpr(_)
            | NodeKind::SizeOfType(_)
            | NodeKind::AlignOfExpr(_)
            | NodeKind::AlignOfType(_)
            | NodeKind::BuiltinChooseExpr(..)
            | NodeKind::BuiltinOffsetof(..) => true,

            NodeKind::FunctionCall(call) => {
                if let NodeKind::Ident(name, _) = self.ast.get_kind(call.callee)
                    && name.as_str().starts_with("__builtin_")
                {
                    return true;
                }
                self.const_ctx().eval_int(node).is_some() || self.const_ctx().eval_float(node).is_some()
            }

            NodeKind::GenericSelection(gs) => {
                for assoc_node in gs.assoc_start.range(gs.assoc_len) {
                    if let NodeKind::GenericAssociation(assoc) = self.ast.get_kind(assoc_node)
                        && !self.is_constant_expr(assoc.result_expr)
                    {
                        return false;
                    }
                }
                true
            }
            _ => self.const_ctx().eval_int(node).is_some() || self.const_ctx().eval_float(node).is_some(),
        }
    }

    fn is_static_duration_object(&self, node: NodeRef) -> bool {
        match self.ast.get_kind(node) {
            NodeKind::Ident(_, sym) => {
                let symbol = self.symbol_table.get_symbol(*sym);
                symbol.has_static_duration()
            }
            NodeKind::IndexAccess(base, index) => {
                self.is_static_duration_object(*base) && self.is_constant_expr(*index)
            }
            NodeKind::MemberAccess(base, ..) => self.is_static_duration_object(*base),
            NodeKind::CompoundLiteral(..) => self.symbol_table.current_scope() == ScopeId::GLOBAL,
            NodeKind::Cast(_, e) => self.is_static_duration_object(*e),
            _ => false,
        }
    }

    fn try_infer_type(&mut self, node: NodeRef) -> Option<QualType> {
        use crate::semantic::conversions::{integer_promotion, usual_arithmetic_conversions};

        let node_kind = *self.ast.get_kind(node);
        match node_kind {
            NodeKind::Literal(l) => Some(self.get_literal_type(l)),
            NodeKind::Ident(_, symbol) => {
                let sym = self.symbol_table.get_symbol(symbol);
                match &sym.kind {
                    SymbolKind::Variable { .. } | SymbolKind::Function { .. } => Some(sym.type_info),
                    SymbolKind::EnumConstant { .. } => Some(QualType::unqualified(self.registry.type_int)),
                    _ => None,
                }
            }
            NodeKind::Cast(qt, _) => Some(qt.strip_all()),
            NodeKind::CompoundLiteral(qt, _) => Some(qt),
            NodeKind::MemberAccess(obj, name, is_arrow) => {
                let obj_qt = self.try_infer_type(obj)?;
                let ty = if is_arrow {
                    self.registry.get_pointee(obj_qt.ty())?.ty()
                } else {
                    obj_qt.ty()
                };
                let type_info = self.registry.get(ty).into_owned();
                type_info.find_member(self.registry, name).map(|m| m.member_type)
            }
            NodeKind::IndexAccess(base, _) => {
                let base_qt = self.try_infer_type(base)?;
                let elem = self.registry.get_array_element(base_qt.ty())?;
                Some(QualType::unqualified(elem))
            }
            NodeKind::UnaryOp(op, expr) => match op {
                UnaryOp::Deref => {
                    let qt = self.try_infer_type(expr)?;
                    self.registry.get_pointee(qt.ty())
                }
                UnaryOp::AddrOf => {
                    let qt = self.try_infer_type(expr)?;
                    let ptr = self.registry.pointer_to(qt);
                    Some(QualType::unqualified(ptr))
                }
                UnaryOp::Plus | UnaryOp::Minus | UnaryOp::BitNot => {
                    let qt = self.try_infer_type(expr)?;
                    Some(if qt.is_integer() {
                        integer_promotion(self.registry, qt, None)
                    } else {
                        qt
                    })
                }
                UnaryOp::LogicNot => Some(QualType::unqualified(self.registry.type_int)),
                _ => None,
            },
            NodeKind::FunctionCall(call) => {
                let func_qt = self.try_infer_type(call.callee)?;
                let mut func_ty = func_qt.ty();
                if func_ty.is_pointer() {
                    func_ty = self.registry.get_pointee(func_ty)?.ty();
                }
                if let TypeKind::Function { return_type, .. } = &self.registry.get(func_ty).kind {
                    Some(QualType::unqualified(*return_type))
                } else {
                    None
                }
            }
            NodeKind::BinaryOp(op, l, r) => match op {
                BinaryOp::Comma => self.try_infer_type(r),
                BinaryOp::Equal
                | BinaryOp::NotEqual
                | BinaryOp::Less
                | BinaryOp::LessEqual
                | BinaryOp::Greater
                | BinaryOp::GreaterEqual
                | BinaryOp::LogicAnd
                | BinaryOp::LogicOr => Some(QualType::unqualified(self.registry.type_int)),
                BinaryOp::Add
                | BinaryOp::Sub
                | BinaryOp::Mul
                | BinaryOp::Div
                | BinaryOp::Mod
                | BinaryOp::BitAnd
                | BinaryOp::BitOr
                | BinaryOp::BitXor
                | BinaryOp::LShift
                | BinaryOp::RShift => {
                    let lt = self.try_infer_type(l)?;
                    let rt = self.try_infer_type(r)?;

                    if (op == BinaryOp::Add || op == BinaryOp::Sub) && lt.is_pointer() {
                        Some(lt)
                    } else if op == BinaryOp::Add && rt.is_pointer() {
                        Some(rt)
                    } else if lt.is_arithmetic() && rt.is_arithmetic() {
                        usual_arithmetic_conversions(self.registry, lt, rt)
                    } else {
                        Some(lt)
                    }
                }
                _ => None,
            },
            NodeKind::Assignment(_, l, _) => self.try_infer_type(l),
            NodeKind::TernaryOp(_, t, e) => {
                let tt = self.try_infer_type(t)?;
                let et = self.try_infer_type(e)?;
                if tt.ty() == et.ty() {
                    Some(tt)
                } else {
                    usual_arithmetic_conversions(self.registry, tt, et)
                }
            }
            NodeKind::SizeOfExpr(_)
            | NodeKind::SizeOfType(_)
            | NodeKind::AlignOfExpr(_)
            | NodeKind::AlignOfType(_)
            | NodeKind::BuiltinOffsetof(..)
            | NodeKind::BuiltinTypesCompatibleP(..) => Some(QualType::unqualified(self.registry.type_long_unsigned)),
            _ => None,
        }
    }

    fn get_literal_type(&mut self, lit: LitRef) -> QualType {
        let ty = match lit.get_val() {
            LitVal::Int { .. } => self.registry.type_int,
            LitVal::Float { suffix, .. } => suffix.get_type(self.registry),
            LitVal::Char(_, prefix) => prefix.get_type(self.registry),
            LitVal::String { value: s, prefix } => {
                // Bolt ⚡: Use metadata-only accessors to avoid full literal lowering.
                let builtin_type = get_string_builtin_type(prefix);
                let size = get_string_literal_size(&s, prefix);
                let elem = self.registry.get_builtin_type(builtin_type);
                self.registry.array_of(elem, ArraySizeType::Constant(size))
            }
            LitVal::Nullptr => self.registry.type_nullptr_t,
            LitVal::True | LitVal::False => self.registry.type_bool,
        };
        QualType::unqualified(ty)
    }

    fn try_deduce_string_initializer_size(&mut self, init_node: NodeRef, element_type: TypeRef) -> Option<usize> {
        match self.ast.get_kind(init_node) {
            NodeKind::Literal(literal_id) => match literal_id.get_val() {
                // Bolt ⚡: Use metadata-only accessor to avoid full literal lowering.
                LitVal::String { value, prefix } => Some(get_string_literal_size(&value, prefix)),
                _ => None,
            },
            NodeKind::InitializerList(list) if list.init_len > 0 => {
                if let NodeKind::InitializerItem(item) = self.ast.get_kind(list.init_start)
                    && item.designator_len == 0
                    && let NodeKind::Literal(literal_id) = self.ast.get_kind(item.initializer)
                    && let LitVal::String { value, prefix } = literal_id.get_val()
                    // Bolt ⚡: Use metadata-only accessors.
                    && let builtin_type = get_string_builtin_type(prefix)
                    && let size = get_string_literal_size(&value, prefix)
                    && self.registry.is_compatible(
                        QualType::unqualified(element_type),
                        QualType::unqualified(self.registry.get_builtin_type(builtin_type)),
                    )
                {
                    Some(size)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    fn deduce_array_size_full(&mut self, init_node: NodeRef, element_type: TypeRef) -> Option<usize> {
        if let Some(size) = self.try_deduce_string_initializer_size(init_node, element_type) {
            return Some(size);
        }

        let kind = *self.ast.get_kind(init_node);
        match kind {
            NodeKind::InitializerList(list) => {
                let mut max_index: i64 = -1;
                let mut current_index: i64 = 0;

                let mut iter = list.init_start.range(list.init_len).peekable();

                while let Some(item) = iter.peek().copied() {
                    let item_kind = *self.ast.get_kind(item);
                    let NodeKind::InitializerItem(init) = item_kind else {
                        iter.next();
                        continue;
                    };

                    if init.designator_len > 0 {
                        let designator_kind = *self.ast.get_kind(init.designator_start);
                        match designator_kind {
                            NodeKind::Designator(Designator::ArrayIndex(idx)) => {
                                current_index = self.const_ctx().eval_int(idx)?;
                            }
                            NodeKind::Designator(Designator::ArrayRange(start, end)) => {
                                let s_v = self.const_ctx().eval_int(start)?;
                                let e_v = self.const_ctx().eval_int(end)?;
                                if s_v > e_v {
                                    return None;
                                }
                                current_index = e_v;
                            }
                            _ => {}
                        }
                    }

                    max_index = max_index.max(current_index);

                    let start_item = iter.peek().map(|n| n.raw());
                    self.consume_initializers(element_type, &mut iter, true);

                    if let Some(end_item) = iter.peek().map(|n| n.raw())
                        && start_item == Some(end_item)
                    {
                        iter.next();
                    }

                    current_index += 1;
                }

                Some((max_index + 1) as usize)
            }
            _ => None,
        }
    }

    fn consume_initializers<I>(
        &mut self,
        element_type: TypeRef,
        iter: &mut std::iter::Peekable<I>,
        allow_array_designator: bool,
    ) where
        I: Iterator<Item = NodeRef>,
    {
        // Check if there are more items
        let Some(item) = iter.peek().copied() else {
            return;
        };

        let item_kind = *self.ast.get_kind(item);
        let NodeKind::InitializerItem(init) = item_kind else {
            // Should not happen in valid AST
            return;
        };

        if init.designator_len == 0 {
            // C11 6.7.9p14: Character array initialized by string literal
            if element_type.is_array()
                && let Some(et) = self.registry.get_array_element(element_type)
                && (et.is_char() || et.is_wchar_t())
            {
                let kind = *self.ast.get_kind(init.initializer);
                if let NodeKind::Literal(lid) = kind
                    && lid.kind() == LitKind::String
                {
                    iter.next();
                    return;
                }
            }
        }

        if init.designator_len > 0 {
            // Check for array designators
            match *self.ast.get_kind(init.designator_start) {
                NodeKind::Designator(Designator::ArrayIndex(_))
                | NodeKind::Designator(Designator::ArrayRange(_, _)) => {
                    if !allow_array_designator {
                        return;
                    }
                    // If allowed, we proceed to consume this item (and potentially others)
                }
                _ => {
                    // Field designator.
                    // For now, we assume field designators consume one item from the list.
                    // (Strictly we should check if it belongs to current struct, but for size counting
                    // we assume valid C code).
                    iter.next();
                    return;
                }
            }
        } else if element_type.is_record() {
            // Check for struct-to-struct initialization
            if let Some(ty) = self.try_infer_type(init.initializer)
                && self.registry.is_compatible(QualType::unqualified(element_type), ty)
            {
                iter.next();
                return;
            }
        }

        // Check braced initializer
        if let NodeKind::InitializerList(_) = *self.ast.get_kind(init.initializer) {
            iter.next();
            return;
        }

        // Brace elision logic
        enum AggTask {
            Record(Arc<[RecordMember]>),
            Array(TypeRef, usize),
            Scalar,
        }
        let task = {
            let type_info = self.registry.get(element_type);
            match &type_info.kind {
                TypeKind::Record { members, .. } => AggTask::Record(Arc::clone(members)),
                TypeKind::Array {
                    element_type,
                    size: ArraySizeType::Constant(len),
                } => AggTask::Array(*element_type, *len),
                _ => AggTask::Scalar,
            }
        };

        match task {
            AggTask::Record(members) => {
                let mut is_first_member = true;
                for member in members.iter() {
                    let allow = allow_array_designator && is_first_member;
                    self.consume_initializers(member.member_type.ty(), iter, allow);
                    is_first_member = false;

                    // If we stopped consuming, we should also stop for this record
                    if iter.peek().is_none() {
                        return;
                    }
                    // Check if next item is an array designator (stopper)
                    if let Some(next) = iter.peek()
                        && let item_kind = *self.ast.get_kind(*next)
                        && let NodeKind::InitializerItem(next_init) = item_kind
                        && next_init.designator_len > 0
                    {
                        match *self.ast.get_kind(next_init.designator_start) {
                            NodeKind::Designator(Designator::ArrayIndex(_))
                            | NodeKind::Designator(Designator::ArrayRange(_, _)) => {
                                return;
                            }
                            _ => {}
                        }
                    }
                }
            }
            AggTask::Array(element_type, len) => {
                let mut is_first = true;
                for _ in 0..len {
                    let allow = allow_array_designator && is_first;
                    self.consume_initializers(element_type, iter, allow);
                    is_first = false;

                    if iter.peek().is_none() {
                        return;
                    }
                    // Check stopper
                    if let Some(next) = iter.peek()
                        && let item_kind = *self.ast.get_kind(*next)
                        && let NodeKind::InitializerItem(next_init) = item_kind
                        && next_init.designator_len > 0
                    {
                        match *self.ast.get_kind(next_init.designator_start) {
                            NodeKind::Designator(Designator::ArrayIndex(_))
                            | NodeKind::Designator(Designator::ArrayRange(_, _)) => {
                                return;
                            }
                            _ => {}
                        }
                    }
                }
            }
            AggTask::Scalar => {
                // Scalar or Variable/Incomplete array. Consume 1 item for safety.
                iter.next();
            }
        }
    }
    fn extract_bit_field_width(&mut self, declarator: DeclaratorRef) -> Option<u16> {
        let declarator = self.parsed_ast.parsed_types.get_decl(declarator);
        match declarator {
            ParsedDeclarator::BitField { inner: _, width } => {
                let width_expr = self.visit_expression(*width);
                let span = self.ast.get_span(width_expr);

                match self.const_ctx().eval_int(width_expr) {
                    Some(val) if (0..=65535).contains(&val) => Some(val as u16),
                    Some(_) => {
                        self.report_error(span, SemanticError::InvalidBitfieldWidth);
                        None
                    }
                    None => {
                        self.report_error(span, SemanticError::NonConstantBitfieldWidth);
                        None
                    }
                }
            }
            ParsedDeclarator::Pointer { inner, .. } => self.extract_bit_field_width(*inner),
            ParsedDeclarator::Array { inner, .. } => self.extract_bit_field_width(*inner),
            ParsedDeclarator::Function { inner, .. } => self.extract_bit_field_width(*inner),
            ParsedDeclarator::Attribute { inner, .. } => self.extract_bit_field_width(*inner),
            _ => None,
        }
    }

    /// Recursively apply declarator to base type
    fn apply_declarator(
        &mut self,
        current_type: QualType,
        declarator: DeclaratorRef,
        span: SourceSpan,
        mut spec_info: Option<&mut DeclSpecInfo>,
        ctx: DeclaratorContext,
    ) -> QualType {
        let declarator = self.parsed_ast.parsed_types.get_decl(declarator);
        match declarator {
            ParsedDeclarator::Identifier(..) => current_type,
            ParsedDeclarator::Pointer { qualifiers, inner } => {
                let pointer_type = self.registry.pointer_to(current_type);
                let modified_current =
                    self.merge_qualifiers_with_check(QualType::unqualified(pointer_type), *qualifiers, span);
                self.apply_declarator(modified_current, *inner, span, spec_info, ctx)
            }
            ParsedDeclarator::Array { inner, size } => {
                if current_type.is_function() {
                    self.report_error(span, SemanticError::FunctionReturningFunction);
                }
                let array_qt = self.lower_array_declarator(*inner, size, current_type, span, ctx);
                self.apply_declarator(array_qt, *inner, span, spec_info, ctx)
            }
            ParsedDeclarator::Function { params, flags, inner } => {
                if current_type.is_array() {
                    self.report_error(span, SemanticError::FunctionReturningArray);
                }
                if current_type.is_function() {
                    self.report_error(span, SemanticError::FunctionReturningFunction);
                }

                if self.registry.get(current_type.ty()).kind == TypeKind::AutoType {
                    self.report_error(
                        span,
                        SemanticError::AutoTypeNotAllowed {
                            context: "function return type",
                        },
                    );
                }

                let params_list = self.parsed_ast.parsed_types.get_params(*params);
                let processed_params = self.visit_function_parameters(params_list, false);
                let is_noreturn = spec_info.as_ref().map(|s| s.is_noreturn).unwrap_or(false);
                let function_type =
                    self.registry
                        .function_type(current_type.ty(), processed_params, flags.is_variadic, is_noreturn);
                self.apply_declarator(QualType::unqualified(function_type), *inner, span, spec_info, ctx)
            }
            ParsedDeclarator::BitField { inner, .. } => {
                // Bit-fields don't affect the base type in the same way, we just recurse
                self.apply_declarator(current_type, *inner, span, spec_info, ctx)
            }
            ParsedDeclarator::Attribute { inner, spec } => {
                if let Some(info) = spec_info.as_mut() {
                    match spec {
                        DeclSpec::AttributeCleanup(expr) => info.cleanup_func = Some(*expr),
                        DeclSpec::AttributePacked => info.is_packed = true,
                        DeclSpec::AlignmentSpec(align, is_gnu) => {
                            info.alignment = self.resolve_alignment(align, span);
                            if *is_gnu {
                                info.is_gnu_aligned = true;
                            } else {
                                info.has_c11_alignment = true;
                            }
                        }
                        DeclSpec::FunctionSpec(FunctionSpec::Noreturn) => info.is_noreturn = true,
                        DeclSpec::FunctionSpec(FunctionSpec::Inline) => info.is_inline = true,
                        _ => {}
                    }
                }
                self.apply_declarator(current_type, *inner, span, spec_info, ctx)
            }
        }
    }

    fn resolve_record_tag(
        &mut self,
        tag: Option<NameId>,
        is_union: bool,
        is_definition: bool,
        span: SourceSpan,
    ) -> Result<TypeRef, SemanticDiag> {
        let (tag_name, existing) = if let Some(t) = tag {
            (t, self.symbol_table.lookup_tag(t))
        } else {
            (self.gen_anon_name(), None)
        };

        if let Some((sym_ref, scope_id)) = existing
            && (!is_definition || scope_id == self.symbol_table.current_scope())
        {
            let (ty, is_completed, def_span) = {
                let symbol = self.symbol_table.get_symbol(sym_ref);
                (symbol.type_info.ty(), symbol.is_completed, symbol.def_span)
            };

            if is_definition && is_completed {
                self.report_error(
                    span,
                    SemanticError::Redefinition {
                        name: tag_name,
                        first_def: def_span,
                    },
                );
            }
            // Store unique mapping for anonymous tags
            if tag.is_none() {
                self.type_to_tag_sym.insert(ty, sym_ref);
            }
            return Ok(ty);
        }
        let ty = self.registry.declare_record(tag, is_union);
        let sym = self.symbol_table.define_record(tag_name, ty, false, span);

        // Store unique mapping for anonymous tags and update side table with stable name
        if tag.is_none() {
            self.type_to_tag_sym.insert(ty, sym);
            self.ast.semantic_info.anonymous_tags.insert(ty, tag_name);
        }

        Ok(ty)
    }

    fn resolve_enum_tag(
        &mut self,
        tag: Option<NameId>,
        is_definition: bool,
        has_fixed: bool,
        // _fixed_base: Option<TypeRef>,
        span: SourceSpan,
    ) -> Result<TypeRef, SemanticDiag> {
        let (tag_name, existing) = if let Some(t) = tag {
            (t, self.symbol_table.lookup_tag(t))
        } else {
            (self.gen_anon_name(), None)
        };
        if let Some((sym_ref, scope_id)) = existing
            && (!is_definition || scope_id == self.symbol_table.current_scope())
        {
            let (ty, is_completed, def_span, has_enumerators) = {
                let symbol = self.symbol_table.get_symbol(sym_ref);
                let has_enums =
                    if let TypeKind::Enum { enumerators, .. } = &self.registry.get(symbol.type_info.ty()).kind {
                        !enumerators.is_empty()
                    } else {
                        false
                    };
                (symbol.type_info.ty(), symbol.is_completed, symbol.def_span, has_enums)
            };

            if is_definition && is_completed {
                // C23 allows redefinition only if it was empty or compatible
                let type_info = self.registry.get(ty);
                if let TypeKind::Enum {
                    has_fixed_underlying_type: existing_fixed,
                    ..
                } = &type_info.kind
                {
                    if !existing_fixed && !has_fixed {
                        self.report_error(
                            span,
                            SemanticError::Redefinition {
                                name: tag_name,
                                first_def: def_span,
                            },
                        );
                    } else if has_enumerators {
                        // C23: only one definition can have an enumerator list
                        self.report_error(
                            span,
                            SemanticError::Redefinition {
                                name: tag_name,
                                first_def: def_span,
                            },
                        );
                    }
                }
            }
            if !is_definition && !is_completed {
                self.report_warning(span, SemanticError::EnumForwardDeclaration);
            }

            // Store unique mapping for anonymous tags
            if tag.is_none() {
                self.type_to_tag_sym.insert(ty, sym_ref);
            }
            return Ok(ty);
        }

        if is_definition {
            let ty = self.registry.declare_enum(tag, self.registry.type_int, false);
            let sym = self.symbol_table.define_enum(tag_name, ty, span);
            // Store unique mapping for anonymous tags and update side table with stable name
            if tag.is_none() {
                self.type_to_tag_sym.insert(ty, sym);
                self.ast.semantic_info.anonymous_tags.insert(ty, tag_name);
            }
            Ok(ty)
        } else {
            // Forward declaration
            let ty = self.registry.declare_enum(tag, self.registry.type_int, false);
            let sym = self.symbol_table.define_enum(tag_name, ty, span);
            // Store unique mapping for anonymous tags and update side table with stable name
            if tag.is_none() {
                self.type_to_tag_sym.insert(ty, sym);
                self.ast.semantic_info.anonymous_tags.insert(ty, tag_name);
            }
            Ok(ty)
        }
    }

    fn complete_enum_symbol(
        &mut self,
        tag: Option<NameId>,
        ty: TypeRef,
        enumerators: Vec<EnumConstant>,
        base_type: Option<TypeRef>,
        has_fixed: bool,
        span: SourceSpan,
    ) -> Result<(), SemanticDiag> {
        // Determine the underlying type
        let base_type = base_type.unwrap_or_else(|| self.choose_enum_type(&enumerators));

        let (existing_fixed, existing_base, is_complete, has_enumerators) = {
            let type_info = self.registry.get(ty);
            if let TypeKind::Enum {
                has_fixed_underlying_type: existing_fixed1,
                base_type: existing_base1,
                is_complete: is_complete1,
                enumerators: existing_enumerators1,
                ..
            } = &type_info.kind
            {
                (
                    *existing_fixed1,
                    *existing_base1,
                    *is_complete1,
                    !existing_enumerators1.is_empty(),
                )
            } else {
                (false, self.registry.type_int, false, false)
            }
        };

        if existing_fixed
            && has_fixed
            && !self
                .registry
                .is_compatible(QualType::unqualified(existing_base), QualType::unqualified(base_type))
        {
            let _existing_str = self.registry.display_qual_type(QualType::unqualified(existing_base));
            let _new_str = self.registry.display_qual_type(QualType::unqualified(base_type));
            self.report_error(
                span,
                SemanticError::ConflictingTypes {
                    name: tag.unwrap_or_else(|| NameId::new("")), // Tag name could be missing if anonymous
                    first_def: span,                              // This is a bit lazy, should be first_def from symbol
                },
            );
        }

        if is_complete && !enumerators.is_empty() && has_enumerators {
            // Both have enumerators -> Redefinition
        }

        let enumerators = Arc::from(enumerators);

        // Update the type in AST and SymbolTable using the proper completion function
        self.registry
            .complete_enum(ty, Arc::clone(&enumerators), base_type, has_fixed);
        if let Err(e) = self.registry.ensure_layout(ty) {
            return Err(SemanticDiag::new(span, e.to_semantic_kind()));
        }

        if let Some(tag_name) = tag
            && let Some((entry, _)) = self.symbol_table.lookup_tag(tag_name)
        {
            let entry = self.symbol_table.get_symbol_mut(entry);
            entry.is_completed = true;
            if let SymbolKind::EnumTag { is_complete } = &mut entry.kind {
                *is_complete = true;
            }
        }
        Ok(())
    }

    fn complete_record_symbol(
        &mut self,
        tag: Option<NameId>,
        ty: TypeRef,
        members: Vec<RecordMember>,
        packing: Option<u32>,
        alignment: Option<u16>,
        span: SourceSpan,
    ) -> Result<(), SemanticDiag> {
        // Validation for name conflicts across anonymous members
        let mut seen_names = HashMap::new();
        let mut validation_errors = Vec::new();
        validate_record_members_helper(self.registry, &members, &mut seen_names, &mut validation_errors);
        for error in validation_errors {
            self.report_error(error.span, error.kind);
        }

        let final_packing = packing.or(self.current_packing.map(|n| n as u32));

        let members = Arc::from(members);

        // Update the type in AST and SymbolTable
        self.registry
            .complete_record(ty, Arc::clone(&members), final_packing, alignment);
        if let Err(e) = self.registry.ensure_layout(ty) {
            return Err(SemanticDiag::new(span, e.to_semantic_kind()));
        }

        if let Some(tag_name) = tag
            && let Some((entry, _)) = self.symbol_table.lookup_tag(tag_name)
        {
            let entry = self.symbol_table.get_symbol_mut(entry);
            entry.is_completed = true;
            if let SymbolKind::Record {
                is_complete,
                members: entry_members,
                ..
            } = &mut entry.kind
            {
                *is_complete = true;
                *entry_members = members;
            }
        }
        Ok(())
    }

    fn choose_enum_type(&self, enumerators: &[EnumConstant]) -> TypeRef {
        if enumerators.is_empty() {
            return self.registry.type_int;
        }

        let min = enumerators.iter().map(|e| e.value).min().unwrap_or(0);
        let max = enumerators.iter().map(|e| e.value).max().unwrap_or(0);

        let i32_min = i32::MIN as i64;
        let i32_max = i32::MAX as i64;
        let u32_max = u32::MAX as i64;

        if min >= i32_min && max <= i32_max {
            return self.registry.type_int;
        }

        if min >= 0 && max <= u32_max {
            return self.registry.type_int_unsigned;
        }

        // Must be in i64 or u64
        if min >= 0 {
            self.registry.type_long_long_unsigned
        } else {
            self.registry.type_long_long
        }
    }

    fn resolve_type_spec(&mut self, ts: &TypeSpec, span: SourceSpan) -> Result<QualType, SemanticDiag> {
        use TypeSpec::*;
        let ty = match ts {
            Atomic(p) => return self.resolve_atomic_specifier(*p, span),
            Record(u, t, d, a) => return self.resolve_record_specifier(*u, *t, d, a, span),
            Enum(t, e, u) => return self.resolve_enum_specifier(*t, e, *u, span),
            TypedefName(n) => return self.resolve_typedef_name(*n, span),
            TypeSpec::Typeof(ty) => return self.lower_typeof(*ty, span),
            TypeSpec::TypeofUnqual(ty) => return self.lower_typeof_unqual(*ty, span),
            TypeSpec::TypeofExpr(expr) => return Ok(self.lower_typeof_expr(*expr, span)),
            TypeSpec::TypeofUnqualExpr(expr) => return Ok(self.lower_typeof_unqual_expr(*expr)),

            Void => self.registry.type_void,
            Char => self.registry.type_char,
            Short => self.registry.type_short,
            Int => self.registry.type_int,
            Long => self.registry.type_long,
            LongLong => self.registry.type_long_long,
            UnsignedLong => self.registry.type_long_unsigned,
            UnsignedLongLong => self.registry.type_long_long_unsigned,
            UnsignedShort => self.registry.type_short_unsigned,
            UnsignedChar => self.registry.type_char_unsigned,
            SignedChar => self.registry.type_schar,
            SignedShort => self.registry.type_short,
            SignedLong => self.registry.type_long,
            SignedLongLong => self.registry.type_long_long,

            Float => self.registry.type_float,
            Double => self.registry.type_double,
            LongDouble => self.registry.type_long_double,
            ComplexFloat => self.registry.complex_type(self.registry.type_float),
            ComplexDouble => self.registry.complex_type(self.registry.type_double),
            ComplexLongDouble => self.registry.complex_type(self.registry.type_long_double),
            Signed => self.registry.type_signed,
            Unsigned => self.registry.type_int_unsigned,
            Bool => self.registry.type_bool,
            Complex => self.registry.type_complex_marker,
            VaList => self.registry.type_valist,
            AutoType => self.registry.auto_type(),
        };
        Ok(QualType::unqualified(ty))
    }

    fn merge_base_type(
        &mut self,
        existing: Option<QualType>,
        new_type: QualType,
        span: SourceSpan,
    ) -> Option<QualType> {
        let Some(existing) = existing else {
            return Some(new_type);
        };

        let existing_type = self.registry.get(existing.ty());
        let new_type_kind = &self.registry.get(new_type.ty()).kind;

        match (&existing_type.kind, new_type_kind) {
            (TypeKind::Builtin(e), TypeKind::Builtin(n)) => {
                let (&a, &b) = if (*e as u8) <= (*n as u8) { (e, n) } else { (n, e) };
                let ty = match (a, b) {
                    (x, y) if x == y => {
                        if x == BuiltinType::Long {
                            self.registry.type_long_long
                        } else {
                            existing.ty()
                        }
                    }
                    (BuiltinType::Char, BuiltinType::Signed) => self.registry.type_schar,
                    (x, BuiltinType::Signed) if x.is_integer() => self.registry.get_builtin_type(x),
                    (BuiltinType::Char, BuiltinType::UInt) => self.registry.type_char_unsigned,
                    (BuiltinType::Short, BuiltinType::UInt) => self.registry.type_short_unsigned,
                    (BuiltinType::Int, BuiltinType::UInt) => self.registry.type_int_unsigned,
                    (BuiltinType::UInt, BuiltinType::Long) => self.registry.type_long_unsigned,
                    (BuiltinType::UInt, BuiltinType::LongLong) => self.registry.type_long_long_unsigned,
                    (BuiltinType::UInt, BuiltinType::Signed) => self.registry.type_int_unsigned,
                    (BuiltinType::Short, BuiltinType::Int) => self.registry.type_short,
                    (BuiltinType::UShort, BuiltinType::Int) => self.registry.type_short_unsigned,
                    (BuiltinType::Int, BuiltinType::Long) => self.registry.type_long,
                    (BuiltinType::Int, BuiltinType::ULong) => self.registry.type_long_unsigned,
                    (BuiltinType::Int, BuiltinType::LongLong) => self.registry.type_long_long,
                    (BuiltinType::Int, BuiltinType::ULongLong) => self.registry.type_long_long_unsigned,
                    (BuiltinType::Long, BuiltinType::LongLong) => self.registry.type_long_long,
                    (BuiltinType::Long, BuiltinType::ULong) => self.registry.type_long_long_unsigned,
                    (BuiltinType::Long, BuiltinType::ULongLong) => self.registry.type_long_long_unsigned,
                    (BuiltinType::Long, BuiltinType::Double) => self.registry.type_long_double,
                    (BuiltinType::Float, BuiltinType::Complex) => self.registry.complex_type(self.registry.type_float),
                    (BuiltinType::Double, BuiltinType::Complex) => {
                        self.registry.complex_type(self.registry.type_double)
                    }
                    (BuiltinType::LongDouble, BuiltinType::Complex) => {
                        self.registry.complex_type(self.registry.type_long_double)
                    }
                    _ => {
                        self.report_error(span, SemanticError::ConflictingTypeSpec { prev: existing });
                        self.registry.type_error
                    }
                };
                Some(QualType::unqualified(ty))
            }
            _ => {
                self.report_error(span, SemanticError::ConflictingTypeSpec { prev: existing });
                Some(QualType::unqualified(self.registry.type_error))
            }
        }
    }

    fn validate_specifier_combinations(&mut self, info: &DeclSpecInfo, span: SourceSpan) {
        let storage_conflict = if info.is_typedef {
            info.storage.is_some_and(|s| s != StorageClass::Typedef) || info.is_thread_local || info.is_constexpr
        } else if info.is_thread_local {
            info.storage
                .is_some_and(|s| s != StorageClass::Static && s != StorageClass::Extern)
        } else if info.is_constexpr {
            info.storage
                .is_some_and(|s| s != StorageClass::Static && s != StorageClass::Auto && s != StorageClass::Register)
                || info.is_thread_local
        } else {
            false
        };

        if storage_conflict {
            self.report_error(span, SemanticError::ConflictingStorageClasses);
        }

        if info.is_typedef && info.has_auto {
            self.report_error(span, SemanticError::ConflictingStorageClasses);
        }

        if info.alignment.is_some() && info.storage == Some(StorageClass::Register) {
            self.report_error(
                span,
                SemanticError::AlignmentNotAllowed {
                    context: "register object",
                },
            );
        }

        if info.base_type.is_none() {
            self.report_error(span, SemanticError::MissingTypeSpec);
        }
    }

    fn get_definition_params(&mut self, declarator: DeclaratorRef) -> Option<Vec<FunctionParam>> {
        let declarator = self.parsed_ast.parsed_types.get_decl(declarator);
        match declarator {
            ParsedDeclarator::Function { inner, params, .. } => {
                if let Some(inner_params) = self.get_definition_params(*inner) {
                    Some(inner_params)
                } else {
                    let params_list = self.parsed_ast.parsed_types.get_params(*params);
                    Some(self.visit_function_parameters(params_list, true))
                }
            }
            ParsedDeclarator::Pointer { inner, .. } => self.get_definition_params(*inner),
            ParsedDeclarator::Array { inner, .. } => self.get_definition_params(*inner),
            ParsedDeclarator::BitField { inner, .. } => self.get_definition_params(*inner),
            _ => None,
        }
    }

    fn visit_decl_specs(&mut self, specs: &[DeclSpec], span: SourceSpan) -> DeclSpecInfo {
        let mut info = DeclSpecInfo::default();

        for spec in specs {
            match spec {
                DeclSpec::StorageClass(sc) => {
                    if *sc == StorageClass::ThreadLocal {
                        if info.is_thread_local {
                            self.report_error(span, SemanticError::ConflictingStorageClasses);
                        }
                        info.is_thread_local = true;
                    } else if *sc == StorageClass::Constexpr {
                        if info.is_constexpr {
                            self.report_error(span, SemanticError::ConflictingStorageClasses);
                        }
                        info.is_constexpr = true;
                    } else if *sc == StorageClass::Auto {
                        info.has_auto = true;
                        if self.lang_opts.c_standard < CStandard::C23 {
                            if info.storage.is_some() {
                                self.report_error(span, SemanticError::ConflictingStorageClasses);
                            }
                            info.storage = Some(StorageClass::Auto);
                        }
                    } else {
                        if info.storage.is_some() {
                            self.report_error(span, SemanticError::ConflictingStorageClasses);
                        }
                        info.storage = Some(*sc);
                        info.is_typedef |= *sc == StorageClass::Typedef;
                    }
                }
                DeclSpec::TypeQualifier(tq) => {
                    info.qualifiers.insert(TypeQualifiers::from_type_qualifier(*tq));
                }
                DeclSpec::TypeSpec(ts) => {
                    let ty = self.resolve_type_spec(ts, span).unwrap_or_else(|e| {
                        self.report_error(e.span, e.kind);
                        QualType::unqualified(self.registry.type_error)
                    });
                    info.base_type = self.merge_base_type(info.base_type, ty, span);
                }
                DeclSpec::AlignmentSpec(align, is_gnu) => {
                    if let Some(val) = self.resolve_alignment(align, span) {
                        info.alignment = Some(std::cmp::max(info.alignment.unwrap_or(0), val));
                    }
                    if *is_gnu {
                        info.is_gnu_aligned = true;
                    } else {
                        info.has_c11_alignment = true;
                    }
                }
                DeclSpec::FunctionSpec(fs) => match fs {
                    FunctionSpec::Inline => info.is_inline = true,
                    FunctionSpec::Noreturn => info.is_noreturn = true,
                },
                DeclSpec::Attribute => {}
                DeclSpec::AttributePacked => {
                    info.is_packed = true;
                }
                DeclSpec::AttributeCleanup(node_ref) => {
                    info.cleanup_func = Some(*node_ref);
                }
            }
        }

        if let Some(base) = info.base_type {
            let ty = base.ty();
            if ty == self.registry.type_signed {
                info.base_type = Some(QualType::unqualified(self.registry.type_int));
            } else if ty == self.registry.type_complex_marker {
                info.base_type = Some(QualType::unqualified(
                    self.registry.complex_type(self.registry.type_double),
                ));
            }
        } else if info.has_auto && self.lang_opts.c_standard >= CStandard::C23 {
            info.base_type = Some(QualType::unqualified(self.registry.auto_type()));
        }

        self.validate_specifier_combinations(&info, span);
        info
    }

    fn visit_function_parameters(&mut self, params: &[ParsedParam], is_definition: bool) -> Vec<FunctionParam> {
        let mut seen_names: HashMap<NameId, SourceSpan> = HashMap::new();
        let mut processed_params = Vec::with_capacity(params.len());

        for param in params {
            let base_type_node = self.parsed_ast.parsed_types.get_base_type(param.ty.base);
            if let ParsedBaseType::Builtin(TypeSpec::AutoType) = base_type_node {
                self.report_error(
                    param.span,
                    SemanticError::AutoTypeNotAllowed {
                        context: "function parameter",
                    },
                );
            }
        }

        // C11 6.2.1p4: Function prototype scope for declarations, block scope for definitions.
        // If it's not a definition, we push a temporary scope for these parameters.
        // If it is a definition, we assume the caller (visit_function_definition) has already pushed the scope.
        let old_in_prototype = self.in_prototype;
        self.in_prototype = !is_definition;

        let pushed_scope = if !is_definition || self.symbol_table.current_scope() == ScopeId::GLOBAL {
            self.symbol_table.push_scope();
            true
        } else {
            false
        };

        for param in params {
            let span = param.span;
            let decayed_qt = self
                .lower_type(param.ty, span, true)
                .unwrap_or_else(|_| QualType::unqualified(self.registry.type_error));

            let pname = param.name;

            // C11 6.7.6.3p4: "after adjustment, shall have complete object type."
            // C11 6.7.6.3p12: "If the function declarator is not part of a definition of that function,
            // parameters may have incomplete type..."
            // Bolt ⚡: Extension: allow incomplete enums in declarations (per GCC/Clang).
            if !self.registry.is_complete(decayed_qt.ty()) {
                let is_void_param_list = params.len() == 1 && decayed_qt.is_void() && pname.is_none();
                let is_incomplete_enum = matches!(self.registry.get(decayed_qt.ty()).kind, TypeKind::Enum { .. });

                let should_report = if decayed_qt.is_void() {
                    !is_void_param_list
                } else if is_incomplete_enum {
                    is_definition
                } else {
                    // For structs and other incomplete types, keep previous strictness (always error)
                    true
                };

                if should_report {
                    self.report_error(span, SemanticError::IncompleteType { ty: decayed_qt });
                }
            }

            if let Some(name) = pname {
                if let Some(&first_span) = seen_names.get(&name) {
                    self.report_error(
                        span,
                        SemanticError::Redefinition {
                            name,
                            first_def: first_span,
                        },
                    );
                } else {
                    seen_names.insert(name, span);

                    // Add parameter to symbol table so subsequent parameters can refer to it (e.g. for VLA sizes)
                    // If is_definition is true, visit_function_definition will call define_variable again,
                    // but we need them in scope NOW for type lowering.
                    // We use define_variable but since it's a parameter we don't need a full initializer.
                    let _ = self.symbol_table.define_variable(
                        name,
                        decayed_qt,
                        span,
                        Variable {
                            is_global: self.symbol_table.current_scope() == ScopeId::GLOBAL,
                            storage: param.storage,
                            is_thread_local: false,
                            initializer: None,
                            alignment: None,
                            cleanup_func: None,
                        },
                    );
                }
            }

            if let Some(sc) = param.storage {
                if sc == StorageClass::ThreadLocal {
                    self.report_error(span, SemanticError::ThreadLocalNotAllowed);
                } else if sc != StorageClass::Register {
                    self.report_error(span, SemanticError::InvalidStorageClassForParameter);
                }
            }

            if param.is_inline {
                self.report_error(span, SemanticError::InvalidFunctionSpec { spec: "inline" });
            }
            if param.is_noreturn {
                self.report_error(span, SemanticError::InvalidFunctionSpec { spec: "_Noreturn" });
            }

            if param.alignment.is_some() {
                self.report_error(
                    span,
                    SemanticError::AlignmentNotAllowed {
                        context: "function parameter",
                    },
                );
            }

            processed_params.push(FunctionParam {
                name: pname,
                param_type: decayed_qt,
                storage: param.storage,
            });
        }

        if pushed_scope {
            self.symbol_table.pop_scope();
        }

        self.in_prototype = old_in_prototype;

        processed_params
    }

    /// Common logic for lowering struct members, used by both TypeSpec::Record lowering
    /// and Declarator::AnonymousRecord handling.
    fn visit_record_members(
        &mut self,
        member_nodes: &[ParsedNodeRef],
        span: SourceSpan,
        is_union: bool,
    ) -> Vec<RecordMember> {
        let mut struct_members = Vec::new();

        for &node in member_nodes {
            let node = self.parsed_ast.get_node(node);
            match &node.kind {
                ParsedNodeKind::StaticAssert(cond, msg) => {
                    self.check_static_assert(*cond, *msg, node.span);
                }
                ParsedNodeKind::Declaration(decl) => {
                    self.visit_record_member_decl(decl, node.span, span, is_union, &mut struct_members);
                }
                ParsedNodeKind::PragmaPack(kind) => {
                    self.handle_pragma_pack(*kind);
                }
                _ => unreachable!(),
            }
        }
        struct_members
    }

    fn visit_record_member_decl(
        &mut self,
        decl: &ParsedDecl,
        node_span: SourceSpan,
        span: SourceSpan,
        is_union: bool,
        record_members: &mut Vec<RecordMember>,
    ) {
        let mut spec_info = self.visit_decl_specs(&decl.specifiers, span);

        if let Some(base) = spec_info.base_type
            && self.registry.get(base.ty()).kind == TypeKind::AutoType
        {
            self.report_error(
                node_span,
                SemanticError::AutoTypeNotAllowed {
                    context: "struct or union member",
                },
            );
        }

        if spec_info.storage.is_some() {
            self.report_error(span, SemanticError::ConflictingStorageClasses);
        }

        if decl.init_declarators.is_empty() {
            if let Some(base) = spec_info.base_type
                && let qt = self.merge_qualifiers_with_check(base, spec_info.qualifiers, span)
                && qt.is_record()
                && matches!(&self.registry.get(qt.ty()).kind, TypeKind::Record { tag: None, .. })
            {
                record_members.push(RecordMember {
                    member_type: qt,
                    alignment: spec_info.alignment,
                    is_packed: spec_info.is_packed,
                    span,
                    ..Default::default()
                });
            }
            return;
        }

        for id in &decl.init_declarators {
            if let Some(member) = self.lower_single_record_member(id, &mut spec_info, is_union) {
                record_members.push(member);
            }
        }
    }

    fn lower_single_record_member(
        &mut self,
        id: &ParsedInitDeclarator,
        spec_info: &mut DeclSpecInfo,
        is_union: bool,
    ) -> Option<RecordMember> {
        let bit_field_size = self.extract_bit_field_width(id.declarator);

        if bit_field_size.is_some() && spec_info.has_c11_alignment {
            self.report_error(id.span, SemanticError::AlignmentNotAllowed { context: "bit-field" });
        }

        self.check_function_specs(spec_info, id.span);

        let name = self.extract_name(id.declarator);
        if name.is_none() && bit_field_size.is_none() {
            self.report_error(id.span, SemanticError::EmptyDeclaration);
            return None;
        }

        let base = spec_info
            .base_type
            .unwrap_or_else(|| QualType::unqualified(self.registry.type_int));
        let qualified_base = self.merge_qualifiers_with_check(base, spec_info.qualifiers, id.span);

        let member_type = self.apply_declarator(
            qualified_base,
            id.declarator,
            id.span,
            Some(spec_info),
            DeclaratorContext { in_parameter: false },
        );

        self.validate_member_layout(
            member_type,
            bit_field_size,
            spec_info.alignment,
            name,
            id.span,
            is_union,
            spec_info.is_packed,
        );

        Some(RecordMember {
            name,
            member_type,
            bit_field_size,
            alignment: spec_info.alignment,
            is_packed: spec_info.is_packed,
            span: id.span,
        })
    }

    fn lower_record(
        &mut self,
        tag: Option<NameId>,
        members: Option<ParsedStructMemberRange>,
        is_union: bool,
        span: SourceSpan,
    ) -> Result<QualType, SemanticDiag> {
        let is_definition = members.is_some();
        let ty = self.resolve_record_tag(tag, is_union, is_definition, span)?;

        if let Some(members_range) = members {
            let parsed_members = self.parsed_ast.parsed_types.get_struct_members(members_range);
            let struct_members = parsed_members
                .iter()
                .map(|m| {
                    let member_type = self.lower_type(m.ty, span, false)?;
                    let bit_field_size = self.extract_bit_field_width(m.ty.declarator);
                    Ok(RecordMember {
                        name: m.name,
                        member_type,
                        bit_field_size,
                        alignment: m.alignment,
                        is_packed: m.is_packed,
                        span: m.span,
                    })
                })
                .collect::<Result<Vec<_>, SemanticDiag>>()?;

            self.complete_record_symbol(tag, ty, struct_members, None, None, span)?;
        }
        Ok(QualType::unqualified(ty))
    }

    fn lower_enum(
        &mut self,
        tag: Option<NameId>,
        enumerators: Option<ParsedEnumRange>,
        underlying_type: Option<ParsedType>,
        span: SourceSpan,
    ) -> Result<QualType, SemanticDiag> {
        let underlying_qt = if let Some(ut) = underlying_type {
            let qt = self.lower_type(ut, span, false)?;
            if !qt.is_integer() || qt.is_enum() {
                self.report_error(span, SemanticError::InvalidEnumUnderlyingType { ty: qt });
            }
            Some(qt)
        } else {
            None
        };

        let is_definition = enumerators.is_some() || underlying_qt.is_some();
        let ty = self.resolve_enum_tag(tag, is_definition, underlying_qt.is_some(), span)?;

        if let Some(enum_range) = enumerators {
            let parsed_enums = self.parsed_ast.parsed_types.get_enum_constants(enum_range);
            let mut next_value = 0i64;
            let mut enumerators_list = Vec::with_capacity(parsed_enums.len());

            for m in parsed_enums {
                let value = m.value.unwrap_or(next_value);
                let is_representable = if let Some(uqt) = underlying_qt {
                    self.registry.get(uqt.ty()).truncate_int(value) == value
                } else {
                    (i32::MIN as i64..=i32::MAX as i64).contains(&value)
                };

                if !is_representable {
                    let err = SemanticError::EnumeratorValueNotRepresentable {
                        name: m.name,
                        value,
                        target_ty: underlying_qt,
                    };
                    self.report_error(m.span, err);
                }
                next_value = value.wrapping_add(1);
                let _ = self.symbol_table.define_enum_constant(m.name, value, ty, m.span);
                enumerators_list.push(EnumConstant {
                    name: m.name,
                    value,
                    span: m.span,
                    init_expr: None,
                });
            }

            self.complete_enum_symbol(
                tag,
                ty,
                enumerators_list,
                underlying_qt.map(|q| q.ty()),
                underlying_qt.is_some(),
                span,
            )?;
        } else if let Some(uqt) = underlying_qt {
            // C23: definition with underlying type but no enumerators
            self.complete_enum_symbol(tag, ty, Vec::new(), Some(uqt.ty()), true, span)?;
        }
        Ok(QualType::unqualified(ty))
    }

    fn lower_typedef(&mut self, name: NameId, span: SourceSpan) -> Result<QualType, SemanticDiag> {
        match self
            .symbol_table
            .lookup_symbol(name)
            .map(|r| self.symbol_table.get_symbol(r))
        {
            Some(entry) => {
                if let SymbolKind::Typedef { aliased_type } = entry.kind {
                    Ok(aliased_type)
                } else {
                    Err(SemanticDiag::new(
                        span,
                        SemanticError::ExpectedTypedefName { found: name },
                    ))
                }
            }
            None => Ok(QualType::unqualified(self.registry.declare_record(Some(name), false))),
        }
    }

    fn lower_typeof(&mut self, ty: ParsedType, span: SourceSpan) -> Result<QualType, SemanticDiag> {
        self.report_warning(span, SemanticError::GnuTypeof);
        self.lower_type(ty, span, false)
    }

    fn lower_typeof_expr(&mut self, expr: ParsedNodeRef, span: SourceSpan) -> QualType {
        self.report_warning(span, SemanticError::GnuTypeof);
        let expr_node = self.visit_expression(expr);
        self.try_infer_type(expr_node)
            .unwrap_or_else(|| QualType::unqualified(self.registry.typeof_expr(expr_node)))
    }

    fn lower_typeof_unqual(&mut self, ty: ParsedType, span: SourceSpan) -> Result<QualType, SemanticDiag> {
        let qt = self.lower_type(ty, span, false)?;
        Ok(QualType::unqualified(qt.ty()))
    }

    fn lower_typeof_unqual_expr(&mut self, expr: ParsedNodeRef) -> QualType {
        let expr_node = self.visit_expression(expr);
        let ty = self
            .try_infer_type(expr_node)
            .map(|qt| qt.ty())
            .unwrap_or_else(|| self.registry.typeof_unqual_expr(expr_node));
        QualType::unqualified(ty)
    }

    /// Convert a ParsedBaseTypeNode to a QualType
    fn convert_to_qual_type(
        &mut self,
        parsed_base: &ParsedBaseType,
        span: SourceSpan,
    ) -> Result<QualType, SemanticDiag> {
        match parsed_base {
            ParsedBaseType::Builtin(ts) => self.resolve_type_spec(ts, span),
            ParsedBaseType::Record { tag, members, is_union } => self.lower_record(*tag, *members, *is_union, span),
            ParsedBaseType::Enum {
                tag,
                enumerators,
                underlying_type,
            } => self.lower_enum(*tag, *enumerators, *underlying_type, span),
            ParsedBaseType::Typedef(name) => self.lower_typedef(*name, span),
            ParsedBaseType::Typeof(ty) => self.lower_typeof(*ty, span),
            ParsedBaseType::TypeofExpr(expr) => Ok(self.lower_typeof_expr(*expr, span)),
            ParsedBaseType::TypeofUnqual(ty) => self.lower_typeof_unqual(*ty, span),
            ParsedBaseType::TypeofUnqualExpr(expr) => Ok(self.lower_typeof_unqual_expr(*expr)),
        }
    }
}

// Standalone helper to avoid borrow checker issues with LowerCtx
fn validate_record_members_helper(
    registry: &TypeRegistry,
    members: &[RecordMember],
    seen_names: &mut HashMap<NameId, SourceSpan>,
    errors: &mut Vec<SemanticDiag>,
) {
    for member in members {
        if let Some(name) = member.name {
            if let Some(&first_def) = seen_names.get(&name) {
                errors.push(SemanticDiag::new(
                    member.span,
                    SemanticError::DuplicateMember { name, first_def },
                ));
            } else {
                seen_names.insert(name, member.span);
            }
        } else if let TypeKind::Record {
            members: inner_members, ..
        } = &registry.get(member.member_type.ty()).kind
        {
            // Anonymous member, recurse
            validate_record_members_helper(registry, inner_members, seen_names, errors);
        }
    }
}
