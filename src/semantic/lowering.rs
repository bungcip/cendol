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

use crate::ast::literal;
use crate::ast::parsed::{
    ParsedDeclarationData, ParsedDeclarator, ParsedFunctionDefData, ParsedNodeKind, ParsedNodeRef, ParsedTypeSpecifier,
};
use crate::ast::*;
use crate::diagnostic::DiagnosticEngine;
use crate::semantic::const_eval::{self, ConstEvalCtx};
use crate::semantic::errors::{SemanticError, SemanticErrorKind};
use crate::semantic::symbol_table::{DefinitionState, SymbolTableError};
use crate::semantic::{
    ArraySizeType, BuiltinType, EnumConstant, ScopeId, StructMember, SymbolKind, SymbolRef, SymbolTable, TypeKind,
    TypeQualifiers, TypeRef, TypeRegistry,
};
use crate::semantic::{FunctionParameter, QualType};
use crate::source_manager::SourceSpan;
use std::sync::Arc;

#[derive(Clone, Copy)]
struct DeclaratorContext {
    in_parameter: bool,
}

/// Recursively apply parsed declarator to base type
fn apply_parsed_declarator(
    current_type: QualType,
    declarator: ParsedDeclRef,
    ctx: &mut LowerCtx,
    span: SourceSpan,
    decl_ctx: DeclaratorContext,
) -> QualType {
    let declarator_node = ctx.parsed_ast.parsed_types.get_decl(declarator);

    match declarator_node {
        ParsedDeclaratorNode::Identifier => current_type,
        ParsedDeclaratorNode::Pointer { qualifiers, inner } => {
            // Pointer
            // Apply Pointer modifier to the current type first (Top-Down)
            let pointer_type = ctx.registry.pointer_to(current_type);
            // Pointer type is always compatible with restrict, but we use checked merge anyway for consistency
            let modified_current =
                ctx.merge_qualifiers_with_check(QualType::unqualified(pointer_type), qualifiers, span);
            apply_parsed_declarator(modified_current, inner, ctx, span, decl_ctx)
        }
        ParsedDeclaratorNode::Array { size, inner } => {
            // Array
            // Apply Array modifier to the current type
            // Propagate qualifiers from the element type to the array type (C11 6.7.3)

            // C11 6.7.6.2p1: qualifiers and static in array declarator only allowed in function parameters
            // and only in the outermost array type derivation.
            let has_quals = match &size {
                ParsedArraySize::Expression { qualifiers, .. } => !qualifiers.is_empty(),
                ParsedArraySize::Star { qualifiers } => !qualifiers.is_empty(),
                ParsedArraySize::VlaSpecifier { qualifiers, .. } => !qualifiers.is_empty(),
                ParsedArraySize::Incomplete => false,
            };
            let has_static = matches!(size, ParsedArraySize::VlaSpecifier { is_static: true, .. });

            if has_static || has_quals {
                let inner_node = ctx.parsed_ast.parsed_types.get_decl(inner);
                let is_outermost = matches!(inner_node, ParsedDeclaratorNode::Identifier);

                if !decl_ctx.in_parameter {
                    if has_static {
                        ctx.report_error(span, SemanticErrorKind::ArrayStaticOutsideParameter);
                    }
                    if has_quals {
                        ctx.report_error(span, SemanticErrorKind::ArrayQualifierOutsideParameter);
                    }
                } else if !is_outermost {
                    if has_static {
                        ctx.report_error(span, SemanticErrorKind::ArrayStaticNotOutermost);
                    }
                    if has_quals {
                        ctx.report_error(span, SemanticErrorKind::ArrayQualifierNotOutermost);
                    }
                }
            }

            let array_size = convert_parsed_array_size(&size, ctx);
            let array_type = ctx.registry.array_of(current_type.ty(), array_size);
            let qualified_array = QualType::unqualified(array_type).merge_qualifiers(current_type.qualifiers());
            apply_parsed_declarator(qualified_array, inner, ctx, span, decl_ctx)
        }
        ParsedDeclaratorNode::Function { params, flags, inner } => {
            // Function
            // Process parameters separately
            let parsed_params: Vec<_> = ctx.parsed_ast.parsed_types.get_params(params).to_vec();
            let mut processed_params = Vec::new();
            for param in parsed_params {
                let param_type = convert_to_qual_type(ctx, param.ty, param.span, true).unwrap_or_else(|_| {
                    // Create an error type if conversion fails
                    QualType::unqualified(ctx.registry.type_int)
                });

                // Apply array-to-pointer decay for function parameters
                let ptr_quals = extract_array_param_qualifiers_from_ref(param.ty.declarator, ctx);
                let decayed_param_type = ctx.registry.decay(param_type, ptr_quals);

                processed_params.push(FunctionParameter {
                    param_type: decayed_param_type,
                    name: param.name,
                    storage: None,
                });
            }

            // Apply Function modifier to the current type
            let function_type = ctx.registry.function_type(
                current_type.ty(),
                processed_params,
                flags.is_variadic,
                false, // `_Noreturn` is a specifier, not part of declarator
            );
            apply_parsed_declarator(QualType::unqualified(function_type), inner, ctx, span, decl_ctx)
        }
    }
}

fn extract_array_param_qualifiers_from_ref(decl: ParsedDeclRef, ctx: &LowerCtx) -> TypeQualifiers {
    let decl = ctx.parsed_ast.parsed_types.get_decl(decl);
    match decl {
        ParsedDeclaratorNode::Identifier => TypeQualifiers::empty(),
        ParsedDeclaratorNode::Pointer { .. } => TypeQualifiers::empty(),
        ParsedDeclaratorNode::Function { .. } => TypeQualifiers::empty(),
        ParsedDeclaratorNode::Array { size, inner } => {
            let inner_quals = extract_array_param_qualifiers_from_ref(inner, ctx);
            if !inner_quals.is_empty() {
                return inner_quals;
            }
            match size {
                ParsedArraySize::Expression { qualifiers, .. } => qualifiers,
                ParsedArraySize::Star { qualifiers } => qualifiers,
                ParsedArraySize::VlaSpecifier { qualifiers, .. } => qualifiers,
                ParsedArraySize::Incomplete => TypeQualifiers::empty(),
            }
        }
    }
}

fn extract_array_param_qualifiers(decl: &ParsedDeclarator) -> TypeQualifiers {
    match decl {
        ParsedDeclarator::Identifier(..) | ParsedDeclarator::Abstract => TypeQualifiers::empty(),
        ParsedDeclarator::Pointer(..) => TypeQualifiers::empty(),
        ParsedDeclarator::Array(inner, size) => {
            let inner_quals = extract_array_param_qualifiers(inner);
            if !inner_quals.is_empty() {
                return inner_quals;
            }
            match size {
                ParsedArraySize::Expression { qualifiers, .. } => *qualifiers,
                ParsedArraySize::Star { qualifiers } => *qualifiers,
                ParsedArraySize::VlaSpecifier { qualifiers, .. } => *qualifiers,
                ParsedArraySize::Incomplete => TypeQualifiers::empty(),
            }
        }
        ParsedDeclarator::Function { .. } => TypeQualifiers::empty(),
        ParsedDeclarator::BitField(inner, _) => extract_array_param_qualifiers(inner),
    }
}

/// Convert ParsedArraySize to ArraySizeType
fn convert_parsed_array_size(size: &ParsedArraySize, ctx: &mut LowerCtx) -> ArraySizeType {
    match size {
        ParsedArraySize::Expression { expr, .. } => resolve_array_size(Some(*expr), ctx),
        ParsedArraySize::Star { .. } => ArraySizeType::Star,
        ParsedArraySize::Incomplete => ArraySizeType::Incomplete,
        ParsedArraySize::VlaSpecifier { size, .. } => resolve_array_size(*size, ctx),
    }
}

/// Helper function to resolve array size logic
fn resolve_array_size(size: Option<ParsedNodeRef>, ctx: &mut LowerCtx) -> ArraySizeType {
    if let Some(node) = size {
        let expr = ctx.visit_expression(node);
        if let Some(val) = const_eval::eval_const_expr(&ctx.const_ctx(), expr) {
            if val < 0 {
                ctx.report_error(ctx.ast.get_span(expr), SemanticErrorKind::InvalidArraySize);
                return ArraySizeType::Incomplete;
            }
            return ArraySizeType::Constant(val as usize);
        } else {
            // For now, we only support constant sizes (VLA support is future)
            // Or maybe we should return Variable(expr_ref) and let ensure_layout fail?
            // But verify what Variable does.
            // ensure_layout returns "incomplete/VLA array layout" error.
            return ArraySizeType::Variable(expr);
        }
    }
    ArraySizeType::Incomplete
}

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
}

impl<'a, 'src> LowerCtx<'a, 'src> {
    /// Create a new lowering context
    pub(crate) fn new(
        parsed_ast: &'a ParsedAst,
        ast: &'a mut Ast,
        diag: &'src mut DiagnosticEngine,
        symbol_table: &'a mut SymbolTable,
        registry: &'a mut TypeRegistry,
    ) -> Self {
        Self {
            parsed_ast,
            ast,
            diag,
            symbol_table,
            registry,
            next_compound_uses_scope: None,
        }
    }

    /// Report a semantic error and mark context as having errors
    /// Report a semantic error
    pub(crate) fn report_error(&mut self, span: SourceSpan, kind: SemanticErrorKind) {
        let error = SemanticError { span, kind };
        for diag in error.into_diagnostic(self.registry) {
            self.diag.report_diagnostic(diag);
        }
    }

    fn check_function_specifiers(&mut self, info: &DeclSpecInfo, span: SourceSpan) {
        if info.is_inline {
            self.report_error(span, SemanticErrorKind::InvalidFunctionSpecifier { spec: "inline" });
        }
        if info.is_noreturn {
            self.report_error(span, SemanticErrorKind::InvalidFunctionSpecifier { spec: "_Noreturn" });
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
                self.report_error(span, SemanticErrorKind::InvalidRestrict);
            }
        }
        if add.contains(TypeQualifiers::ATOMIC) {
            if base.is_array() {
                self.report_error(span, SemanticErrorKind::InvalidAtomicQualifier { type_kind: "array" });
            } else if base.is_function() {
                self.report_error(
                    span,
                    SemanticErrorKind::InvalidAtomicQualifier { type_kind: "function" },
                );
            } else if base.is_void() {
                self.report_error(span, SemanticErrorKind::InvalidAtomicQualifier { type_kind: "void" });
            }
        }
        base.merge_qualifiers(add)
    }

    fn check_static_assert(&mut self, cond: ParsedNodeRef, msg: ParsedNodeRef, span: SourceSpan) {
        let cond_node = self.visit_expression(cond);
        let msg_node = self.visit_expression(msg);

        if let Some(cond_ty) = self.ast.get_resolved_type(cond_node)
            && !cond_ty.is_integer()
        {
            // The condition of _Static_assert must be an integer constant expression.
            // Wait, an integer constant expression is one that has integer type.
            // If the type is not integer, we report error, but we still try to evaluate it for better diagnostics.
            self.report_error(span, SemanticErrorKind::ExpectedIntegerType { found: cond_ty });
        }

        let const_ctx = self.const_ctx();
        match const_eval::eval_const_expr(&const_ctx, cond_node) {
            Some(0) => {
                let message = match self.ast.get_kind(msg_node) {
                    NodeKind::Literal(literal::Literal::String(s)) => s.as_str().to_string(),
                    _ => String::new(),
                };

                self.report_error(span, SemanticErrorKind::StaticAssertFailed { message });
            }
            None => self.report_error(span, SemanticErrorKind::StaticAssertNotConstant),
            _ => {}
        }
    }

    fn validate_member_layout(
        &mut self,
        member_type: QualType,
        bit_field_size: Option<u16>,
        alignment: Option<u32>,
        name: Option<NameId>,
        span: SourceSpan,
    ) {
        if let Some(width) = bit_field_size {
            if !member_type.is_integer() {
                self.report_error(span, SemanticErrorKind::InvalidBitfieldType { ty: member_type });
            } else if member_type.qualifiers().contains(TypeQualifiers::ATOMIC) {
                self.report_error(span, SemanticErrorKind::BitfieldHasAtomicType);
            } else if let Ok(layout) = self.registry.ensure_layout(member_type.ty()) {
                let type_width = layout.size * 8;
                if (width as u64) > type_width {
                    self.report_error(span, SemanticErrorKind::BitfieldWidthExceedsType { width, type_width });
                }
            }
            if width == 0 && name.is_some() {
                self.report_error(span, SemanticErrorKind::NamedZeroWidthBitfield);
            }
        } else if let Ok(layout) = self.registry.ensure_layout(member_type.ty())
            && let Some(req_align) = alignment
        {
            let natural_align = layout.alignment as u32;
            if req_align < natural_align {
                self.report_error(
                    span,
                    SemanticErrorKind::AlignmentTooLoose {
                        requested: req_align,
                        natural: natural_align,
                    },
                );
            }
        }
    }

    fn resolve_alignment(&mut self, align: &ParsedAlignmentSpecifier, span: SourceSpan) -> Option<u32> {
        match align {
            ParsedAlignmentSpecifier::Type(parsed_ty) => {
                let qt = convert_to_qual_type(self, *parsed_ty, span, false)
                    .unwrap_or(QualType::unqualified(self.registry.type_error));
                match self.registry.ensure_layout(qt.ty()) {
                    Ok(layout) => Some(layout.alignment as u32),
                    Err(e) => {
                        self.report_error(span, e.to_semantic_kind());
                        None
                    }
                }
            }
            ParsedAlignmentSpecifier::Expr(expr) => {
                let lowered_expr = self.visit_expression(*expr);
                let const_ctx = self.const_ctx();
                if let Some(val) = const_eval::eval_const_expr(&const_ctx, lowered_expr) {
                    if val > 0 && (val as u64).is_power_of_two() {
                        Some(val as u32)
                    } else if val == 0 {
                        None
                    } else {
                        self.report_error(span, SemanticErrorKind::InvalidAlignment { value: val });
                        None
                    }
                } else {
                    self.report_error(span, SemanticErrorKind::NonConstantAlignment);
                    None
                }
            }
        }
    }

    fn lower_array_declarator(
        &mut self,
        base: &ParsedDeclarator,
        size: &ParsedArraySize,
        element_ty: QualType,
        span: SourceSpan,
        decl_ctx: DeclaratorContext,
    ) -> QualType {
        // C11 6.7.6.2 Array declarators
        if !self.registry.is_complete(element_ty.ty()) || element_ty.ty().is_function() {
            self.report_error(span, SemanticErrorKind::IncompleteType { ty: element_ty });
        }

        let (has_static, quals) = match size {
            ParsedArraySize::Expression { qualifiers, .. } => (false, qualifiers),
            ParsedArraySize::Star { qualifiers } => (false, qualifiers),
            ParsedArraySize::VlaSpecifier {
                is_static, qualifiers, ..
            } => (*is_static, qualifiers),
            ParsedArraySize::Incomplete => (false, &TypeQualifiers::empty()),
        };

        if has_static || !quals.is_empty() {
            let is_outermost = matches!(base, ParsedDeclarator::Identifier(..) | ParsedDeclarator::Abstract);

            if !decl_ctx.in_parameter {
                if has_static {
                    self.report_error(span, SemanticErrorKind::ArrayStaticOutsideParameter);
                }
                if !quals.is_empty() {
                    self.report_error(span, SemanticErrorKind::ArrayQualifierOutsideParameter);
                }
            } else if !is_outermost {
                if has_static {
                    self.report_error(span, SemanticErrorKind::ArrayStaticNotOutermost);
                }
                if !quals.is_empty() {
                    self.report_error(span, SemanticErrorKind::ArrayQualifierNotOutermost);
                }
            }
        }

        let array_size = match size {
            ParsedArraySize::Expression { expr, .. } => resolve_array_size(Some(*expr), self),
            ParsedArraySize::Star { .. } => ArraySizeType::Star,
            ParsedArraySize::Incomplete => ArraySizeType::Incomplete,
            ParsedArraySize::VlaSpecifier { size, .. } => resolve_array_size(*size, self),
        };

        let ty = self.registry.array_of(element_ty.ty(), array_size);
        QualType::new(ty, element_ty.qualifiers())
    }

    fn resolve_atomic_specifier(
        &mut self,
        parsed_type: ParsedType,
        span: SourceSpan,
    ) -> Result<QualType, SemanticError> {
        let qt = convert_to_qual_type(self, parsed_type, span, false)?;

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
            self.report_error(span, SemanticErrorKind::InvalidAtomicSpecifier { reason });
        }

        Ok(qt.merge_qualifiers(TypeQualifiers::ATOMIC))
    }

    fn resolve_record_specifier(
        &mut self,
        is_union: bool,
        tag: Option<NameId>,
        definition: &Option<ParsedRecordDefData>,
        span: SourceSpan,
    ) -> Result<QualType, SemanticError> {
        let is_definition = definition.is_some();
        let ty = resolve_record_tag(self, tag, is_union, is_definition, span)?;

        if let Some(def) = definition {
            let members = def
                .members
                .as_ref()
                .map(|decls| visit_struct_members(decls, self, span))
                .unwrap_or_default();
            complete_record_symbol(self, tag, ty, members, span)?;
        }

        Ok(QualType::unqualified(ty))
    }

    fn resolve_enum_specifier(
        &mut self,
        tag: Option<NameId>,
        enumerators: &Option<Vec<ParsedNodeRef>>,
        span: SourceSpan,
    ) -> Result<QualType, SemanticError> {
        let is_definition = enumerators.is_some();
        let ty = resolve_enum_tag(self, tag, is_definition, span)?;

        if let Some(enums) = enumerators {
            let mut next_value = 0i64;
            let mut enumerators_list = Vec::with_capacity(enums.len());

            for &enum_ref in enums {
                let node = self.parsed_ast.get_node(enum_ref);
                let ParsedNodeKind::EnumConstant(name, value_expr) = &node.kind else {
                    unreachable!()
                };

                let (value, init_expr) = value_expr
                    .map(|v| {
                        let expr = self.visit_expression(v);
                        let val = const_eval::eval_const_expr(&self.const_ctx(), expr).unwrap_or_else(|| {
                            self.report_error(node.span, SemanticErrorKind::NonConstantInitializer);
                            0
                        });
                        (val, Some(expr))
                    })
                    .unwrap_or((next_value, None));

                if !(i32::MIN as i64..=i32::MAX as i64).contains(&value) {
                    self.report_error(
                        node.span,
                        SemanticErrorKind::EnumeratorValueNotRepresentable { name: *name, value },
                    );
                }

                next_value = value.wrapping_add(1);

                if let Err(SymbolTableError::InvalidRedefinition { existing, .. }) =
                    self.symbol_table.define_enum_constant(*name, value, ty, node.span)
                {
                    let first_def = self.symbol_table.get_symbol(existing).def_span;
                    self.report_error(node.span, SemanticErrorKind::Redefinition { name: *name, first_def });
                }

                enumerators_list.push(EnumConstant {
                    name: *name,
                    value,
                    span: node.span,
                    init_expr,
                });
            }

            complete_enum_symbol(self, tag, ty, enumerators_list, span)?;
        }
        Ok(QualType::unqualified(ty))
    }

    fn resolve_typedef_name(&mut self, name: NameId, span: SourceSpan) -> Result<QualType, SemanticError> {
        match self
            .symbol_table
            .lookup_symbol(name)
            .map(|(r, _)| self.symbol_table.get_symbol(r))
        {
            Some(entry) => {
                if let SymbolKind::Typedef { aliased_type } = entry.kind {
                    Ok(aliased_type)
                } else {
                    Err(SemanticError {
                        span,
                        kind: SemanticErrorKind::ExpectedTypedefName { found: name },
                    })
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
            self.ast.spans[target.index()] = span;
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
            semantic_info: None,
        }
    }
}

/// Information about declaration specifiers after processing
#[derive(Debug, Clone, Default)]
pub(crate) struct DeclSpecInfo {
    pub(crate) storage: Option<StorageClass>,
    pub(crate) is_thread_local: bool,
    pub(crate) qualifiers: TypeQualifiers,
    pub(crate) base_type: Option<QualType>,
    pub(crate) is_typedef: bool,
    pub(crate) is_inline: bool,
    pub(crate) is_noreturn: bool,
    pub(crate) alignment: Option<u32>,
}

/// Convert a ParsedBaseTypeNode to a QualType
fn convert_parsed_base_type_to_qual_type(
    ctx: &mut LowerCtx,
    parsed_base: &ParsedBaseTypeNode,
    span: SourceSpan,
) -> Result<QualType, SemanticError> {
    match parsed_base {
        ParsedBaseTypeNode::Builtin(ts) => resolve_type_specifier(ts, ctx, span),
        ParsedBaseTypeNode::Record { tag, members, is_union } => {
            let is_definition = members.is_some();
            let ty = resolve_record_tag(ctx, *tag, *is_union, is_definition, span)?;

            if let Some(members_range) = members {
                let parsed_members = ctx.parsed_ast.parsed_types.get_struct_members(*members_range).to_vec();
                let struct_members = parsed_members
                    .into_iter()
                    .map(|m| {
                        Ok(StructMember {
                            name: m.name,
                            member_type: convert_to_qual_type(ctx, m.ty, span, false)?,
                            bit_field_size: m.bit_field_size,
                            alignment: m.alignment,
                            span: m.span,
                        })
                    })
                    .collect::<Result<Vec<_>, SemanticError>>()?;

                complete_record_symbol(ctx, *tag, ty, struct_members, span)?;
            }
            Ok(QualType::unqualified(ty))
        }
        ParsedBaseTypeNode::Enum { tag, enumerators } => {
            let is_definition = enumerators.is_some();
            let ty = resolve_enum_tag(ctx, *tag, is_definition, span)?;

            if let Some(enum_range) = enumerators {
                let parsed_enums = ctx.parsed_ast.parsed_types.get_enum_constants(*enum_range).to_vec();
                let mut next_value = 0i64;
                let enumerators_list = parsed_enums
                    .into_iter()
                    .map(|m| {
                        let value = m.value.unwrap_or(next_value);
                        if !(i32::MIN as i64..=i32::MAX as i64).contains(&value) {
                            ctx.report_error(
                                m.span,
                                SemanticErrorKind::EnumeratorValueNotRepresentable { name: m.name, value },
                            );
                        }
                        next_value = value.wrapping_add(1);
                        let _ = ctx.symbol_table.define_enum_constant(m.name, value, ty, m.span);
                        Ok(EnumConstant {
                            name: m.name,
                            value,
                            span: m.span,
                            init_expr: None,
                        })
                    })
                    .collect::<Result<Vec<_>, SemanticError>>()?;

                complete_enum_symbol(ctx, *tag, ty, enumerators_list, span)?;
            }
            Ok(QualType::unqualified(ty))
        }
        ParsedBaseTypeNode::Typedef(name) => {
            match ctx
                .symbol_table
                .lookup_symbol(*name)
                .map(|(r, _)| ctx.symbol_table.get_symbol(r))
            {
                Some(entry) => {
                    if let SymbolKind::Typedef { aliased_type } = entry.kind {
                        Ok(aliased_type)
                    } else {
                        Err(SemanticError {
                            span,
                            kind: SemanticErrorKind::ExpectedTypedefName { found: *name },
                        })
                    }
                }
                None => Ok(QualType::unqualified(ctx.registry.declare_record(Some(*name), false))),
            }
        }
        ParsedBaseTypeNode::Typeof(ty) => convert_to_qual_type(ctx, *ty, span, false),
        ParsedBaseTypeNode::TypeofExpr(expr) => {
            let expr_node = ctx.visit_expression(*expr);
            let tr = ctx
                .registry
                .alloc(crate::semantic::Type::new(crate::semantic::TypeKind::TypeofExpr(
                    expr_node,
                )));
            Ok(QualType::unqualified(tr))
        }
    }
}

/// Convert a ParsedType to a TypeRef
fn convert_to_qual_type(
    ctx: &mut LowerCtx,
    parsed_type: ParsedType,
    span: SourceSpan,
    in_parameter: bool,
) -> Result<QualType, SemanticError> {
    let base_type_node = {
        let parsed_types = &ctx.parsed_ast.parsed_types;
        parsed_types.get_base_type(parsed_type.base)
    };

    let declarator = parsed_type.declarator;
    let qualifiers = parsed_type.qualifiers;

    let base = convert_parsed_base_type_to_qual_type(ctx, &base_type_node, span)?;
    let qbase = ctx.merge_qualifiers_with_check(base, qualifiers, span);

    let final_type = apply_parsed_declarator(qbase, declarator, ctx, span, DeclaratorContext { in_parameter });
    Ok(final_type)
}

/// Helper to resolve struct/union tags (lookup, forward decl, or definition validation)
fn resolve_record_tag(
    ctx: &mut LowerCtx,
    tag: Option<NameId>,
    is_union: bool,
    is_definition: bool,
    span: SourceSpan,
) -> Result<TypeRef, SemanticError> {
    let Some(tag_name) = tag else {
        return Ok(ctx.registry.declare_record(None, is_union));
    };

    let existing = ctx.symbol_table.lookup_tag(tag_name);

    if let Some((entry, scope_id)) = existing
        && (!is_definition || scope_id == ctx.symbol_table.current_scope())
    {
        let entry = ctx.symbol_table.get_symbol(entry);
        let type_info = entry.type_info;
        let is_completed = entry.is_completed;
        let def_span = entry.def_span;

        if is_definition && is_completed {
            ctx.report_error(
                span,
                SemanticErrorKind::Redefinition {
                    name: tag_name,
                    first_def: def_span,
                },
            );
        }
        Ok(type_info.ty())
    } else {
        let ty = ctx.registry.declare_record(Some(tag_name), is_union);
        ctx.symbol_table.define_record(tag_name, ty, false, span);
        Ok(ty)
    }
}

/// Helper to resolve enum tags
fn resolve_enum_tag(
    ctx: &mut LowerCtx,
    tag: Option<NameId>,
    is_definition: bool,
    span: SourceSpan,
) -> Result<TypeRef, SemanticError> {
    let Some(tag_name) = tag else {
        return Ok(ctx.registry.declare_enum(None, ctx.registry.type_int));
    };

    let existing = ctx.symbol_table.lookup_tag(tag_name);

    if let Some((sym, scope_id)) = existing
        && (!is_definition || scope_id == ctx.symbol_table.current_scope())
    {
        let symbol = ctx.symbol_table.get_symbol(sym);
        let type_info = symbol.type_info;
        let is_completed = symbol.is_completed;
        let def_span = symbol.def_span;

        if is_definition && is_completed {
            ctx.report_error(
                span,
                SemanticErrorKind::Redefinition {
                    name: tag_name,
                    first_def: def_span,
                },
            );
        }
        Ok(type_info.ty())
    } else {
        let ty = ctx.registry.declare_enum(Some(tag_name), ctx.registry.type_int);
        ctx.symbol_table.define_enum(tag_name, ty, span);
        Ok(ty)
    }
}

/// Recursively validates that there are no duplicate member names, descending into anonymous records.
///
/// ⚡ Bolt: This function is optimized to avoid heap allocations.
/// Instead of taking a mutable `LowerCtx` and cloning member lists to satisfy the
/// borrow checker, it now takes an immutable `&TypeRegistry` and returns a `Vec`
/// of diagnostics. This avoids expensive `members.clone()` operations, especially
/// in deeply nested anonymous structs/unions.
fn validate_record_members(
    registry: &TypeRegistry,
    members: &[StructMember],
    seen_names: &mut HashMap<NameId, SourceSpan>,
) -> Vec<SemanticError> {
    let mut errors = Vec::new();

    for member in members {
        if let Some(name) = member.name {
            if let Some(&first_def) = seen_names.get(&name) {
                errors.push(SemanticError {
                    span: member.span,
                    kind: SemanticErrorKind::DuplicateMember { name, first_def },
                });
            } else {
                seen_names.insert(name, member.span);
            }
        } else if let TypeKind::Record {
            members: inner_members, ..
        } = &registry.get(member.member_type.ty()).kind
        {
            // Anonymous member, recurse
            errors.extend(validate_record_members(registry, inner_members, seen_names));
        }
    }
    errors
}

fn complete_record_symbol(
    ctx: &mut LowerCtx,
    tag: Option<NameId>,
    ty: TypeRef,
    members: Vec<StructMember>,
    span: SourceSpan,
) -> Result<(), SemanticError> {
    // New: Validate for name conflicts across anonymous members
    let mut seen_names = HashMap::new();
    let validation_errors = validate_record_members(ctx.registry, &members, &mut seen_names);
    for error in validation_errors {
        ctx.report_error(error.span, error.kind);
    }

    // Update the type in AST and SymbolTable
    ctx.registry.complete_record(ty, members.clone());
    if let Err(e) = ctx.registry.ensure_layout(ty) {
        return Err(SemanticError {
            span,
            kind: e.to_semantic_kind(),
        });
    }

    if let Some(tag_name) = tag
        && let Some((entry, _)) = ctx.symbol_table.lookup_tag(tag_name)
    {
        let entry = ctx.symbol_table.get_symbol_mut(entry);
        entry.is_completed = true;
        if let SymbolKind::Record {
            is_complete,
            members: entry_members,
            ..
        } = &mut entry.kind
        {
            *is_complete = true;
            *entry_members = Arc::from(members); // This is now the original value
        }
    }
    Ok(())
}

fn choose_enum_type(registry: &TypeRegistry, enumerators: &[EnumConstant]) -> TypeRef {
    if enumerators.is_empty() {
        return registry.type_int;
    }

    let min = enumerators.iter().map(|e| e.value).min().unwrap_or(0);
    let max = enumerators.iter().map(|e| e.value).max().unwrap_or(0);

    // C11 6.7.2.2p4:
    // Each enumerated type shall be compatible with char, a signed integer type, or an unsigned integer type.
    // The choice of type is implementation-defined...

    const UINT_MAX: i64 = u32::MAX as i64;
    const INT_MAX: i64 = i32::MAX as i64;
    const INT_MIN: i64 = i32::MIN as i64;

    // We prioritize unsigned int if all values are non-negative and fit.
    // This helps with strict pointer compatibility checks against unsigned int *.
    if min >= 0 && max <= UINT_MAX {
        return registry.type_int_unsigned;
    }

    // Default to int if it fits (or if min < 0)
    if min >= INT_MIN && max <= INT_MAX {
        return registry.type_int;
    }

    // For larger values, fallback to long long
    if min >= 0 {
        return registry.type_long_long_unsigned;
    }

    registry.type_long_long
}

fn complete_enum_symbol(
    ctx: &mut LowerCtx,
    tag: Option<NameId>,
    ty: TypeRef,
    enumerators: Vec<EnumConstant>,
    span: SourceSpan,
) -> Result<(), SemanticError> {
    // Determine the underlying type
    let base_type = choose_enum_type(ctx.registry, &enumerators);

    // Update the type in AST and SymbolTable using the proper completion function
    ctx.registry.complete_enum(ty, enumerators, base_type);
    if let Err(e) = ctx.registry.ensure_layout(ty) {
        return Err(SemanticError {
            span,
            kind: e.to_semantic_kind(),
        });
    }

    if let Some(tag_name) = tag
        && let Some((entry, _)) = ctx.symbol_table.lookup_tag(tag_name)
    {
        let entry = ctx.symbol_table.get_symbol_mut(entry);
        entry.is_completed = true;
        if let SymbolKind::EnumTag { is_complete } = &mut entry.kind {
            *is_complete = true;
        }
    }
    Ok(())
}

/// Resolve a type specifier to a QualType
fn resolve_type_specifier(
    ts: &ParsedTypeSpecifier,
    ctx: &mut LowerCtx,
    span: SourceSpan,
) -> Result<QualType, SemanticError> {
    use ParsedTypeSpecifier::*;
    match ts {
        Void => Ok(QualType::unqualified(ctx.registry.type_void)),
        Char => Ok(QualType::unqualified(ctx.registry.type_char)),
        Short => Ok(QualType::unqualified(ctx.registry.type_short)),
        Int => Ok(QualType::unqualified(ctx.registry.type_int)),
        Long => Ok(QualType::unqualified(ctx.registry.type_long)),
        LongLong => Ok(QualType::unqualified(ctx.registry.type_long_long)),
        UnsignedLong => Ok(QualType::unqualified(ctx.registry.type_long_unsigned)),
        UnsignedLongLong => Ok(QualType::unqualified(ctx.registry.type_long_long_unsigned)),
        UnsignedShort => Ok(QualType::unqualified(ctx.registry.type_short_unsigned)),
        UnsignedChar => Ok(QualType::unqualified(ctx.registry.type_char_unsigned)),
        SignedChar => Ok(QualType::unqualified(ctx.registry.type_schar)),
        SignedShort => Ok(QualType::unqualified(ctx.registry.type_short)),
        SignedLong => Ok(QualType::unqualified(ctx.registry.type_long)),
        SignedLongLong => Ok(QualType::unqualified(ctx.registry.type_long_long)),

        Float => Ok(QualType::unqualified(ctx.registry.type_float)),
        Double => Ok(QualType::unqualified(ctx.registry.type_double)),
        LongDouble => Ok(QualType::unqualified(ctx.registry.type_long_double)),
        ComplexFloat => Ok(QualType::unqualified(
            ctx.registry.complex_type(ctx.registry.type_float),
        )),
        ComplexDouble => Ok(QualType::unqualified(
            ctx.registry.complex_type(ctx.registry.type_double),
        )),
        ComplexLongDouble => Ok(QualType::unqualified(
            ctx.registry.complex_type(ctx.registry.type_long_double),
        )),
        Signed => Ok(QualType::unqualified(ctx.registry.type_signed)),
        Unsigned => Ok(QualType::unqualified(ctx.registry.type_int_unsigned)),
        Bool => Ok(QualType::unqualified(ctx.registry.type_bool)),
        Complex => Ok(QualType::unqualified(ctx.registry.type_complex_marker)),
        Atomic(p) => ctx.resolve_atomic_specifier(*p, span),
        Record(u, t, d) => ctx.resolve_record_specifier(*u, *t, d, span),
        Enum(t, e) => ctx.resolve_enum_specifier(*t, e, span),
        TypedefName(n) => ctx.resolve_typedef_name(*n, span),
        VaList => Ok(QualType::unqualified(ctx.registry.type_valist)),
        ParsedTypeSpecifier::Typeof(ty) => convert_to_qual_type(ctx, *ty, span, false),
        ParsedTypeSpecifier::TypeofExpr(expr) => {
            let expr_node = ctx.visit_expression(*expr);
            let tr = ctx
                .registry
                .alloc(crate::semantic::Type::new(crate::semantic::TypeKind::TypeofExpr(
                    expr_node,
                )));
            Ok(QualType::unqualified(tr))
        }
    }
}

/// Merge base types according to C type combination rules
fn merge_base_type(
    existing: Option<QualType>,
    new_type: QualType,
    ctx: &mut LowerCtx,
    span: SourceSpan,
) -> Option<QualType> {
    let Some(existing) = existing else {
        return Some(new_type);
    };

    let existing_type = ctx.registry.get(existing.ty());
    let new_type = ctx.registry.get(new_type.ty());

    match (&existing_type.kind, &new_type.kind) {
        (TypeKind::Builtin(e), TypeKind::Builtin(n)) => {
            let (&a, &b) = if (*e as u8) <= (*n as u8) { (e, n) } else { (n, e) };
            let ty = match (a, b) {
                (x, y) if x == y => {
                    if x == BuiltinType::Long {
                        ctx.registry.type_long_long
                    } else {
                        existing.ty()
                    }
                }
                // Signed modifier (Signed = 17)
                (BuiltinType::Char, BuiltinType::Signed) => ctx.registry.type_schar,
                (x, BuiltinType::Signed) if x.is_integer() => ctx.registry.get_builtin_type(x),

                // Unsigned modifier (UInt = 9)
                (BuiltinType::Char, BuiltinType::UInt) => ctx.registry.type_char_unsigned,
                (BuiltinType::Short, BuiltinType::UInt) => ctx.registry.type_short_unsigned,
                (BuiltinType::Int, BuiltinType::UInt) => ctx.registry.type_int_unsigned,
                (BuiltinType::UInt, BuiltinType::Long) => ctx.registry.type_long_unsigned,
                (BuiltinType::UInt, BuiltinType::LongLong) => ctx.registry.type_long_long_unsigned,
                (BuiltinType::UInt, BuiltinType::Signed) => ctx.registry.type_int_unsigned,

                // Int redundant specifier (Int = 8)
                (BuiltinType::Short, BuiltinType::Int) => ctx.registry.type_short,
                (BuiltinType::UShort, BuiltinType::Int) => ctx.registry.type_short_unsigned,
                (BuiltinType::Int, BuiltinType::Long) => ctx.registry.type_long,
                (BuiltinType::Int, BuiltinType::ULong) => ctx.registry.type_long_unsigned,
                (BuiltinType::Int, BuiltinType::LongLong) => ctx.registry.type_long_long,
                (BuiltinType::Int, BuiltinType::ULongLong) => ctx.registry.type_long_long_unsigned,

                // Long upgrades (Long = 10, ULong = 11, LongLong = 12, ULongLong = 13)
                (BuiltinType::Long, BuiltinType::LongLong) => ctx.registry.type_long_long,
                (BuiltinType::Long, BuiltinType::ULong) => ctx.registry.type_long_long_unsigned,
                (BuiltinType::Long, BuiltinType::ULongLong) => ctx.registry.type_long_long_unsigned,

                // Float/Double combinations (Double = 15)
                (BuiltinType::Long, BuiltinType::Double) => ctx.registry.type_long_double,

                // Complex combinations (Complex = 19)
                (BuiltinType::Float, BuiltinType::Complex) => ctx.registry.complex_type(ctx.registry.type_float),
                (BuiltinType::Double, BuiltinType::Complex) => ctx.registry.complex_type(ctx.registry.type_double),
                (BuiltinType::LongDouble, BuiltinType::Complex) => {
                    ctx.registry.complex_type(ctx.registry.type_long_double)
                }
                _ => {
                    ctx.report_error(span, SemanticErrorKind::ConflictingTypeSpecifiers { prev: existing });
                    ctx.registry.type_error
                }
            };
            Some(QualType::unqualified(ty))
        }
        _ => {
            ctx.report_error(span, SemanticErrorKind::ConflictingTypeSpecifiers { prev: existing });
            Some(QualType::unqualified(ctx.registry.type_error))
        }
    }
}

/// Validate specifier combinations for semantic correctness
fn validate_specifier_combinations(info: &DeclSpecInfo, ctx: &mut LowerCtx, span: SourceSpan) {
    // Storage class constraints (C11 6.7.1)
    let storage_conflict = if info.is_typedef {
        info.storage.is_some_and(|s| s != StorageClass::Typedef) || info.is_thread_local
    } else if info.is_thread_local {
        info.storage
            .is_some_and(|s| s != StorageClass::Static && s != StorageClass::Extern)
    } else {
        false
    };

    if storage_conflict {
        ctx.report_error(span, SemanticErrorKind::ConflictingStorageClasses);
    }

    // _Alignas constraints (C11 6.7.5p3)
    if info.alignment.is_some() && info.storage == Some(StorageClass::Register) {
        ctx.report_error(
            span,
            SemanticErrorKind::AlignmentNotAllowed {
                context: "register object",
            },
        );
    }

    if info.base_type.is_none() {
        ctx.report_error(span, SemanticErrorKind::MissingTypeSpecifier);
    }
}

/// Parse and validate declaration specifiers
fn visit_decl_specifiers(specs: &[ParsedDeclSpecifier], ctx: &mut LowerCtx, span: SourceSpan) -> DeclSpecInfo {
    let mut info = DeclSpecInfo::default();

    for spec in specs {
        match spec {
            ParsedDeclSpecifier::StorageClass(sc) => {
                if *sc == StorageClass::ThreadLocal {
                    if info.is_thread_local {
                        ctx.report_error(span, SemanticErrorKind::ConflictingStorageClasses);
                    }
                    info.is_thread_local = true;
                } else {
                    if info.storage.is_some() {
                        ctx.report_error(span, SemanticErrorKind::ConflictingStorageClasses);
                    }
                    info.storage = Some(*sc);
                    info.is_typedef |= *sc == StorageClass::Typedef;
                }
            }
            ParsedDeclSpecifier::TypeQualifier(tq) => {
                info.qualifiers.insert(match tq {
                    TypeQualifier::Const => TypeQualifiers::CONST,
                    TypeQualifier::Volatile => TypeQualifiers::VOLATILE,
                    TypeQualifier::Restrict => TypeQualifiers::RESTRICT,
                    TypeQualifier::Atomic => TypeQualifiers::ATOMIC,
                });
            }
            ParsedDeclSpecifier::TypeSpecifier(ts) => {
                let ty = resolve_type_specifier(ts, ctx, span).unwrap_or_else(|e| {
                    ctx.report_error(e.span, e.kind);
                    QualType::unqualified(ctx.registry.type_error)
                });
                info.base_type = merge_base_type(info.base_type, ty, ctx, span);
            }
            ParsedDeclSpecifier::AlignmentSpecifier(align) => {
                if let Some(val) = ctx.resolve_alignment(align, span) {
                    info.alignment = Some(std::cmp::max(info.alignment.unwrap_or(0), val));
                }
            }
            ParsedDeclSpecifier::FunctionSpecifier(fs) => match fs {
                FunctionSpecifier::Inline => info.is_inline = true,
                FunctionSpecifier::Noreturn => info.is_noreturn = true,
            },
            ParsedDeclSpecifier::Attribute => {}
        }
    }

    if let Some(base) = info.base_type {
        let ty = base.ty();
        if ty == ctx.registry.type_signed {
            info.base_type = Some(QualType::unqualified(ctx.registry.type_int));
        } else if ty == ctx.registry.type_complex_marker {
            info.base_type = Some(QualType::unqualified(
                ctx.registry.complex_type(ctx.registry.type_double),
            ));
        }
    }

    validate_specifier_combinations(&info, ctx, span);
    info
}

fn visit_function_parameters(
    params: &[ParsedParamData],
    ctx: &mut LowerCtx,
    is_definition: bool,
) -> Vec<FunctionParameter> {
    let mut seen_names = HashMap::new();
    params
        .iter()
        .map(|param| {
            let span = param.span;
            let spec_info = visit_decl_specifiers(&param.specifiers, ctx, span);

            // C standard: if type specifier is missing in a parameter, it defaults to int.
            let mut base_ty = spec_info
                .base_type
                .unwrap_or_else(|| QualType::unqualified(ctx.registry.type_int));
            base_ty = ctx.merge_qualifiers_with_check(base_ty, spec_info.qualifiers, span);

            let final_ty = if let Some(declarator) = &param.declarator {
                apply_declarator(
                    base_ty,
                    declarator,
                    ctx,
                    span,
                    &spec_info,
                    DeclaratorContext { in_parameter: true },
                )
            } else {
                base_ty
            };

            // Apply array-to-pointer decay for function parameters (C11 6.7.6.3)
            let ptr_quals = if let Some(decl) = &param.declarator {
                extract_array_param_qualifiers(decl)
            } else {
                TypeQualifiers::empty()
            };
            let decayed_ty = ctx.registry.decay(final_ty, ptr_quals);

            let pname = param.declarator.as_ref().and_then(extract_name);

            // C11 6.7.6.3p4: After adjustment, the parameters ... shall not have incomplete type.
            // C11 6.7.6.3p10: The special case of an unnamed parameter of type void as the only item
            // in the list specifies that the function has no parameters.
            if is_definition && !ctx.registry.is_complete(decayed_ty.ty()) {
                let is_void_param_list = params.len() == 1 && decayed_ty.is_void() && pname.is_none();
                if !is_void_param_list {
                    ctx.report_error(span, SemanticErrorKind::IncompleteType { ty: decayed_ty });
                }
            }

            if let Some(name) = pname {
                if let Some(&first_def) = seen_names.get(&name) {
                    ctx.report_error(span, SemanticErrorKind::Redefinition { name, first_def });
                } else {
                    seen_names.insert(name, span);
                }
            }

            if spec_info.alignment.is_some() {
                ctx.report_error(
                    span,
                    SemanticErrorKind::AlignmentNotAllowed {
                        context: "function parameter",
                    },
                );
            }

            // C11 6.7.6.3p2: "The only storage-class specifier that shall occur in a parameter declaration is register."
            if let Some(sc) = spec_info.storage
                && sc != StorageClass::Register
            {
                ctx.report_error(span, SemanticErrorKind::InvalidStorageClassForParameter);
            }
            if spec_info.is_thread_local {
                ctx.report_error(span, SemanticErrorKind::ThreadLocalNotAllowed);
            }

            // Function specifiers are only allowed for functions
            ctx.check_function_specifiers(&spec_info, span);

            FunctionParameter {
                param_type: decayed_ty,
                name: pname,
                storage: spec_info.storage,
            }
        })
        .collect()
}

/// Helper to get the actual parameters from the function declarator being defined.
/// This is necessary because interned function types in TypeRegistry might not have
/// the parameter names if the function was previously declared without them.
fn get_definition_params(decl: &ParsedDeclarator, ctx: &mut LowerCtx) -> Option<Vec<FunctionParameter>> {
    match decl {
        ParsedDeclarator::Function { inner, params, .. } => {
            if let Some(inner_params) = get_definition_params(inner, ctx) {
                Some(inner_params)
            } else {
                Some(visit_function_parameters(params, ctx, true))
            }
        }
        ParsedDeclarator::Pointer(_, inner) => inner.as_ref().and_then(|d| get_definition_params(d, ctx)),
        ParsedDeclarator::Array(inner, _) => get_definition_params(inner, ctx),
        ParsedDeclarator::BitField(inner, _) => get_definition_params(inner, ctx),
        _ => None,
    }
}

fn extract_name(decl: &ParsedDeclarator) -> Option<NameId> {
    match decl {
        ParsedDeclarator::Identifier(name, _) => Some(*name),
        ParsedDeclarator::Pointer(_, inner) => inner.as_ref().and_then(|d| extract_name(d)),
        ParsedDeclarator::Array(inner, _) => extract_name(inner),
        ParsedDeclarator::Function { inner, .. } => extract_name(inner),
        ParsedDeclarator::BitField(inner, _) => extract_name(inner),
        _ => None,
    }
}

/// Apply declarator transformations to a base type
fn apply_declarator(
    base_type: QualType,
    declarator: &ParsedDeclarator,
    ctx: &mut LowerCtx,
    span: SourceSpan,
    spec_info: &DeclSpecInfo,
    decl_ctx: DeclaratorContext,
) -> QualType {
    match declarator {
        ParsedDeclarator::Pointer(qualifiers, next) => {
            let ty = ctx.registry.pointer_to(base_type);
            let modified = ctx.merge_qualifiers_with_check(QualType::unqualified(ty), *qualifiers, span);
            match next {
                Some(next) => apply_declarator(modified, next, ctx, span, spec_info, decl_ctx),
                None => modified,
            }
        }
        ParsedDeclarator::Identifier(_, qualifiers) => ctx.merge_qualifiers_with_check(base_type, *qualifiers, span),
        ParsedDeclarator::Array(inner, size) => {
            let array_qt = ctx.lower_array_declarator(inner, size, base_type, span, decl_ctx);
            apply_declarator(array_qt, inner, ctx, span, spec_info, decl_ctx)
        }
        ParsedDeclarator::Function {
            inner,
            params,
            is_variadic,
        } => {
            let parameters = visit_function_parameters(params, ctx, false);
            let ty = ctx
                .registry
                .function_type(base_type.ty(), parameters, *is_variadic, spec_info.is_noreturn);
            apply_declarator(QualType::unqualified(ty), inner, ctx, span, spec_info, decl_ctx)
        }
        ParsedDeclarator::BitField(inner, _) => apply_declarator(base_type, inner, ctx, span, spec_info, decl_ctx),
        ParsedDeclarator::Abstract => base_type,
    }
}

/// Finalize tentative definitions by converting them to defined state
fn finalize_tentative_definitions(symbol_table: &mut SymbolTable) {
    for entry in &mut symbol_table.entries {
        if entry.scope_id == ScopeId::GLOBAL
            && matches!(entry.kind, SymbolKind::Variable { .. })
            && entry.def_state == DefinitionState::Tentative
        {
            entry.def_state = DefinitionState::Defined;
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
) {
    // Finalize tentative definitions
    finalize_tentative_definitions(symbol_table);

    // Create lowering context
    let mut lower_ctx = LowerCtx::new(parsed_ast, ast, diag, symbol_table, registry);

    // Perform recursive scope-aware lowering starting from root
    let root = parsed_ast.get_root();
    lower_ctx.visit_node(root);
}

impl<'a, 'src> LowerCtx<'a, 'src> {
    pub(crate) fn visit_node(&mut self, node: ParsedNodeRef) -> SmallVec<[NodeRef; 1]> {
        self.visit_node_entry(node, None)
    }

    fn visit_node_entry(&mut self, node: ParsedNodeRef, target_slots: Option<&[NodeRef]>) -> SmallVec<[NodeRef; 1]> {
        let parsed_node = self.parsed_ast.get_node(node);
        let span = parsed_node.span;
        let kind = parsed_node.kind.clone();

        match kind {
            ParsedNodeKind::TranslationUnit(children) => {
                smallvec![self.visit_translation_unit(&children, span)]
            }
            ParsedNodeKind::CompoundStatement(stmts) => {
                smallvec![self.visit_compound_statement(&stmts, target_slots, span)]
            }
            ParsedNodeKind::Declaration(decl_data) => self.visit_declaration(&decl_data, span, target_slots),
            ParsedNodeKind::FunctionDef(func_def) => {
                let node = self.get_or_push_slot(target_slots, span);
                self.visit_function_definition(&func_def, node, span);
                smallvec![node]
            }
            // ... other top level kinds ...
            _ => self.visit_node_rest(node, target_slots),
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
                ParsedNodeKind::FunctionDef(..) | ParsedNodeKind::StaticAssert(..) => 1,
                ParsedNodeKind::Declaration(decl) => {
                    if !decl.init_declarators.is_empty() {
                        decl.init_declarators.len()
                    } else if let Some(ParsedDeclSpecifier::TypeSpecifier(ts)) = decl
                        .specifiers
                        .iter()
                        .find(|s| matches!(s, ParsedDeclSpecifier::TypeSpecifier(..)))
                    {
                        match ts {
                            ParsedTypeSpecifier::Record(_, _, is_def) if is_def.is_some() => 1,
                            ParsedTypeSpecifier::Enum(_, is_def) if is_def.is_some() => 1,
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
            }
        }

        let decl_start = if decl_len > 0 { reserved_slots[0] } else { NodeRef::ROOT };
        self.ast.kinds[tu_node.index()] = NodeKind::TranslationUnit(TranslationUnitData {
            decl_start,
            decl_len,
            scope_id: ScopeId::GLOBAL,
        });
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
            }
        }

        if pushed {
            self.symbol_table.pop_scope();
        } else {
            self.symbol_table.set_current_scope(old_scope);
        }

        self.ast.kinds[node.index()] = NodeKind::CompoundStatement(CompoundStmtData {
            stmt_start,
            stmt_len,
            scope_id,
        });
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
                    let lowered_msg = self.visit_expression(*msg);
                    self.ast.kinds[target.index()] = NodeKind::StaticAssert(lowered_expr, lowered_msg);
                    self.ast.spans[target.index()] = span;
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
        let Some((sym, existing_scope)) = self.symbol_table.lookup_symbol(name) else {
            return new_ty;
        };

        let current_scope = self.symbol_table.current_scope();
        let symbol = self.symbol_table.get_symbol(sym);
        let symbol_type_info = symbol.type_info;
        let symbol_def_span = symbol.def_span;
        let symbol_has_linkage = symbol.has_linkage();
        let symbol_storage = match &symbol.kind {
            SymbolKind::Variable { storage, .. } => Some(*storage),
            SymbolKind::Function { storage } => Some(*storage),
            _ => None,
        };

        let is_global = current_scope == ScopeId::GLOBAL;
        let is_func = new_ty.is_function();
        let new_has_linkage = is_global || storage == Some(StorageClass::Extern) || is_func;
        let is_conflict = (existing_scope == current_scope) || (new_has_linkage && symbol_has_linkage);

        if !is_conflict {
            return new_ty;
        }

        // Check for linkage conflict (C11 6.2.2)
        if let Some(existing_s) = symbol_storage {
            let existing_is_static = existing_s == Some(StorageClass::Static);
            let new_is_static = storage == Some(StorageClass::Static);

            // static followed by extern/plain is OK and inherits internal linkage.
            // extern/plain followed by static is an error.
            if !existing_is_static && new_is_static {
                self.report_error(
                    span,
                    SemanticErrorKind::ConflictingLinkage {
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
                SemanticErrorKind::Redefinition {
                    name,
                    first_def: symbol_def_span,
                },
            );
            return new_ty;
        }

        let composite = self.registry.composite_type(symbol_type_info, new_ty);
        if composite.is_none() {
            self.report_error(
                span,
                SemanticErrorKind::ConflictingTypes {
                    name,
                    first_def: symbol_def_span,
                },
            );
            return new_ty;
        }
        let composite = composite.unwrap();

        // Update the existing symbol's type with the composite type
        let existing_mut = self.symbol_table.get_symbol_mut(sym);
        existing_mut.type_info = composite;

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
        let get_noreturn = |ty: QualType, registry: &TypeRegistry| {
            if let TypeKind::Function { is_noreturn, .. } = &registry.get(ty.ty()).kind {
                *is_noreturn
            } else {
                false
            }
        };

        let existing_is_noreturn = get_noreturn(existing_ty, self.registry);
        let new_is_noreturn = get_noreturn(new_ty, self.registry);

        if existing_is_noreturn != new_is_noreturn {
            self.report_error(span, SemanticErrorKind::ConflictingTypes { name, first_def });
        }
    }

    fn visit_function_definition(&mut self, func_def: &ParsedFunctionDefData, node: NodeRef, span: SourceSpan) {
        let spec_info = visit_decl_specifiers(&func_def.specifiers, self, span);
        let mut base_ty = spec_info
            .base_type
            .unwrap_or_else(|| QualType::unqualified(self.registry.type_int));
        base_ty = self.merge_qualifiers_with_check(base_ty, spec_info.qualifiers, span);

        let mut final_ty = apply_declarator(
            base_ty,
            &func_def.declarator,
            self,
            span,
            &spec_info,
            DeclaratorContext { in_parameter: false },
        );
        let func_name = extract_name(&func_def.declarator).expect("Function definition must have a name");

        final_ty = self.check_redeclaration_compatibility(func_name, final_ty, span, spec_info.storage);

        // Check for _Noreturn on existing declarations
        let existing_symbol_is_noreturn = if let Some((sym, _)) = self.symbol_table.lookup_symbol(func_name) {
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

        if let Err(SymbolTableError::InvalidRedefinition { existing, .. }) =
            self.symbol_table
                .define_function(func_name, final_ty.ty(), spec_info.storage, true, span)
        {
            let entry = self.symbol_table.get_symbol(existing);
            if entry.def_state == DefinitionState::Defined {
                let first_def = entry.def_span;
                self.report_error(
                    span,
                    SemanticErrorKind::Redefinition {
                        name: func_name,
                        first_def,
                    },
                );
            }
        }
        let func_sym = self.symbol_table.lookup_symbol(func_name).map(|(s, _)| s).unwrap();
        let scope_id = self.symbol_table.push_scope();

        // Implement __func__ (C11 6.4.2.2)
        {
            let func_name_str = func_name.to_string();
            let name_len = func_name_str.len();

            // Create string literal for initializer
            let func_name_id = NameId::new(&func_name_str);
            let init_literal = literal::Literal::String(func_name_id);
            let init_node = self.push_dummy(span);
            self.ast.kinds[init_node.index()] = NodeKind::Literal(init_literal);

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
            let _ = self
                .symbol_table
                .define_variable(func_id, qt, storage, Some(init_node), None, span);

            // Also define __PRETTY_FUNCTION__ (GCC extension)
            let pretty_func_id = NameId::new("__PRETTY_FUNCTION__");
            let _ = self
                .symbol_table
                .define_variable(pretty_func_id, qt, storage, Some(init_node), None, span);
        }

        // Pre-scan labels for forward goto support
        self.collect_labels(func_def.body);

        let parameters = get_definition_params(&func_def.declarator, self).unwrap_or_default();

        let param_len = parameters.len() as u16;
        let mut param_dummies = Vec::new();
        for _ in 0..param_len {
            param_dummies.push(self.push_dummy(span));
        }

        for (i, param) in parameters.iter().enumerate() {
            if let Some(pname) = param.name {
                // Check if parameter name conflicts with something already in scope (like __func__)
                self.check_redeclaration_compatibility(pname, param.param_type, span, None);

                if let Ok(sym) =
                    self.symbol_table
                        .define_variable(pname, param.param_type, param.storage, None, None, span)
                {
                    let param_dummy = param_dummies[i];
                    self.ast.kinds[param_dummy.index()] = NodeKind::Param(ParamData {
                        symbol: sym,
                        ty: param.param_type,
                    });
                }
            }
        }

        let param_start = if param_len > 0 { param_dummies[0] } else { NodeRef::ROOT };

        // Signal the body block (if it's a compound statement) to reuse the current scope
        self.next_compound_uses_scope = Some(scope_id);
        let body_node = self.visit_single_statement(func_def.body);
        // Ensure it's cleared even if it wasn't a compound statement
        self.next_compound_uses_scope = None;

        self.symbol_table.pop_scope();

        self.ast.kinds[node.index()] = NodeKind::Function(FunctionData {
            symbol: func_sym,
            ty: final_ty.ty(),
            is_noreturn: final_is_noreturn,
            param_start,
            param_len,
            body: body_node,
            scope_id,
        });
        self.ast.spans[node.index()] = span;
    }

    fn visit_declaration(
        &mut self,
        decl: &ParsedDeclarationData,
        span: SourceSpan,
        target_slots: Option<&[NodeRef]>,
    ) -> SmallVec<[NodeRef; 1]> {
        let spec_info = visit_decl_specifiers(&decl.specifiers, self, span);
        let mut base_ty = spec_info
            .base_type
            .unwrap_or(QualType::unqualified(self.registry.type_int));
        base_ty = self.merge_qualifiers_with_check(base_ty, spec_info.qualifiers, span);

        if decl.init_declarators.is_empty() {
            return self.visit_tag_definition(&spec_info, span, target_slots);
        }

        let mut nodes = SmallVec::new();
        for (i, init) in decl.init_declarators.iter().enumerate() {
            let target_slot = target_slots.and_then(|slots| slots.get(i)).copied();
            if let Some(node) = self.visit_single_declarator(init, base_ty, &spec_info, span, target_slot) {
                nodes.push(node);
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
        enum TypeData {
            Record(Option<NameId>, Arc<[StructMember]>, bool),
            Enum(Option<NameId>, Arc<[EnumConstant]>),
        }

        let type_info = self.registry.get(qt.ty());
        let type_data = match &type_info.kind {
            TypeKind::Record {
                tag, members, is_union, ..
            } => Some(TypeData::Record(*tag, members.clone(), *is_union)),
            TypeKind::Enum { tag, enumerators, .. } => Some(TypeData::Enum(*tag, enumerators.clone())),
            _ => None,
        };

        if let Some(data) = type_data {
            let node = self.get_or_push_slot(target_slots, span);
            self.check_function_specifiers(spec_info, span);

            match data {
                TypeData::Record(tag, members, is_union) => {
                    let member_start_idx = self.ast.kinds.len() as u32 + 1;
                    let member_start = NodeRef::new(member_start_idx).expect("NodeRef overflow");
                    let member_len = members.len() as u16;

                    for m in members.iter() {
                        self.ast.push_node(
                            NodeKind::FieldDecl(FieldDeclData {
                                name: m.name,
                                ty: m.member_type,
                                alignment: m.alignment,
                            }),
                            m.span,
                        );
                    }

                    self.ast.kinds[node.index()] = NodeKind::RecordDecl(RecordDeclData {
                        name: tag,
                        ty: qt.ty(),
                        member_start,
                        member_len,
                        is_union,
                    });
                }
                TypeData::Enum(tag, enumerators) => {
                    let mut member_start = NodeRef::ROOT;
                    let member_len = enumerators.len() as u16;

                    for (i, e) in enumerators.iter().enumerate() {
                        let member = self.ast.push_node(
                            NodeKind::EnumMember(EnumMemberData {
                                name: e.name,
                                value: e.value,
                                init_expr: e.init_expr,
                            }),
                            e.span,
                        );
                        if i == 0 {
                            member_start = member;
                        }
                    }

                    self.ast.kinds[node.index()] = NodeKind::EnumDecl(EnumDeclData {
                        name: tag,
                        ty: qt.ty(),
                        member_start,
                        member_len,
                    });
                }
            }
            return smallvec![node];
        }

        smallvec![]
    }

    fn visit_single_declarator(
        &mut self,
        init: &crate::ast::parsed::ParsedInitDeclarator,
        base_ty: QualType,
        spec_info: &DeclSpecInfo,
        span: SourceSpan,
        target_slot: Option<NodeRef>,
    ) -> Option<NodeRef> {
        let final_ty = apply_declarator(
            base_ty,
            &init.declarator,
            self,
            init.span,
            spec_info,
            DeclaratorContext { in_parameter: false },
        );

        // Check if declarator has an identifier
        let Some(name) = extract_name(&init.declarator) else {
            // Declaration without identifier (e.g., "int;") - emit warning and skip
            self.report_error(init.span, SemanticErrorKind::EmptyDeclaration);
            return None;
        };

        let node = if let Some(slot) = target_slot {
            self.ast.spans[slot.index()] = span;
            slot
        } else {
            self.push_dummy(span)
        };

        if spec_info.is_typedef {
            if spec_info.alignment.is_some() {
                self.report_error(init.span, SemanticErrorKind::AlignmentNotAllowed { context: "typedef" });
            }

            self.check_function_specifiers(spec_info, init.span);

            if let Err(SymbolTableError::InvalidRedefinition { existing, .. }) =
                self.symbol_table.define_typedef(name, final_ty, span)
            {
                let existing_symbol = self.symbol_table.get_symbol(existing);
                if let SymbolKind::Typedef { aliased_type } = existing_symbol.kind {
                    if aliased_type != final_ty {
                        self.report_error(
                            span,
                            SemanticErrorKind::RedefinitionWithDifferentType {
                                name,
                                first_def: existing_symbol.def_span,
                            },
                        );
                    }
                } else {
                    self.report_error(
                        span,
                        SemanticErrorKind::Redefinition {
                            name,
                            first_def: existing_symbol.def_span,
                        },
                    );
                }
            }
            self.ast.kinds[node.index()] = NodeKind::TypedefDecl(TypedefDeclData { name, ty: final_ty });
            return Some(node);
        }

        let is_func = final_ty.is_function();

        if !is_func {
            self.check_function_specifiers(spec_info, span);
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
        if spec_info.alignment.is_some() {
            self.report_error(span, SemanticErrorKind::AlignmentNotAllowed { context: "function" });
        }

        let final_qt = self.check_redeclaration_compatibility(name, final_ty, span, spec_info.storage);
        let func_decl = FunctionDeclData {
            name,
            ty: final_qt.ty(),
            storage: spec_info.storage,
            scope_id: self.symbol_table.current_scope(),
        };

        if let Err(crate::semantic::symbol_table::SymbolTableError::InvalidRedefinition { existing, .. }) = self
            .symbol_table
            .define_function(name, final_qt.ty(), spec_info.storage, false, span)
        {
            let first_def = self.symbol_table.get_symbol(existing).def_span;
            self.report_error(span, SemanticErrorKind::Redefinition { name, first_def });
        }
        self.ast.kinds[node.index()] = NodeKind::FunctionDecl(func_decl);
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
        qt = self.check_redeclaration_compatibility(name, qt, span, spec_info.storage);

        // Define variable in symbol table early so it's visible in its own initializer
        let sym_res = self
            .symbol_table
            .define_variable(name, qt, spec_info.storage, None, spec_info.alignment, span);

        let mut init_expr = None;
        if let Some(init_node) = init {
            init_expr = Some(self.visit_expression(init_node));

            // Update symbol entry with the actual initializer
            if let Ok(sym) = sym_res {
                let symbol = self.symbol_table.get_symbol_mut(sym);
                if let SymbolKind::Variable { initializer, .. } = &mut symbol.kind {
                    *initializer = init_expr;
                }
                symbol.def_state = DefinitionState::Defined;
            }
        }

        if let Some(ie) = init_expr
            && let TypeKind::Array {
                element_type,
                size: ArraySizeType::Incomplete,
            } = &self.registry.get(qt.ty()).kind
        {
            let element_type = *element_type;
            if let Some(deduced_size) = self.deduce_array_size_full(ie, element_type) {
                let new_ty = self
                    .registry
                    .array_of(element_type, ArraySizeType::Constant(deduced_size));
                qt = QualType::new(new_ty, qt.qualifiers());

                // Update type in symbol table as well
                if let Ok(sym) = sym_res {
                    self.symbol_table.get_symbol_mut(sym).type_info = qt;
                }
            }
        }

        // C11 6.7p7: If an identifier for an object is declared with no linkage, the type for the object
        // shall be complete by the end of its declarator...
        // C11 6.9.2p3: If the declaration of an identifier for an object is a tentative definition
        // and has internal linkage, the declared type shall not be an incomplete type.
        let current_scope = self.symbol_table.current_scope();
        let is_global = current_scope == ScopeId::GLOBAL;
        let has_internal_linkage = is_global && spec_info.storage == Some(StorageClass::Static);
        let has_no_linkage = !is_global && spec_info.storage != Some(StorageClass::Extern);

        if (has_internal_linkage || has_no_linkage) && !self.registry.is_complete(qt.ty()) {
            self.report_error(span, SemanticErrorKind::IncompleteType { ty: qt });
        }

        let var_decl = VarDeclData {
            name,
            ty: qt,
            storage: spec_info.storage,
            init: init_expr,
            alignment: spec_info.alignment.map(|a| a as u16),
        };

        if let Err(SymbolTableError::InvalidRedefinition { existing, .. }) = sym_res {
            let first_def = self.symbol_table.get_symbol(existing).def_span;
            self.report_error(span, SemanticErrorKind::Redefinition { name, first_def });
        }

        if let Ok(layout) = self.registry.ensure_layout(qt.ty())
            && let Some(req_align) = spec_info.alignment
        {
            let natural_align = layout.alignment as u32;
            if req_align < natural_align {
                self.report_error(
                    span,
                    SemanticErrorKind::AlignmentTooLoose {
                        requested: req_align,
                        natural: natural_align,
                    },
                );
            }
        }

        self.ast.kinds[node.index()] = NodeKind::VarDecl(var_decl);
    }

    fn visit_node_rest(&mut self, node: ParsedNodeRef, target_slots: Option<&[NodeRef]>) -> SmallVec<[NodeRef; 1]> {
        let node = self.parsed_ast.get_node(node);
        let span = node.span;
        match &node.kind {
            ParsedNodeKind::Declaration(decl) => self.visit_declaration(decl, span, target_slots),
            ParsedNodeKind::StaticAssert(expr, msg) => {
                let node = self.get_or_push_slot(target_slots, span);
                let lowered_expr = self.visit_expression(*expr);
                let lowered_msg = self.visit_expression(*msg);
                self.ast.kinds[node.index()] = NodeKind::StaticAssert(lowered_expr, lowered_msg);
                smallvec![node]
            }
            ParsedNodeKind::If(stmt) => {
                let node = self.get_or_push_slot(target_slots, span);
                let cond = self.visit_expression(stmt.condition);
                let then = self.visit_single_statement(stmt.then_branch);
                let else_branch = stmt.else_branch.map(|b| self.visit_single_statement(b));
                self.ast.kinds[node.index()] = NodeKind::If(IfStmt {
                    condition: cond,
                    then_branch: then,
                    else_branch,
                });
                smallvec![node]
            }
            ParsedNodeKind::While(stmt) => {
                let node = self.get_or_push_slot(target_slots, span);
                let cond = self.visit_expression(stmt.condition);
                let body = self.visit_single_statement(stmt.body);
                self.ast.kinds[node.index()] = NodeKind::While(WhileStmt { condition: cond, body });
                smallvec![node]
            }
            ParsedNodeKind::DoWhile(body, cond) => {
                let node = self.get_or_push_slot(target_slots, span);
                let b = self.visit_single_statement(*body);
                let c = self.visit_expression(*cond);
                self.ast.kinds[node.index()] = NodeKind::DoWhile(b, c);
                smallvec![node]
            }
            ParsedNodeKind::For(stmt) => {
                let node = self.get_or_push_slot(target_slots, span);
                let scope_id = self.symbol_table.push_scope();

                let init = stmt.init.map(|i| self.visit_node(i).first().cloned().unwrap());
                let cond = stmt.condition.map(|c| self.visit_expression(c));
                let inc = stmt.increment.map(|i| self.visit_expression(i));
                let body = self.visit_single_statement(stmt.body);
                self.symbol_table.pop_scope();

                self.ast.kinds[node.index()] = NodeKind::For(crate::ast::ForStmt {
                    init,
                    condition: cond,
                    increment: inc,
                    body,
                    scope_id,
                });
                smallvec![node]
            }
            ParsedNodeKind::Switch(cond, body) => {
                let node = self.get_or_push_slot(target_slots, span);
                let c = self.visit_expression(*cond);
                let b = self.visit_single_statement(*body);
                self.ast.kinds[node.index()] = NodeKind::Switch(c, b);
                smallvec![node]
            }
            ParsedNodeKind::Case(expr, stmt) => {
                let node = self.get_or_push_slot(target_slots, span);
                let e = self.visit_expression(*expr);
                let s = self.visit_single_statement(*stmt);
                self.ast.kinds[node.index()] = NodeKind::Case(e, s);
                smallvec![node]
            }
            ParsedNodeKind::CaseRange(start, end, stmt) => {
                let node = self.get_or_push_slot(target_slots, span);
                let s_expr = self.visit_expression(*start);
                let e_expr = self.visit_expression(*end);
                let s_stmt = self.visit_single_statement(*stmt);
                self.ast.kinds[node.index()] = NodeKind::CaseRange(s_expr, e_expr, s_stmt);
                smallvec![node]
            }
            ParsedNodeKind::Default(stmt) => {
                let node = self.get_or_push_slot(target_slots, span);
                let s = self.visit_single_statement(*stmt);
                self.ast.kinds[node.index()] = NodeKind::Default(s);
                smallvec![node]
            }
            ParsedNodeKind::Break => {
                let node = self.get_or_push_slot(target_slots, span);
                self.ast.kinds[node.index()] = NodeKind::Break;
                smallvec![node]
            }
            ParsedNodeKind::Continue => {
                let node = self.get_or_push_slot(target_slots, span);
                self.ast.kinds[node.index()] = NodeKind::Continue;
                smallvec![node]
            }
            ParsedNodeKind::Goto(name) => {
                let sym = self.resolve_label(*name, span);
                let node = self.get_or_push_slot(target_slots, span);
                self.ast.kinds[node.index()] = NodeKind::Goto(*name, sym);
                smallvec![node]
            }
            ParsedNodeKind::Label(name, inner) => {
                let node = self.get_or_push_slot(target_slots, span);
                let sym = self.define_label(*name, span);
                let s = self.visit_single_statement(*inner);
                self.ast.kinds[node.index()] = NodeKind::Label(*name, s, sym);
                smallvec![node]
            }
            ParsedNodeKind::Return(expr) => {
                let node = self.get_or_push_slot(target_slots, span);
                let e = expr.map(|x| self.visit_expression(x));
                self.ast.kinds[node.index()] = NodeKind::Return(e);
                smallvec![node]
            }
            ParsedNodeKind::ExpressionStatement(expr) => {
                let node = self.get_or_push_slot(target_slots, span);
                let e = expr.map(|x| self.visit_expression(x));
                self.ast.kinds[node.index()] = NodeKind::ExpressionStatement(e);
                smallvec![node]
            }
            ParsedNodeKind::BinaryOp(op, lhs, rhs) => {
                let node = self.get_or_push_slot(target_slots, span);
                let l = self.visit_expression(*lhs);
                let r = self.visit_expression(*rhs);
                self.ast.kinds[node.index()] = NodeKind::BinaryOp(*op, l, r);
                smallvec![node]
            }
            ParsedNodeKind::Assignment(op, lhs, rhs) => {
                let node = self.get_or_push_slot(target_slots, span);
                let l = self.visit_expression(*lhs);
                let r = self.visit_expression(*rhs);
                self.ast.kinds[node.index()] = NodeKind::Assignment(*op, l, r);
                smallvec![node]
            }
            ParsedNodeKind::UnaryOp(op, operand) => {
                let node = self.get_or_push_slot(target_slots, span);
                let o = self.visit_expression(*operand);
                self.ast.kinds[node.index()] = NodeKind::UnaryOp(*op, o);
                smallvec![node]
            }
            ParsedNodeKind::Literal(literal) => {
                let node = self.get_or_push_slot(target_slots, span);
                self.ast.kinds[node.index()] = NodeKind::Literal(*literal);
                smallvec![node]
            }
            ParsedNodeKind::Ident(name) => {
                let sym = self.resolve_ident(*name, span);
                let node = self.get_or_push_slot(target_slots, span);
                self.ast.kinds[node.index()] = NodeKind::Ident(*name, sym);
                smallvec![node]
            }
            ParsedNodeKind::FunctionCall(func, args) => {
                // Reserve a slot for the FunctionCall node to ensure parent < child index (when necessary)
                // If we have a target slot for the result, we can use it directly?
                // But FunctionCall needs to know ranges of args.
                // The structure is: CallNode -> FuncExpr, Arg1, Arg2...
                // FuncExpr and Args can be anywhere, but Args must be contiguous.

                let call_node_idx = self.get_or_push_slot(target_slots, span);

                let f = self.visit_expression(*func);

                // Reserve slots for arguments to ensure contiguity
                let mut arg_dummies = Vec::with_capacity(args.len());
                for _ in 0..args.len() {
                    arg_dummies.push(self.push_dummy(span));
                }

                // Lower arguments into reserved slots
                for (i, &arg) in args.iter().enumerate() {
                    self.visit_expression_into(arg, arg_dummies[i]);
                }

                let arg_start = if !arg_dummies.is_empty() {
                    arg_dummies[0]
                } else {
                    NodeRef::ROOT
                };
                let arg_len = arg_dummies.len() as u16;

                // Replace the reserved dummy node with the actual FunctionCall
                self.ast.kinds[call_node_idx.index()] = NodeKind::FunctionCall(CallExpr {
                    callee: f,
                    arg_start,
                    arg_len,
                });

                smallvec![call_node_idx]
            }
            ParsedNodeKind::MemberAccess(base, member, is_arrow) => {
                let node = self.get_or_push_slot(target_slots, span);
                let b = self.visit_expression(*base);
                self.ast.kinds[node.index()] = NodeKind::MemberAccess(b, *member, *is_arrow);
                smallvec![node]
            }
            ParsedNodeKind::Cast(ty_name, expr) => {
                let node = self.get_or_push_slot(target_slots, span);
                let e = self.visit_expression(*expr);
                let ty = convert_to_qual_type(self, *ty_name, span, false)
                    .unwrap_or(QualType::unqualified(self.registry.type_error));
                self.ast.kinds[node.index()] = NodeKind::Cast(ty, e);
                smallvec![node]
            }
            ParsedNodeKind::PostIncrement(operand) => {
                let node = self.get_or_push_slot(target_slots, span);
                let o = self.visit_expression(*operand);
                self.ast.kinds[node.index()] = NodeKind::PostIncrement(o);
                smallvec![node]
            }
            ParsedNodeKind::PostDecrement(operand) => {
                let node = self.get_or_push_slot(target_slots, span);
                let o = self.visit_expression(*operand);
                self.ast.kinds[node.index()] = NodeKind::PostDecrement(o);
                smallvec![node]
            }
            ParsedNodeKind::IndexAccess(base, index) => {
                let node = self.get_or_push_slot(target_slots, span);
                let b = self.visit_expression(*base);
                let i = self.visit_expression(*index);
                self.ast.kinds[node.index()] = NodeKind::IndexAccess(b, i);
                smallvec![node]
            }
            ParsedNodeKind::TernaryOp(cond, then_branch, else_branch) => {
                let node = self.get_or_push_slot(target_slots, span);
                let c = self.visit_expression(*cond);
                let t = self.visit_expression(*then_branch);
                let e = self.visit_expression(*else_branch);
                self.ast.kinds[node.index()] = NodeKind::TernaryOp(c, t, e);
                smallvec![node]
            }
            ParsedNodeKind::GnuStatementExpression(stmt, _expr) => {
                let node = self.get_or_push_slot(target_slots, span);
                let s = self.visit_single_statement(*stmt);

                let last_stmt = if let NodeKind::CompoundStatement(data) = self.ast.get_kind(s) {
                    data.stmt_start.range(data.stmt_len).last()
                } else {
                    None
                };

                let result_expr = last_stmt
                    .and_then(|stmt| {
                        if let NodeKind::ExpressionStatement(Some(e)) = self.ast.get_kind(stmt) {
                            Some(*e)
                        } else {
                            None
                        }
                    })
                    .unwrap_or_else(|| self.push_dummy(span));

                self.ast.kinds[node.index()] = NodeKind::GnuStatementExpression(s, result_expr);
                smallvec![node]
            }
            ParsedNodeKind::SizeOfExpr(expr) => {
                let node = self.get_or_push_slot(target_slots, span);
                let e = self.visit_expression(*expr);
                self.ast.kinds[node.index()] = NodeKind::SizeOfExpr(e);
                smallvec![node]
            }
            ParsedNodeKind::SizeOfType(ty_name) => {
                let node = self.get_or_push_slot(target_slots, span);
                let ty = convert_to_qual_type(self, *ty_name, span, false)
                    .unwrap_or(QualType::unqualified(self.registry.type_error));
                self.ast.kinds[node.index()] = NodeKind::SizeOfType(ty);
                smallvec![node]
            }
            ParsedNodeKind::AlignOf(ty_name) => {
                let node = self.get_or_push_slot(target_slots, span);
                let ty = convert_to_qual_type(self, *ty_name, span, false)
                    .unwrap_or(QualType::unqualified(self.registry.type_error));
                self.ast.kinds[node.index()] = NodeKind::AlignOf(ty);
                smallvec![node]
            }
            ParsedNodeKind::BuiltinVaArg(ty_name, expr) => {
                let node = self.get_or_push_slot(target_slots, span);
                let e = self.visit_expression(*expr);
                let ty = convert_to_qual_type(self, *ty_name, span, false)
                    .unwrap_or(QualType::unqualified(self.registry.type_error));
                self.ast.kinds[node.index()] = NodeKind::BuiltinVaArg(ty, e);
                smallvec![node]
            }
            ParsedNodeKind::BuiltinOffsetof(ty_name, expr) => {
                let node = self.get_or_push_slot(target_slots, span);
                let e = self.visit_expression(*expr);
                let ty = convert_to_qual_type(self, *ty_name, span, false)
                    .unwrap_or(QualType::unqualified(self.registry.type_error));
                self.ast.kinds[node.index()] = NodeKind::BuiltinOffsetof(ty, e);
                smallvec![node]
            }
            ParsedNodeKind::BuiltinVaStart(ap, last) => {
                let node = self.get_or_push_slot(target_slots, span);
                let a = self.visit_expression(*ap);
                let l = self.visit_expression(*last);
                self.ast.kinds[node.index()] = NodeKind::BuiltinVaStart(a, l);
                smallvec![node]
            }
            ParsedNodeKind::BuiltinVaEnd(ap) => {
                let node = self.get_or_push_slot(target_slots, span);
                let a = self.visit_expression(*ap);
                self.ast.kinds[node.index()] = NodeKind::BuiltinVaEnd(a);
                smallvec![node]
            }
            ParsedNodeKind::BuiltinVaCopy(dst, src) => {
                let node = self.get_or_push_slot(target_slots, span);
                let d = self.visit_expression(*dst);
                let s = self.visit_expression(*src);
                self.ast.kinds[node.index()] = NodeKind::BuiltinVaCopy(d, s);
                smallvec![node]
            }
            ParsedNodeKind::BuiltinExpect(exp, c) => {
                let node = self.get_or_push_slot(target_slots, span);
                let e = self.visit_expression(*exp);
                let expected = self.visit_expression(*c);
                self.ast.kinds[node.index()] = NodeKind::BuiltinExpect(e, expected);
                smallvec![node]
            }
            ParsedNodeKind::BuiltinPopcount(expr) => {
                let node = self.get_or_push_slot(target_slots, span);
                let e = self.visit_expression(*expr);
                self.ast.kinds[node.index()] = NodeKind::BuiltinPopcount(e);
                smallvec![node]
            }
            ParsedNodeKind::BuiltinClz(expr) => {
                let node = self.get_or_push_slot(target_slots, span);
                let e = self.visit_expression(*expr);
                self.ast.kinds[node.index()] = NodeKind::BuiltinClz(e);
                smallvec![node]
            }
            ParsedNodeKind::BuiltinCtz(expr) => {
                let node = self.get_or_push_slot(target_slots, span);
                let e = self.visit_expression(*expr);
                self.ast.kinds[node.index()] = NodeKind::BuiltinCtz(e);
                smallvec![node]
            }
            ParsedNodeKind::BuiltinTypesCompatibleP(ty1, ty2) => {
                let node = self.get_or_push_slot(target_slots, span);
                let t1 = convert_to_qual_type(self, *ty1, span, false)
                    .unwrap_or(QualType::unqualified(self.registry.type_error));
                let t2 = convert_to_qual_type(self, *ty2, span, false)
                    .unwrap_or(QualType::unqualified(self.registry.type_error));
                self.ast.kinds[node.index()] = NodeKind::BuiltinTypesCompatibleP(t1, t2);
                smallvec![node]
            }
            ParsedNodeKind::AtomicOp(op, args) => {
                let node = self.get_or_push_slot(target_slots, span);

                // Reserve slots for args to ensure contiguity
                let mut arg_dummies = Vec::with_capacity(args.len());
                for _ in 0..args.len() {
                    arg_dummies.push(self.push_dummy(span));
                }

                // Lower arguments into reserved slots
                for (i, &arg) in args.iter().enumerate() {
                    self.visit_expression_into(arg, arg_dummies[i]);
                }

                let arg_start = if !arg_dummies.is_empty() {
                    arg_dummies[0]
                } else {
                    NodeRef::ROOT
                };
                let arg_len = arg_dummies.len() as u16;

                self.ast.kinds[node.index()] = NodeKind::AtomicOp(*op, arg_start, arg_len);
                smallvec![node]
            }
            ParsedNodeKind::CompoundLiteral(ty_name, init) => {
                let node = self.get_or_push_slot(target_slots, span);
                let mut qt = convert_to_qual_type(self, *ty_name, span, false)
                    .unwrap_or(QualType::unqualified(self.registry.type_error));
                let i = self.visit_expression(*init);

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

                self.ast.kinds[node.index()] = NodeKind::CompoundLiteral(qt, i);
                smallvec![node]
            }
            ParsedNodeKind::BuiltinChooseExpr(cond, true_expr, false_expr) => {
                let node = self.get_or_push_slot(target_slots, span);
                let c = self.visit_expression(*cond);
                let t = self.visit_expression(*true_expr);
                let e = self.visit_expression(*false_expr);
                self.ast.kinds[node.index()] = NodeKind::BuiltinChooseExpr(c, t, e);
                smallvec![node]
            }
            ParsedNodeKind::BuiltinConstantP(expr) => {
                let node = self.get_or_push_slot(target_slots, span);
                let e = self.visit_expression(*expr);
                self.ast.kinds[node.index()] = NodeKind::BuiltinConstantP(e);
                smallvec![node]
            }
            ParsedNodeKind::GenericSelection(control, associations) => {
                let node = self.get_or_push_slot(target_slots, span);
                let c = self.visit_expression(*control);

                let assoc_len = associations.len() as u16;
                let mut assoc_dummies = Vec::new();
                for _ in 0..assoc_len {
                    assoc_dummies.push(self.push_dummy(span));
                }

                for (i, a) in associations.iter().enumerate() {
                    let ty = a.type_name.map(|t| {
                        convert_to_qual_type(self, t, span, false)
                            .unwrap_or(QualType::unqualified(self.registry.type_error))
                    });
                    let expr = self.visit_expression(a.result_expr);
                    let assoc_dummy = assoc_dummies[i];
                    self.ast.kinds[assoc_dummy.index()] =
                        NodeKind::GenericAssociation(GenericAssociationData { ty, result_expr: expr });
                }

                let assoc_start = if assoc_len > 0 { assoc_dummies[0] } else { NodeRef::ROOT };

                self.ast.kinds[node.index()] = NodeKind::GenericSelection(GenericSelectionData {
                    control: c,
                    assoc_start,
                    assoc_len,
                });
                smallvec![node]
            }
            ParsedNodeKind::InitializerList(inits) => {
                let node = self.get_or_push_slot(target_slots, span);

                // Reserve slots for InitializerItems to ensure parent < child index
                let mut init_dummies = Vec::new();
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
                            ParsedDesignator::GnuArrayRange(start, end) => {
                                Designator::GnuArrayRange(self.visit_expression(*start), self.visit_expression(*end))
                            }
                        };
                        let d_dummy = designator_dummies[j];
                        self.ast.kinds[d_dummy.index()] = NodeKind::Designator(node_kind);
                    }

                    let designator_start = if designator_count > 0 {
                        designator_dummies[0]
                    } else {
                        NodeRef::ROOT
                    };

                    let di = DesignatedInitializer {
                        designator_start,
                        designator_len: designator_count,
                        initializer: expr,
                    };

                    let item_dummy = init_dummies[i];
                    self.ast.kinds[item_dummy.index()] = NodeKind::InitializerItem(di);
                }

                let init_len = init_dummies.len() as u16;
                let init_start = if init_len > 0 { init_dummies[0] } else { NodeRef::ROOT };

                self.ast.kinds[node.index()] = NodeKind::InitializerList(InitializerListData { init_start, init_len });

                smallvec![node]
            }
            ParsedNodeKind::EmptyStatement => {
                smallvec![]
            }
            _ => {
                // For unhandled nodes (or Dummy), push a Dummy node to avoid ICE
                smallvec![self.push_dummy(span)]
            }
        }
    }

    pub(crate) fn visit_expression(&mut self, node: ParsedNodeRef) -> NodeRef {
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

    fn resolve_ident(&mut self, name: NameId, span: SourceSpan) -> SymbolRef {
        if let Some((sym, _)) = self.symbol_table.lookup_symbol(name) {
            sym
        } else {
            let name_str = name.as_str();
            if name_str.starts_with("__builtin_")
                && let Some(sym) = self.handle_builtin_implicit_decl(name, name_str, span)
            {
                return sym;
            }
            self.report_error(span, SemanticErrorKind::UndeclaredIdentifier { name });
            SymbolRef::new(1).expect("SymbolRef 1 creation failed")
        }
    }

    fn handle_builtin_implicit_decl(&mut self, name: NameId, name_str: &str, span: SourceSpan) -> Option<SymbolRef> {
        let (params, ret_ty) = match name_str {
            "__builtin_nanf" | "__builtin_nan" => {
                let char_const = QualType::new(self.registry.type_char, TypeQualifiers::CONST);
                let char_ptr = QualType::unqualified(self.registry.pointer_to(char_const));
                let params = vec![FunctionParameter {
                    param_type: char_ptr,
                    name: None,
                    storage: None,
                }];
                let ret = if name_str == "__builtin_nanf" {
                    self.registry.type_float
                } else {
                    self.registry.type_double
                };
                (params, ret)
            }
            "__builtin_inff" | "__builtin_inf" | "__builtin_huge_val" | "__builtin_huge_valf" => {
                let ret = if name_str.ends_with('f') {
                    self.registry.type_float
                } else {
                    self.registry.type_double
                };
                (vec![], ret)
            }
            _ => return None,
        };

        let func_ty = self.registry.function_type(ret_ty, params, false, false);

        // Save current scope and switch to global for implicit decl
        let old_scope = self.symbol_table.current_scope();
        self.symbol_table.set_current_scope(ScopeId::GLOBAL);
        let result = self.symbol_table.define_function(name, func_ty, None, false, span).ok();
        self.symbol_table.set_current_scope(old_scope);
        result
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
            self.report_error(span, SemanticErrorKind::UndeclaredIdentifier { name });
            SymbolRef::new(1).unwrap()
        }
    }

    fn collect_labels(&mut self, node: ParsedNodeRef) {
        let parsed_node = self.parsed_ast.get_node(node);
        if let ParsedNodeKind::Label(name, _) = &parsed_node.kind {
            let _ = self.define_label(*name, parsed_node.span);
        }
        let mut f = |child| self.collect_labels(child);
        parsed_node.kind.for_each_child(&mut f);
    }

    fn try_deduce_string_initializer_size(&self, init_node: NodeRef, element_type: TypeRef) -> Option<usize> {
        match self.ast.get_kind(init_node) {
            NodeKind::Literal(literal::Literal::String(s)) => {
                let parsed = crate::semantic::literal_utils::parse_string_literal(*s);
                Some(parsed.size)
            }
            NodeKind::InitializerList(list) if list.init_len > 0 => {
                let first_item = list.init_start;
                if let NodeKind::InitializerItem(item) = self.ast.get_kind(first_item)
                    && item.designator_len == 0
                    && let NodeKind::Literal(literal::Literal::String(s)) = self.ast.get_kind(item.initializer)
                {
                    let parsed = crate::semantic::literal_utils::parse_string_literal(*s);
                    let string_elem_type = self.registry.get_builtin_type(parsed.builtin_type);

                    if self.registry.is_compatible(
                        QualType::unqualified(element_type),
                        QualType::unqualified(string_elem_type),
                    ) {
                        return Some(parsed.size);
                    }
                }
                None
            }
            _ => None,
        }
    }

    fn deduce_array_size_full(&self, init_node: NodeRef, element_type: TypeRef) -> Option<usize> {
        if let Some(size) = self.try_deduce_string_initializer_size(init_node, element_type) {
            return Some(size);
        }

        match self.ast.get_kind(init_node) {
            NodeKind::InitializerList(list) => {
                let mut max_index: i64 = -1;
                let mut current_index: i64 = 0;
                let eval = |e| const_eval::eval_const_expr(&self.const_ctx(), e);

                let mut iter = list.init_start.range(list.init_len).peekable();

                while let Some(item) = iter.peek().copied() {
                    let NodeKind::InitializerItem(init) = self.ast.get_kind(item) else {
                        iter.next();
                        continue;
                    };

                    if init.designator_len > 0 {
                        match self.ast.get_kind(init.designator_start) {
                            NodeKind::Designator(Designator::ArrayIndex(idx)) => {
                                current_index = eval(*idx)?;
                            }
                            NodeKind::Designator(Designator::GnuArrayRange(start, end)) => {
                                let (s_v, e_v) = (eval(*start)?, eval(*end)?);
                                if s_v > e_v {
                                    return None;
                                }
                                current_index = e_v;
                            }
                            _ => {}
                        }
                    }

                    max_index = max_index.max(current_index);

                    let start_item = iter.peek().map(|n| n.get());
                    self.consume_initializers(element_type, &mut iter, true);

                    if let Some(end_item) = iter.peek().map(|n| n.get())
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
        &self,
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

        let NodeKind::InitializerItem(init) = self.ast.get_kind(item) else {
            // Should not happen in valid AST
            return;
        };

        if init.designator_len > 0 {
            // Check for array designators
            match self.ast.get_kind(init.designator_start) {
                NodeKind::Designator(Designator::ArrayIndex(_))
                | NodeKind::Designator(Designator::GnuArrayRange(_, _)) => {
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
        }

        // Check braced initializer
        if let NodeKind::InitializerList(_) = self.ast.get_kind(init.initializer) {
            iter.next();
            return;
        }

        // Brace elision logic
        let type_kind = &self.registry.get(element_type).kind;
        match type_kind {
            TypeKind::Record { members, .. } => {
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
                        && let NodeKind::InitializerItem(next_init) = self.ast.get_kind(*next)
                        && next_init.designator_len > 0
                    {
                        match self.ast.get_kind(next_init.designator_start) {
                            NodeKind::Designator(Designator::ArrayIndex(_))
                            | NodeKind::Designator(Designator::GnuArrayRange(_, _)) => {
                                return;
                            }
                            _ => {}
                        }
                    }
                }
            }
            TypeKind::Array { element_type, size } => {
                if let ArraySizeType::Constant(len) = size {
                    let mut is_first = true;
                    for _ in 0..*len {
                        let allow = allow_array_designator && is_first;
                        self.consume_initializers(*element_type, iter, allow);
                        is_first = false;

                        if iter.peek().is_none() {
                            return;
                        }
                        // Check stopper
                        if let Some(next) = iter.peek()
                            && let NodeKind::InitializerItem(next_init) = self.ast.get_kind(*next)
                            && next_init.designator_len > 0
                        {
                            match self.ast.get_kind(next_init.designator_start) {
                                NodeKind::Designator(Designator::ArrayIndex(_))
                                | NodeKind::Designator(Designator::GnuArrayRange(_, _)) => {
                                    return;
                                }
                                _ => {}
                            }
                        }
                    }
                } else {
                    // Variable/Incomplete array. Consume 1 item for safety.
                    iter.next();
                }
            }
            _ => {
                // Scalar
                iter.next();
            }
        }
    }
}
/// Extracts the bit-field width from a declarator if it exists.
fn extract_bit_field_width(declarator: &ParsedDeclarator, ctx: &mut LowerCtx) -> Option<u16> {
    match declarator {
        ParsedDeclarator::BitField(_, expr) => {
            let width_expr = ctx.visit_expression(*expr);
            let span = ctx.ast.get_span(width_expr);

            match const_eval::eval_const_expr(&ctx.const_ctx(), width_expr) {
                Some(val) if (0..=65535).contains(&val) => Some(val as u16),
                Some(_) => {
                    ctx.report_error(span, SemanticErrorKind::InvalidBitfieldWidth);
                    None
                }
                None => {
                    ctx.report_error(span, SemanticErrorKind::NonConstantBitfieldWidth);
                    None
                }
            }
        }
        ParsedDeclarator::Pointer(_, Some(inner)) => extract_bit_field_width(inner, ctx),
        ParsedDeclarator::Array(inner, _) => extract_bit_field_width(inner, ctx),
        ParsedDeclarator::Function { inner, .. } => extract_bit_field_width(inner, ctx),
        _ => None,
    }
}

/// Common logic for lowering struct members, used by both TypeSpecifier::Record lowering
/// and Declarator::AnonymousRecord handling.
fn visit_struct_members(member_nodes: &[ParsedNodeRef], ctx: &mut LowerCtx, span: SourceSpan) -> Vec<StructMember> {
    let mut struct_members = Vec::new();

    for &node in member_nodes {
        let node = ctx.parsed_ast.get_node(node);
        match &node.kind {
            ParsedNodeKind::StaticAssert(cond, msg) => {
                ctx.check_static_assert(*cond, *msg, node.span);
            }
            ParsedNodeKind::Declaration(decl) => {
                let spec_info = visit_decl_specifiers(&decl.specifiers, ctx, span);

                if spec_info.storage.is_some() {
                    ctx.report_error(span, SemanticErrorKind::ConflictingStorageClasses);
                }

                if decl.init_declarators.is_empty() {
                    if let Some(base) = spec_info.base_type {
                        let ty = ctx.merge_qualifiers_with_check(base, spec_info.qualifiers, span);
                        if ty.is_record()
                            && matches!(&ctx.registry.get(ty.ty()).kind, TypeKind::Record { tag: None, .. })
                        {
                            struct_members.push(StructMember {
                                member_type: ty,
                                alignment: spec_info.alignment,
                                span,
                                ..Default::default()
                            });
                        }
                    }
                    continue;
                }

                for id in &decl.init_declarators {
                    let bit_field_size = extract_bit_field_width(&id.declarator, ctx);

                    if bit_field_size.is_some() && spec_info.alignment.is_some() {
                        ctx.report_error(id.span, SemanticErrorKind::AlignmentNotAllowed { context: "bit-field" });
                    }

                    ctx.check_function_specifiers(&spec_info, id.span);

                    let name = extract_name(&id.declarator);
                    let base = spec_info
                        .base_type
                        .unwrap_or_else(|| QualType::unqualified(ctx.registry.type_int));
                    let qualified_base = ctx.merge_qualifiers_with_check(base, spec_info.qualifiers, id.span);

                    let member_type = apply_declarator(
                        qualified_base,
                        &id.declarator,
                        ctx,
                        id.span,
                        &spec_info,
                        DeclaratorContext { in_parameter: false },
                    );

                    ctx.validate_member_layout(member_type, bit_field_size, spec_info.alignment, name, id.span);

                    struct_members.push(StructMember {
                        name,
                        member_type,
                        bit_field_size,
                        alignment: spec_info.alignment,
                        span: id.span,
                    });
                }
            }
            _ => unreachable!(),
        }
    }
    struct_members
}
