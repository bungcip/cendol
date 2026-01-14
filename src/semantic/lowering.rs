//! SemanticLowering
//!
//! Responsibility
//! - Declaration Lowering (Declaration -> VarDecl/RecordDecl/EnumDecl/TypedefDecl, FunctionDef -> Function)
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
use std::num::NonZeroU16;

use crate::ast::parsed::{
    ParsedDeclarationData, ParsedDeclarator, ParsedFunctionDefData, ParsedNodeKind, ParsedNodeRef, ParsedTypeSpecifier,
};
use crate::ast::*;
use crate::diagnostic::{DiagnosticEngine, SemanticError};
use crate::semantic::const_eval::{self, ConstEvalCtx};
use crate::semantic::symbol_table::{DefinitionState, SymbolTableError};
use crate::semantic::{
    ArraySizeType, BuiltinType, EnumConstant, ScopeId, StructMember, SymbolKind, SymbolRef, SymbolTable, TypeKind,
    TypeQualifiers, TypeRef, TypeRegistry,
};
use crate::semantic::{FunctionParameter, QualType};
use crate::source_manager::SourceSpan;

/// Recursively apply parsed declarator to base type
fn apply_parsed_declarator_recursive(
    current_type: QualType,
    declarator_ref: ParsedDeclRef,
    ctx: &mut LowerCtx,
) -> QualType {
    let declarator_node = ctx.parsed_ast.parsed_types.get_decl(declarator_ref);

    match declarator_node {
        ParsedDeclaratorNode::Identifier { .. } => current_type,
        ParsedDeclaratorNode::Pointer { qualifiers, inner } => {
            // Pointer
            // Apply Pointer modifier to the current type first (Top-Down)
            let pointer_type = ctx.registry.pointer_to(current_type);
            let modified_current = ctx
                .registry
                .merge_qualifiers(QualType::unqualified(pointer_type), qualifiers);
            apply_parsed_declarator_recursive(modified_current, inner, ctx)
        }
        ParsedDeclaratorNode::Array { size, inner } => {
            // Array
            // Apply Array modifier to the current type
            // Propagate qualifiers from the element type to the array type (C11 6.7.3)
            let array_size = convert_parsed_array_size(&size, ctx);
            let array_type_ref = ctx.registry.array_of(current_type.ty(), array_size);
            let qualified_array = ctx
                .registry
                .merge_qualifiers(QualType::unqualified(array_type_ref), current_type.qualifiers());
            apply_parsed_declarator_recursive(qualified_array, inner, ctx)
        }
        ParsedDeclaratorNode::Function { params, flags, inner } => {
            // Function
            // Process parameters separately
            let parsed_params: Vec<_> = ctx.parsed_ast.parsed_types.get_params(params).to_vec();
            let mut processed_params = Vec::new();
            for param in parsed_params {
                let param_type = convert_to_qual_type(ctx, param.ty, param.span).unwrap_or_else(|_| {
                    // Create an error type if conversion fails
                    QualType::unqualified(ctx.registry.type_int)
                });

                // Apply array-to-pointer decay for function parameters
                let ptr_quals = extract_array_param_qualifiers_from_ref(param.ty.declarator, ctx);
                let decayed_param_type = ctx.registry.decay(param_type, ptr_quals);

                processed_params.push(FunctionParameter {
                    param_type: decayed_param_type,
                    name: param.name,
                });
            }

            // Apply Function modifier to the current type
            // TODO: Handle function returning qualified type
            let function_type_ref = ctx
                .registry
                .function_type(current_type.ty(), processed_params, flags.is_variadic);
            apply_parsed_declarator_recursive(QualType::unqualified(function_type_ref), inner, ctx)
        }
    }
}

fn extract_array_param_qualifiers_from_ref(decl_ref: ParsedDeclRef, ctx: &LowerCtx) -> TypeQualifiers {
    let decl = ctx.parsed_ast.parsed_types.get_decl(decl_ref);
    match decl {
        ParsedDeclaratorNode::Identifier { .. } => TypeQualifiers::empty(),
        ParsedDeclaratorNode::Pointer { inner, .. } => extract_array_param_qualifiers_from_ref(inner, ctx),
        ParsedDeclaratorNode::Function { inner, .. } => extract_array_param_qualifiers_from_ref(inner, ctx),
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
        ParsedDeclarator::Pointer(_, inner) => {
            if let Some(inner_decl) = inner {
                extract_array_param_qualifiers(inner_decl)
            } else {
                TypeQualifiers::empty()
            }
        }
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
        ParsedDeclarator::Function { inner, .. } => extract_array_param_qualifiers(inner),
        ParsedDeclarator::BitField(inner, _) => extract_array_param_qualifiers(inner),
        ParsedDeclarator::AnonymousRecord(..) => TypeQualifiers::empty(),
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
    if let Some(parsed_ref) = size {
        let expr_ref = ctx.lower_expression(parsed_ref);
        let const_ctx = ConstEvalCtx {
            ast: ctx.ast,
            symbol_table: ctx.symbol_table,
        };
        if let Some(val) = const_eval::eval_const_expr(&const_ctx, expr_ref) {
            if val < 0 {
                ctx.report_error(SemanticError::InvalidArraySize {
                    span: ctx.ast.get_span(expr_ref),
                });
                return ArraySizeType::Incomplete;
            }
            return ArraySizeType::Constant(val as usize);
        } else {
            // For now, we only support constant sizes (VLA support is future)
            // Or maybe we should return Variable(expr_ref) and let ensure_layout fail?
            // But verify what Variable does.
            // ensure_layout returns "incomplete/VLA array layout" error.
            return ArraySizeType::Variable(expr_ref);
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
    pub(crate) has_errors: bool,
    pub(crate) registry: &'a mut TypeRegistry,
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
            has_errors: false,
            registry,
        }
    }

    /// Report a semantic error and mark context as having errors
    pub(crate) fn report_error(&mut self, error: SemanticError) {
        self.has_errors = true;
        self.diag.report(error);
    }

    fn set_scope(&mut self, _node_ref: NodeRef, _scope_id: ScopeId) {
        // scope_map removed.
        // Nodes that need scope now store it directly.
    }

    fn push_dummy(&mut self, span: SourceSpan) -> NodeRef {
        let node_ref = self.ast.push_dummy(span);
        self.set_scope(node_ref, self.symbol_table.current_scope());
        node_ref
    }

    /// Get the first slot from target_slots if available, otherwise push a new dummy node.
    /// Also ensures scope is set on the node.
    fn get_or_push_slot(&mut self, target_slots: Option<&[NodeRef]>, span: SourceSpan) -> NodeRef {
        if let Some(target) = target_slots.and_then(|t| t.first()) {
            self.set_scope(*target, self.symbol_table.current_scope());
            *target
        } else {
            self.push_dummy(span)
        }
    }

    fn count_semantic_nodes(&self, node_ref: ParsedNodeRef) -> usize {
        let node = self.parsed_ast.get_node(node_ref);
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
            // Handle struct/union from parsed types
            let is_definition = members.is_some();
            let type_ref = resolve_record_tag(ctx, *tag, *is_union, is_definition, span)?;

            // Now handle members if it's a definition
            if let Some(members_range) = members {
                // Get the parsed members first to avoid borrowing conflicts
                let parsed_members: Vec<_> = ctx.parsed_ast.parsed_types.get_struct_members(*members_range).to_vec();

                // Process member types separately to avoid borrowing conflicts
                let mut member_types = Vec::new();
                for parsed_member in &parsed_members {
                    let member_type_ref = convert_to_qual_type(ctx, parsed_member.ty, span)?;
                    member_types.push(member_type_ref);
                }

                // Now create struct members with the processed types
                let mut struct_members = Vec::new();
                let mut seen_names = HashMap::new();

                for (i, parsed_member) in parsed_members.iter().enumerate() {
                    if let Some(name) = parsed_member.name {
                        if let Some(&first_def) = seen_names.get(&name) {
                            ctx.report_error(SemanticError::DuplicateMember {
                                name,
                                span: parsed_member.span,
                                first_def,
                            });
                        } else {
                            seen_names.insert(name, parsed_member.span);
                        }
                    }

                    struct_members.push(StructMember {
                        name: parsed_member.name,
                        member_type: member_types[i],
                        bit_field_size: parsed_member.bit_field_size,
                        span: parsed_member.span,
                    });
                }

                complete_record_symbol(ctx, *tag, type_ref, struct_members)?;
            }

            Ok(QualType::unqualified(type_ref))
        }
        ParsedBaseTypeNode::Enum { tag, enumerators } => {
            // Handle enum from parsed types
            let is_definition = enumerators.is_some();
            let type_ref = resolve_enum_tag(ctx, *tag, is_definition, span)?;

            // Process enumerators if it's a definition
            if let Some(enum_range) = enumerators {
                let parsed_enums = ctx.parsed_ast.parsed_types.get_enum_constants(*enum_range);
                let mut next_value = 0i64;
                let mut enumerators_list = Vec::new();

                for parsed_enum in parsed_enums {
                    let value = parsed_enum.value.unwrap_or(next_value);
                    next_value = value + 1;

                    let enum_constant = EnumConstant {
                        name: parsed_enum.name,
                        value,
                        span: parsed_enum.span,
                    };
                    enumerators_list.push(enum_constant);

                    // Register constant in symbol table
                    let _ = ctx
                        .symbol_table
                        .define_enum_constant(parsed_enum.name, value, type_ref, parsed_enum.span);
                }

                complete_enum_symbol(ctx, *tag, type_ref, enumerators_list)?;
            }

            Ok(QualType::unqualified(type_ref))
        }
        ParsedBaseTypeNode::Typedef(name) => {
            // Lookup typedef in symbol table
            if let Some((entry_ref, _scope_id)) = ctx.symbol_table.lookup_symbol(*name) {
                let entry = ctx.symbol_table.get_symbol(entry_ref);
                if let SymbolKind::Typedef { aliased_type } = entry.kind {
                    Ok(aliased_type)
                } else {
                    // Get the kind of the symbol as a string for the error message
                    let kind_string = format!("{:?}", entry.kind);
                    let found_kind_str = kind_string.split_whitespace().next().unwrap_or("symbol");
                    Err(SemanticError::TypeMismatch {
                        expected: "a typedef name".to_string(),
                        found: format!("a {}", found_kind_str.to_lowercase()),
                        span,
                    })
                }
            } else {
                // Typedef not found during semantic lowering - this is expected
                // when typedefs are defined later in the same scope.
                Ok(QualType::unqualified(ctx.registry.declare_record(Some(*name), false)))
            }
        }
        ParsedBaseTypeNode::Error => {
            // Create an error type
            Ok(QualType::unqualified(ctx.registry.type_error))
        }
    }
}

/// Convert a ParsedType to a TypeRef
fn convert_to_qual_type(
    ctx: &mut LowerCtx,
    parsed_type: ParsedType,
    span: SourceSpan,
) -> Result<QualType, SemanticError> {
    let base_type_node = {
        // borrow immutable hanya di dalam block ini
        let parsed_types = &ctx.parsed_ast.parsed_types;
        parsed_types.get_base_type(parsed_type.base)
    };

    let declarator_ref = parsed_type.declarator;
    let qualifiers = parsed_type.qualifiers;

    let base_type_ref = convert_parsed_base_type_to_qual_type(ctx, &base_type_node, span)?;

    let final_type = apply_parsed_declarator_recursive(base_type_ref, declarator_ref, ctx);
    Ok(ctx.registry.merge_qualifiers(final_type, qualifiers))
}

/// Helper to resolve struct/union tags (lookup, forward decl, or definition validation)
fn resolve_record_tag(
    ctx: &mut LowerCtx,
    tag: Option<NameId>,
    is_union: bool,
    is_definition: bool,
    span: SourceSpan,
) -> Result<TypeRef, SemanticError> {
    let existing_entry = tag.and_then(|tag_name| ctx.symbol_table.lookup_tag(tag_name));

    if let Some(tag_name) = tag {
        // Named struct/union
        if is_definition {
            // This is a DEFINITION: struct T { ... }
            let in_current_scope =
                existing_entry.is_some_and(|(_, scope_id)| scope_id == ctx.symbol_table.current_scope());

            if in_current_scope {
                let (entry_ref, _) = existing_entry.unwrap();
                let (is_completed, first_def, ty) = {
                    let entry = ctx.symbol_table.get_symbol(entry_ref);
                    (entry.is_completed, entry.def_span, entry.type_info.ty())
                };

                if is_completed {
                    // Redeclaration error
                    ctx.report_error(SemanticError::Redefinition {
                        name: tag_name,
                        first_def,
                        span,
                    });
                    Ok(ty)
                } else {
                    // Completing a forward declaration in current scope
                    Ok(ty)
                }
            } else {
                // Not in current scope (either not found or shadowing outer)
                // Create a new record type
                let new_type_ref = ctx.registry.declare_record(Some(tag_name), is_union);

                // Add it to the symbol table in the current scope
                ctx.symbol_table.define_record(tag_name, new_type_ref, false, span);
                Ok(new_type_ref)
            }
        } else {
            // This is a USAGE or FORWARD DECL: struct T; or struct T s;
            if let Some((entry_ref, _)) = existing_entry {
                // Found existing (either in current or outer scope)
                let entry = ctx.symbol_table.get_symbol(entry_ref);
                Ok(entry.type_info.ty())
            } else {
                // Not found anywhere, create an implicit forward declaration in current scope
                let forward_ref = ctx.registry.declare_record(Some(tag_name), is_union);

                ctx.symbol_table.define_record(tag_name, forward_ref, false, span);
                Ok(forward_ref)
            }
        }
    } else {
        // Anonymous struct/union definition
        Ok(ctx.registry.declare_record(None, is_union))
    }
}

/// Helper to resolve enum tags
fn resolve_enum_tag(
    ctx: &mut LowerCtx,
    tag: Option<NameId>,
    is_definition: bool,
    span: SourceSpan,
) -> Result<TypeRef, SemanticError> {
    let existing_entry = tag.and_then(|tag_name| ctx.symbol_table.lookup_tag(tag_name));

    if let Some(tag_name) = tag {
        if is_definition {
            // This is a DEFINITION: enum T { ... };
            if let Some((entry_ref, scope_id)) = existing_entry
                && scope_id == ctx.symbol_table.current_scope()
            {
                // Found in current scope, check if completed
                let (is_completed, first_def, type_info) = {
                    let entry = ctx.symbol_table.get_symbol(entry_ref);
                    (entry.is_completed, entry.def_span, entry.type_info)
                };
                if is_completed {
                    ctx.report_error(SemanticError::Redefinition {
                        name: tag_name,
                        first_def,
                        span,
                    });
                }
                Ok(type_info.ty())
            } else {
                // Not found in current scope, create new entry
                let new_type_ref = ctx.registry.declare_enum(Some(tag_name), ctx.registry.type_int);
                ctx.symbol_table.define_enum(tag_name, new_type_ref, span);
                Ok(new_type_ref)
            }
        } else {
            // This is a USAGE or FORWARD DECL: enum T; or enum T e;
            if let Some((entry_ref, _)) = existing_entry {
                let entry = ctx.symbol_table.get_symbol(entry_ref);
                Ok(entry.type_info.ty())
            } else {
                // Implicit forward declaration
                let forward_ref = ctx.registry.declare_enum(Some(tag_name), ctx.registry.type_int);

                ctx.symbol_table.define_enum(tag_name, forward_ref, span);
                Ok(forward_ref)
            }
        }
    } else {
        // Anonymous enum definition
        Ok(ctx.registry.declare_enum(None, ctx.registry.type_int))
    }
}

fn complete_record_symbol(
    ctx: &mut LowerCtx,
    tag: Option<NameId>,
    type_ref: TypeRef,
    members: Vec<StructMember>,
) -> Result<(), SemanticError> {
    // Update the type in AST and SymbolTable
    ctx.registry.complete_record(type_ref, members.clone());
    ctx.registry.ensure_layout(type_ref)?;

    if let Some(tag_name) = tag
        && let Some((entry_ref, _)) = ctx.symbol_table.lookup_tag(tag_name)
    {
        let entry = ctx.symbol_table.get_symbol_mut(entry_ref);
        entry.is_completed = true;
        if let SymbolKind::Record {
            is_complete,
            members: entry_members,
            ..
        } = &mut entry.kind
        {
            *is_complete = true;
            *entry_members = members; // This is now the original value
        }
    }
    Ok(())
}

fn complete_enum_symbol(
    ctx: &mut LowerCtx,
    tag: Option<NameId>,
    type_ref: TypeRef,
    enumerators: Vec<EnumConstant>,
) -> Result<(), SemanticError> {
    // Update the type in AST and SymbolTable using the proper completion function
    ctx.registry.complete_enum(type_ref, enumerators);
    ctx.registry.ensure_layout(type_ref)?;

    if let Some(tag_name) = tag
        && let Some((entry_ref, _)) = ctx.symbol_table.lookup_tag(tag_name)
    {
        let entry = ctx.symbol_table.get_symbol_mut(entry_ref);
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
    match ts {
        ParsedTypeSpecifier::Void => Ok(QualType::unqualified(ctx.registry.type_void)),
        ParsedTypeSpecifier::Char => Ok(QualType::unqualified(ctx.registry.type_char)),
        ParsedTypeSpecifier::Short => Ok(QualType::unqualified(ctx.registry.type_short)),
        ParsedTypeSpecifier::Int => Ok(QualType::unqualified(ctx.registry.type_int)),
        ParsedTypeSpecifier::Long => Ok(QualType::unqualified(ctx.registry.type_long)),
        ParsedTypeSpecifier::LongLong => Ok(QualType::unqualified(ctx.registry.type_long_long)),
        ParsedTypeSpecifier::Float => Ok(QualType::unqualified(ctx.registry.type_float)),
        ParsedTypeSpecifier::Double => Ok(QualType::unqualified(ctx.registry.type_double)),
        ParsedTypeSpecifier::LongDouble => Ok(QualType::unqualified(ctx.registry.type_long_double)),
        ParsedTypeSpecifier::Signed => {
            // Signed modifier
            Ok(QualType::unqualified(ctx.registry.type_signed))
        }
        ParsedTypeSpecifier::Unsigned => {
            // Unsigned modifier - return a special marker type that will be handled in merge_base_type
            Ok(QualType::unqualified(ctx.registry.type_int_unsigned))
        }
        ParsedTypeSpecifier::Bool => Ok(QualType::unqualified(ctx.registry.type_bool)),
        ParsedTypeSpecifier::Complex => {
            // Complex types need a base type
            // For now, default to complex double
            let complex_type = ctx.registry.complex_type(ctx.registry.type_double);
            Ok(QualType::unqualified(complex_type))
        }
        ParsedTypeSpecifier::Atomic(parsed_type) => {
            // Convert the ParsedType to a TypeRef by applying the declarator to the base type
            convert_to_qual_type(ctx, *parsed_type, span)
        }
        ParsedTypeSpecifier::Record(is_union, tag, definition) => {
            // ... resolve_record_tag works same args ...
            let is_definition = definition.is_some();
            let type_ref = resolve_record_tag(ctx, *tag, *is_union, is_definition, span)?;

            // Now handle members if it's a definition
            if let Some(def) = definition {
                // def is ParsedRecordDefData. members is Option<Vec<ParsedDeclarationData>>.
                // lower_struct_members expects Vec<ParsedDeclarationData>?
                // It expects &[DeclarationData] before.
                // I need to update lower_struct_members as well.
                let members = def
                    .members
                    .as_ref()
                    .map(|decls| lower_struct_members(decls, ctx, span))
                    .unwrap_or_default();

                complete_record_symbol(ctx, *tag, type_ref, members)?;
            }

            Ok(QualType::unqualified(type_ref))
        }
        ParsedTypeSpecifier::Enum(tag, enumerators) => {
            let is_definition = enumerators.is_some();
            let type_ref_to_use = resolve_enum_tag(ctx, *tag, is_definition, span)?;

            // 2. Process enumerators if it's a definition
            if let Some(enums) = enumerators {
                let mut next_value = 0i64;
                let mut enumerators_list = Vec::new();

                for &enum_ref in enums {
                    // Get node from PARSED ast
                    let enum_node = ctx.parsed_ast.get_node(enum_ref);
                    if let ParsedNodeKind::EnumConstant(name, value_expr_ref) = &enum_node.kind {
                        let value = if let Some(v_ref) = value_expr_ref {
                            let expr_ref = ctx.lower_expression(*v_ref);
                            let const_ctx = ConstEvalCtx {
                                ast: ctx.ast,
                                symbol_table: ctx.symbol_table,
                            };
                            if let Some(val) = const_eval::eval_const_expr(&const_ctx, expr_ref) {
                                val
                            } else {
                                ctx.report_error(SemanticError::NonConstantInitializer { span: enum_node.span });
                                0
                            }
                        } else {
                            next_value
                        };
                        next_value = value + 1;

                        let enum_constant = EnumConstant {
                            name: *name,
                            value,
                            span: enum_node.span,
                        };
                        enumerators_list.push(enum_constant);

                        // Register constant in symbol table
                        if let Err(SymbolTableError::InvalidRedefinition { existing, .. }) = ctx
                            .symbol_table
                            .define_enum_constant(*name, value, type_ref_to_use, enum_node.span)
                        {
                            let first_def = ctx.symbol_table.get_symbol(existing).def_span;
                            ctx.report_error(SemanticError::Redefinition {
                                name: *name,
                                first_def,
                                span: enum_node.span,
                            });
                        }
                    }
                }

                complete_enum_symbol(ctx, *tag, type_ref_to_use, enumerators_list)?;
            }

            Ok(QualType::unqualified(type_ref_to_use))
        }
        ParsedTypeSpecifier::TypedefName(name) => {
            // Lookup typedef in symbol table
            if let Some((entry_ref, _scope_id)) = ctx.symbol_table.lookup_symbol(*name) {
                let entry = ctx.symbol_table.get_symbol(entry_ref);
                if let SymbolKind::Typedef { aliased_type } = entry.kind {
                    Ok(aliased_type)
                } else {
                    let kind_string = format!("{:?}", entry.kind);
                    let found_kind_str = kind_string.split_whitespace().next().unwrap_or("symbol");
                    Err(SemanticError::ExpectedTypedefName {
                        found: format!("a {}", found_kind_str.to_lowercase()),
                        span,
                    })
                }
            } else {
                Ok(QualType::unqualified(ctx.registry.declare_record(Some(*name), false)))
            }
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
    match existing {
        None => Some(new_type),
        Some(existing_ref) => {
            let existing_type = ctx.registry.get(existing_ref.ty());
            let new_type_info = ctx.registry.get(new_type.ty());

            match (&existing_type.kind, &new_type_info.kind) {
                (TypeKind::Builtin(existing_builtin), TypeKind::Builtin(new_builtin)) => {
                    match (existing_builtin, new_builtin) {
                        // 1. Same types (redundancy)
                        (a, b) if a == b => {
                            // C99/C11: int int is NOT allowed, but long long is.
                            // However, many compilers allow redundant specifiers.
                            // In Cendol, we'll allow it for now if they are identical,
                            // EXCEPT for types that already have a combined form (like long long).
                            if *a == BuiltinType::Long {
                                Some(QualType::unqualified(ctx.registry.type_long_long))
                            } else {
                                Some(existing_ref)
                            }
                        }

                        // 2. Handle Signed as a modifier
                        (BuiltinType::Signed, BuiltinType::Int) => Some(new_type),
                        (BuiltinType::Int, BuiltinType::Signed) => Some(existing_ref),

                        (BuiltinType::Signed, BuiltinType::Char) => {
                            Some(QualType::unqualified(ctx.registry.type_schar))
                        }
                        (BuiltinType::Char, BuiltinType::Signed) => {
                            Some(QualType::unqualified(ctx.registry.type_schar))
                        }

                        (BuiltinType::Signed, BuiltinType::Short) => Some(new_type),
                        (BuiltinType::Short, BuiltinType::Signed) => Some(existing_ref),

                        (BuiltinType::Signed, BuiltinType::Long) => Some(new_type),
                        (BuiltinType::Long, BuiltinType::Signed) => Some(existing_ref),

                        (BuiltinType::Signed, BuiltinType::LongLong) => Some(new_type),
                        (BuiltinType::LongLong, BuiltinType::Signed) => Some(existing_ref),

                        // 3. Unsigned overrides signed/marker
                        (BuiltinType::Int, BuiltinType::UInt) => Some(new_type),
                        (BuiltinType::UInt, BuiltinType::Int) => Some(existing_ref),

                        (BuiltinType::Signed, BuiltinType::UInt) => Some(new_type),
                        (BuiltinType::UInt, BuiltinType::Signed) => Some(existing_ref),

                        // Char + Unsigned -> UChar
                        (BuiltinType::Char, BuiltinType::UInt) => {
                            Some(QualType::unqualified(ctx.registry.type_char_unsigned))
                        }
                        (BuiltinType::UInt, BuiltinType::Char) => {
                            Some(QualType::unqualified(ctx.registry.type_char_unsigned))
                        }

                        // Short + Unsigned -> UShort
                        (BuiltinType::Short, BuiltinType::UInt) => {
                            Some(QualType::unqualified(ctx.registry.type_short_unsigned))
                        }
                        (BuiltinType::UInt, BuiltinType::Short) => {
                            Some(QualType::unqualified(ctx.registry.type_short_unsigned))
                        }

                        // Long + Unsigned -> ULong
                        (BuiltinType::Long, BuiltinType::UInt) => {
                            Some(QualType::unqualified(ctx.registry.type_long_unsigned))
                        }
                        (BuiltinType::UInt, BuiltinType::Long) => {
                            Some(QualType::unqualified(ctx.registry.type_long_unsigned))
                        }

                        // LongLong + Unsigned -> ULongLong
                        (BuiltinType::LongLong, BuiltinType::UInt) => {
                            Some(QualType::unqualified(ctx.registry.type_long_long_unsigned))
                        }
                        (BuiltinType::UInt, BuiltinType::LongLong) => {
                            Some(QualType::unqualified(ctx.registry.type_long_long_unsigned))
                        }

                        // 4. Redundant 'int' combined with other specifiers
                        (BuiltinType::Short, BuiltinType::Int) => Some(existing_ref),
                        (BuiltinType::Int, BuiltinType::Short) => Some(new_type),
                        (BuiltinType::UShort, BuiltinType::Int) => Some(existing_ref),
                        (BuiltinType::Int, BuiltinType::UShort) => Some(new_type),

                        (BuiltinType::Long, BuiltinType::Int) => Some(existing_ref),
                        (BuiltinType::Int, BuiltinType::Long) => Some(new_type),
                        (BuiltinType::ULong, BuiltinType::Int) => Some(existing_ref),
                        (BuiltinType::Int, BuiltinType::ULong) => Some(new_type),

                        (BuiltinType::LongLong, BuiltinType::Int) => Some(existing_ref),
                        (BuiltinType::Int, BuiltinType::LongLong) => Some(new_type),
                        (BuiltinType::ULongLong, BuiltinType::Int) => Some(existing_ref),
                        (BuiltinType::Int, BuiltinType::ULongLong) => Some(new_type),

                        // 5. Long + Long -> LongLong (handled by case 1 above partially, but let's be explicit if needed)
                        // (BuiltinType::Long, BuiltinType::Long) is already handled in case 1.

                        // Long + LongLong -> LongLong
                        (BuiltinType::Long, BuiltinType::LongLong) => Some(new_type),
                        (BuiltinType::LongLong, BuiltinType::Long) => Some(existing_ref),

                        // ULong + Long -> ULongLong
                        (BuiltinType::ULong, BuiltinType::Long) => {
                            Some(QualType::unqualified(ctx.registry.type_long_long_unsigned))
                        }
                        (BuiltinType::Long, BuiltinType::ULong) => {
                            Some(QualType::unqualified(ctx.registry.type_long_long_unsigned))
                        }

                        // Long + ULongLong -> ULongLong
                        (BuiltinType::Long, BuiltinType::ULongLong) => Some(new_type),
                        (BuiltinType::ULongLong, BuiltinType::Long) => Some(existing_ref),

                        // Long + Double -> LongDouble
                        (BuiltinType::Double, BuiltinType::Long) => {
                            Some(QualType::unqualified(ctx.registry.type_long_double))
                        }
                        (BuiltinType::Long, BuiltinType::Double) => {
                            Some(QualType::unqualified(ctx.registry.type_long_double))
                        }

                        // Error for other combinations (e.g. double int)
                        _ => {
                            ctx.report_error(SemanticError::ConflictingTypeSpecifiers {
                                prev: ctx.registry.display_qual_type(existing_ref),
                                span,
                            });
                            Some(QualType::unqualified(ctx.registry.type_error))
                        }
                    }
                }
                _ => {
                    ctx.report_error(SemanticError::ConflictingTypeSpecifiers {
                        prev: ctx.registry.display_qual_type(existing_ref),
                        span,
                    });
                    Some(QualType::unqualified(ctx.registry.type_error))
                }
            }
        }
    }
}

/// Validate specifier combinations for semantic correctness
fn validate_specifier_combinations(info: &DeclSpecInfo, ctx: &mut LowerCtx, span: SourceSpan) {
    // Check typedef with other storage classes
    if info.is_typedef && (info.storage.is_some_and(|s| s != StorageClass::Typedef) || info.is_thread_local) {
        ctx.report_error(SemanticError::ConflictingStorageClasses { span });
    }

    // _Thread_local constraints (C11 6.7.1p3)
    if info.is_thread_local {
        // Can only be used alone or with static/extern
        if let Some(s) = info.storage
            && s != StorageClass::Static
            && s != StorageClass::Extern
        {
            ctx.report_error(SemanticError::ConflictingStorageClasses { span });
        }
    }

    // Check for missing required specifiers (type specifier)
    if info.base_type.is_none() {
        ctx.report_error(SemanticError::MissingTypeSpecifier { span });
    }
}

/// Parse and validate declaration specifiers
pub(crate) fn lower_decl_specifiers(
    specs: &[ParsedDeclSpecifier],
    ctx: &mut LowerCtx,
    span: SourceSpan,
) -> DeclSpecInfo {
    let mut info = DeclSpecInfo::default();

    for spec in specs {
        match spec {
            ParsedDeclSpecifier::StorageClass(sc) => {
                if *sc == StorageClass::ThreadLocal {
                    if info.is_thread_local {
                        // duplicate _Thread_local
                        ctx.report_error(SemanticError::ConflictingStorageClasses { span });
                    }
                    info.is_thread_local = true;
                } else {
                    if info.storage.is_some() {
                        ctx.report_error(SemanticError::ConflictingStorageClasses { span });
                    }
                    if *sc == StorageClass::Typedef {
                        info.is_typedef = true;
                    }
                    info.storage = Some(*sc);
                }
            }
            ParsedDeclSpecifier::TypeQualifier(tq) => {
                let mask = match tq {
                    TypeQualifier::Const => TypeQualifiers::CONST,
                    TypeQualifier::Volatile => TypeQualifiers::VOLATILE,
                    TypeQualifier::Restrict => TypeQualifiers::RESTRICT,
                    TypeQualifier::Atomic => TypeQualifiers::ATOMIC,
                };
                info.qualifiers.insert(mask);
            }
            ParsedDeclSpecifier::TypeSpecifier(ts) => {
                let ty = resolve_type_specifier(ts, ctx, span).unwrap_or_else(|e| {
                    ctx.report_error(e);
                    QualType::unqualified(ctx.registry.type_error)
                });
                info.base_type = merge_base_type(info.base_type, ty, ctx, span);
            }
            ParsedDeclSpecifier::AlignmentSpecifier(align) => {
                let align_val = match align {
                    crate::ast::parsed::ParsedAlignmentSpecifier::Type(parsed_ty) => {
                        let qt = convert_to_qual_type(ctx, *parsed_ty, span)
                            .unwrap_or(QualType::unqualified(ctx.registry.type_error));
                        match ctx.registry.ensure_layout(qt.ty()) {
                            Ok(layout) => layout.alignment as u32,
                            Err(e) => {
                                ctx.report_error(e);
                                0
                            }
                        }
                    }
                    crate::ast::parsed::ParsedAlignmentSpecifier::Expr(expr_ref) => {
                        let lowered_expr = ctx.lower_expression(*expr_ref);
                        let const_ctx = ConstEvalCtx {
                            ast: ctx.ast,
                            symbol_table: ctx.symbol_table,
                        };
                        if let Some(val) = const_eval::eval_const_expr(&const_ctx, lowered_expr) {
                            if val < 0 {
                                ctx.report_error(SemanticError::InvalidAlignment { value: val, span });
                                0
                            } else {
                                val as u32
                            }
                        } else {
                            ctx.report_error(SemanticError::NonConstantAlignment { span });
                            0
                        }
                    }
                };

                if align_val != 0 {
                    if !align_val.is_power_of_two() {
                        ctx.report_error(SemanticError::InvalidAlignment {
                            value: align_val as i64,
                            span,
                        });
                    } else {
                        info.alignment = Some(std::cmp::max(info.alignment.unwrap_or(0), align_val));
                    }
                }
            }
            ParsedDeclSpecifier::FunctionSpecifier(fs) => match fs {
                FunctionSpecifier::Inline => info.is_inline = true,
                FunctionSpecifier::Noreturn => info.is_noreturn = true,
            },
            ParsedDeclSpecifier::Attribute => {
                // Ignore attributes for now
            }
        }
    }

    // Finalize base type: 'signed' without anything else defaults to 'int'
    if let Some(base) = info.base_type
        && base.ty() == ctx.registry.type_signed
    {
        info.base_type = Some(QualType::unqualified(ctx.registry.type_int));
    }

    validate_specifier_combinations(&info, ctx, span);
    info
}

fn lower_function_parameters(params: &[ParsedParamData], ctx: &mut LowerCtx) -> Vec<FunctionParameter> {
    params
        .iter()
        .map(|param| {
            let span = param.span;
            let spec_info = lower_decl_specifiers(&param.specifiers, ctx, span);

            // C standard: if type specifier is missing in a parameter, it defaults to int.
            let mut base_ty = spec_info
                .base_type
                .unwrap_or_else(|| QualType::unqualified(ctx.registry.type_int));
            base_ty = ctx.registry.merge_qualifiers(base_ty, spec_info.qualifiers);

            let final_ty = if let Some(declarator) = &param.declarator {
                apply_declarator(base_ty, declarator, ctx, span)
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
            FunctionParameter {
                param_type: decayed_ty,
                name: pname,
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
                Some(lower_function_parameters(params, ctx))
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
pub(crate) fn apply_declarator(
    base_type: QualType,
    declarator: &ParsedDeclarator,
    ctx: &mut LowerCtx,
    span: SourceSpan,
) -> QualType {
    match declarator {
        ParsedDeclarator::Pointer(qualifiers, next) => {
            let ty = ctx.registry.pointer_to(base_type);
            let modified_ty = ctx.registry.merge_qualifiers(QualType::unqualified(ty), *qualifiers);
            if let Some(next_decl) = next {
                apply_declarator(modified_ty, next_decl, ctx, span)
            } else {
                modified_ty
            }
        }
        ParsedDeclarator::Identifier(_, qualifiers) => ctx.registry.merge_qualifiers(base_type, *qualifiers),
        ParsedDeclarator::Array(base, size) => {
            // C11 6.7.6.2 Array declarators
            // "The element type shall not be an incomplete or function type."
            if !ctx.registry.is_complete(base_type.ty()) || base_type.ty().is_function() {
                let ty_str = ctx.registry.display_type(base_type.ty());
                ctx.report_error(SemanticError::IncompleteType { ty: ty_str, span });
            }

            let array_size = match size {
                ParsedArraySize::Expression { expr, qualifiers: _ } => resolve_array_size(Some(*expr), ctx),
                ParsedArraySize::Star { qualifiers: _ } => ArraySizeType::Star,
                ParsedArraySize::Incomplete => ArraySizeType::Incomplete,
                ParsedArraySize::VlaSpecifier {
                    is_static: _,
                    qualifiers: _,
                    size,
                } => resolve_array_size(*size, ctx),
            };

            let ty = ctx.registry.array_of(base_type.ty(), array_size);
            let array_qt = QualType::new(ty, base_type.qualifiers());
            apply_declarator(array_qt, base, ctx, span)
        }
        ParsedDeclarator::Function {
            inner: base,
            params,
            is_variadic,
        } => {
            let parameters = lower_function_parameters(params, ctx);
            let ty = ctx.registry.function_type(base_type.ty(), parameters, *is_variadic);
            apply_declarator(QualType::unqualified(ty), base, ctx, span)
        }
        ParsedDeclarator::AnonymousRecord(is_union, members) => {
            // Use struct_lowering helper
            let ty = ctx.registry.declare_record(None, *is_union);
            let struct_members = lower_struct_members(members, ctx, SourceSpan::empty());
            ctx.registry.complete_record(ty, struct_members);
            let _ = ctx.registry.ensure_layout(ty);
            QualType::unqualified(ty)
        }
        ParsedDeclarator::BitField(base, _) => {
            // Bitfield logic handled in struct lowering usually. Here just type application.
            apply_declarator(base_type, base, ctx, span)
        }
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
pub(crate) fn run_semantic_lowering(
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
    lower_ctx.lower_node(root);
}

impl<'a, 'src> LowerCtx<'a, 'src> {
    pub(crate) fn lower_node(&mut self, parsed_ref: ParsedNodeRef) -> SmallVec<[NodeRef; 1]> {
        self.lower_node_entry(parsed_ref, None)
    }

    fn lower_node_entry(
        &mut self,
        parsed_ref: ParsedNodeRef,
        target_slots: Option<&[NodeRef]>,
    ) -> SmallVec<[NodeRef; 1]> {
        let parsed_node = self.parsed_ast.get_node(parsed_ref);
        let span = parsed_node.span;
        let kind = parsed_node.kind.clone();

        match kind {
            ParsedNodeKind::TranslationUnit(children) => {
                self.symbol_table.set_current_scope(ScopeId::GLOBAL);

                // Reserve slot for TranslationUnit
                let tu_node = self.push_dummy(span);

                // 1. First pass: count how many semantic nodes each child will produce
                let mut semantic_node_counts = Vec::new();
                let mut total_semantic_nodes = 0;

                for &child_ref in &children {
                    let child = self.parsed_ast.get_node(child_ref);
                    let count = match &child.kind {
                        ParsedNodeKind::FunctionDef(..) => 1,
                        ParsedNodeKind::Declaration(decl) => {
                            if !decl.init_declarators.is_empty() {
                                decl.init_declarators.len()
                            } else if let Some(spec) = decl.specifiers.iter().find_map(|s| {
                                if let ParsedDeclSpecifier::TypeSpecifier(ts) = s {
                                    Some(ts)
                                } else {
                                    None
                                }
                            }) {
                                match spec {
                                    ParsedTypeSpecifier::Record(_, _, is_def) if is_def.is_some() => 1,
                                    ParsedTypeSpecifier::Enum(_, is_def) if is_def.is_some() => 1,
                                    _ => 0, // Empty declaration or no definition side effects
                                }
                            } else {
                                0
                            }
                        }
                        ParsedNodeKind::StaticAssert(..) => 1,
                        _ => 0, // Should not happen for top-level nodes ideally
                    };
                    semantic_node_counts.push(count);
                    total_semantic_nodes += count;
                }

                // 2. Reserve contiguous slots for all top-level nodes
                let decl_len = total_semantic_nodes as u16;
                let mut reserved_slots = Vec::new();
                for _ in 0..decl_len {
                    reserved_slots.push(self.push_dummy(span));
                }

                // 3. Second pass: Lower children into reserved slots
                let mut current_slot_idx = 0;
                for (i, child_ref) in children.iter().enumerate() {
                    let count = semantic_node_counts[i];
                    if count == 0 {
                        continue;
                    }

                    let target_slots = &reserved_slots[current_slot_idx..current_slot_idx + count];
                    self.lower_top_level_node(*child_ref, target_slots);
                    current_slot_idx += count;
                }

                let decl_start = if decl_len > 0 { reserved_slots[0] } else { NodeRef::ROOT };

                self.ast.kinds[tu_node.index()] = NodeKind::TranslationUnit(TranslationUnitData {
                    decl_start,
                    decl_len,
                    scope_id: ScopeId::GLOBAL,
                });

                smallvec![tu_node]
            }
            ParsedNodeKind::CompoundStatement(stmts) => {
                let scope_id = self.symbol_table.push_scope();

                // Use target slot if provided, otherwise reserve new slot
                // Note: We set scope AFTER push_scope since CompoundStatement creates a new scope
                let node = self.get_or_push_slot(target_slots, span);

                // Count total semantic nodes
                let mut total_stmt_nodes = 0;
                for stmt_ref in stmts.iter().copied() {
                    total_stmt_nodes += self.count_semantic_nodes(stmt_ref);
                }

                // Reserve slots for all statements
                let mut stmt_slots = Vec::new();
                for _ in 0..total_stmt_nodes {
                    stmt_slots.push(self.push_dummy(span));
                }

                let stmt_start = if !stmt_slots.is_empty() {
                    stmt_slots[0]
                } else {
                    NodeRef::ROOT
                };
                let stmt_len = stmt_slots.len() as u16;

                // Lower statements directly into reserved slots
                let mut current_slot_idx = 0;
                for stmt_ref in stmts {
                    let count = self.count_semantic_nodes(stmt_ref);
                    if count > 0 {
                        let target_slots = &stmt_slots[current_slot_idx..current_slot_idx + count];
                        self.lower_node_entry(stmt_ref, Some(target_slots));
                        current_slot_idx += count;
                    }
                }

                self.symbol_table.pop_scope();

                // Replace dummy node with actual CompoundStatement
                self.ast.kinds[node.index()] = NodeKind::CompoundStatement(CompoundStmtData {
                    stmt_start,
                    stmt_len,
                    scope_id,
                });

                smallvec![node]
            }
            ParsedNodeKind::Declaration(decl_data) => self.lower_declaration(&decl_data, span, target_slots),
            ParsedNodeKind::FunctionDef(func_def) => {
                let node = self.get_or_push_slot(target_slots, span);
                self.lower_function_definition(&func_def, node, span);
                smallvec![node]
            }
            // ... other top level kinds ...
            _ => self.lower_node_rest(parsed_ref, target_slots),
        }
    }

    fn lower_top_level_node(&mut self, parsed_ref: ParsedNodeRef, target_slots: &[NodeRef]) {
        let parsed_node = self.parsed_ast.get_node(parsed_ref);
        let span = parsed_node.span;

        match &parsed_node.kind {
            ParsedNodeKind::Declaration(decl) => {
                self.lower_declaration(decl, span, Some(target_slots));
            }
            ParsedNodeKind::FunctionDef(func_def) => {
                if let Some(target) = target_slots.first() {
                    self.lower_function_definition(func_def, *target, span);
                }
            }
            _ => {
                if let ParsedNodeKind::StaticAssert(expr, msg) = &parsed_node.kind
                    && let Some(target) = target_slots.first()
                {
                    let lowered_expr = self.lower_expression(*expr);
                    self.ast.kinds[target.index()] = NodeKind::StaticAssert(lowered_expr, *msg);
                    self.set_scope(*target, self.symbol_table.current_scope());
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
    ) {
        if let Some((existing_ref, existing_scope)) = self.symbol_table.lookup_symbol(name) {
            let current_scope = self.symbol_table.current_scope();
            let existing = self.symbol_table.get_symbol(existing_ref);

            let is_global = current_scope == ScopeId::GLOBAL;
            let is_func = new_ty.is_function();
            let new_has_linkage = is_global || storage == Some(StorageClass::Extern) || is_func;

            // Linkage conflict if:
            // 1. Same scope (always conflict)
            // 2. Both have linkage (even different scope)
            let is_conflict = (existing_scope == current_scope) || (new_has_linkage && existing.has_linkage());

            if is_conflict {
                if !self.registry.is_compatible(existing.type_info, new_ty) {
                    let first_def = existing.def_span;
                    self.report_error(SemanticError::ConflictingTypes {
                        name: name.to_string(),
                        span,
                        first_def,
                    });
                } else if new_ty.is_function() {
                    // Check for linkage conflict (static followed by non-static)
                    if let SymbolKind::Function {
                        storage: existing_storage,
                    } = &existing.kind
                    {
                        let existing_is_static = *existing_storage == Some(StorageClass::Static);
                        let new_is_static = storage == Some(StorageClass::Static);

                        if existing_is_static && !new_is_static {
                            let first_def = existing.def_span;
                            self.report_error(SemanticError::ConflictingLinkage {
                                name: name.to_string(),
                                span,
                                first_def,
                            });
                        }
                    }
                }
            }
        }
    }

    fn lower_function_definition(&mut self, func_def: &ParsedFunctionDefData, node: NodeRef, span: SourceSpan) {
        let spec_info = lower_decl_specifiers(&func_def.specifiers, self, span);
        let mut base_ty = spec_info
            .base_type
            .unwrap_or_else(|| QualType::unqualified(self.registry.type_int));
        base_ty = self.registry.merge_qualifiers(base_ty, spec_info.qualifiers);

        let final_ty = apply_declarator(base_ty, &func_def.declarator, self, span);
        let func_name = extract_name(&func_def.declarator).expect("Function definition must have a name");

        self.check_redeclaration_compatibility(func_name, final_ty, span, spec_info.storage);

        if let Err(crate::semantic::symbol_table::SymbolTableError::InvalidRedefinition { existing, .. }) = self
            .symbol_table
            .define_function(func_name, final_ty.ty(), spec_info.storage, true, span)
        {
            let entry = self.symbol_table.get_symbol(existing);
            if entry.def_state == DefinitionState::Defined {
                let first_def = entry.def_span;
                self.report_error(SemanticError::Redefinition {
                    name: func_name,
                    first_def,
                    span,
                });
            }
        }
        let func_sym_ref = self.symbol_table.lookup_symbol(func_name).map(|(s, _)| s).unwrap();

        let scope_id = self.symbol_table.push_scope();

        // Pre-scan labels for forward goto support
        self.collect_labels(func_def.body);

        let parameters = get_definition_params(&func_def.declarator, self).unwrap_or_default();

        let param_len = parameters.len() as u16;
        let mut param_dummies = Vec::new();
        for _ in 0..param_len {
            param_dummies.push(self.push_dummy(span));
        }

        for (i, param) in parameters.iter().enumerate() {
            if let Some(pname) = param.name
                && let Ok(sym) = self
                    .symbol_table
                    .define_variable(pname, param.param_type, None, None, None, span)
            {
                let param_ref = param_dummies[i];
                self.ast.kinds[param_ref.index()] = NodeKind::Param(ParamData {
                    symbol: sym,
                    ty: param.param_type,
                });
                self.set_scope(param_ref, self.symbol_table.current_scope());
            }
        }

        let param_start = if param_len > 0 { param_dummies[0] } else { NodeRef::ROOT };

        self.set_scope(node, self.symbol_table.current_scope());

        let body_node = self.lower_single_statement(func_def.body);

        self.symbol_table.pop_scope();

        self.ast.kinds[node.index()] = NodeKind::Function(FunctionData {
            symbol: func_sym_ref,
            ty: final_ty.ty(),
            param_start,
            param_len,
            body: body_node,
            scope_id,
        });
    }

    fn lower_declaration(
        &mut self,
        decl: &ParsedDeclarationData,
        span: SourceSpan,
        target_slots: Option<&[NodeRef]>,
    ) -> SmallVec<[NodeRef; 1]> {
        let spec_info = lower_decl_specifiers(&decl.specifiers, self, span);
        let mut base_ty = spec_info
            .base_type
            .unwrap_or(QualType::unqualified(self.registry.type_int));
        base_ty = self.registry.merge_qualifiers(base_ty, spec_info.qualifiers);

        if decl.init_declarators.is_empty() {
            if let Some(ty) = spec_info.base_type {
                // Extract needed data from registry to avoid borrowing self.registry during node creation
                let type_data = match &self.registry.get(ty.ty()).kind {
                    TypeKind::Record {
                        tag, members, is_union, ..
                    } => Some(TypeData::Record(*tag, members.clone(), *is_union)),
                    TypeKind::Enum { tag, enumerators, .. } => Some(TypeData::Enum(*tag, enumerators.clone())),
                    _ => None,
                };

                if let Some(data) = type_data {
                    let node = if let Some(slots) = target_slots {
                        slots.first().copied().unwrap_or_else(|| self.push_dummy(span))
                    } else {
                        self.push_dummy(span)
                    };

                    match data {
                        TypeData::Record(tag, members, is_union) => {
                            let mut member_len = 0u16;
                            let member_start_idx = self.ast.kinds.len() as u32 + 1;
                            let member_start = NodeRef::new(member_start_idx).expect("NodeRef overflow");

                            for m in members {
                                let field_node = self.ast.push_node(
                                    NodeKind::FieldDecl(FieldDeclData {
                                        name: m.name,
                                        ty: m.member_type,
                                    }),
                                    m.span,
                                );
                                self.set_scope(field_node, self.symbol_table.current_scope());
                                member_len += 1;
                            }

                            self.ast.kinds[node.index()] = NodeKind::RecordDecl(RecordDeclData {
                                name: tag,
                                ty: ty.ty(),
                                member_start,
                                member_len,
                                is_union,
                            });
                        }
                        TypeData::Enum(tag, enumerators) => {
                            let mut member_start = NodeRef::ROOT;
                            let member_len = enumerators.len() as u16;

                            for (i, e) in enumerators.iter().enumerate() {
                                let member_ref = self.ast.push_node(
                                    NodeKind::EnumMember(EnumMemberData {
                                        name: e.name,
                                        value: e.value,
                                    }),
                                    e.span,
                                );
                                self.set_scope(member_ref, self.symbol_table.current_scope());
                                if i == 0 {
                                    member_start = member_ref;
                                }
                            }

                            self.ast.kinds[node.index()] = NodeKind::EnumDecl(EnumDeclData {
                                name: tag,
                                ty: ty.ty(),
                                member_start,
                                member_len,
                            });
                        }
                    }
                    return smallvec![node];
                }
            }
            return smallvec![];
        }

        enum TypeData {
            Record(Option<NameId>, Vec<StructMember>, bool),
            Enum(Option<NameId>, Vec<EnumConstant>),
        }

        let mut nodes = SmallVec::new();

        for (i, init) in decl.init_declarators.iter().enumerate() {
            let final_ty = apply_declarator(base_ty, &init.declarator, self, init.span);

            let name = extract_name(&init.declarator).expect("Declarator must have identifier");

            let node = if let Some(slots) = target_slots {
                slots[i]
            } else {
                self.push_dummy(span)
            };
            self.set_scope(node, self.symbol_table.current_scope());

            if spec_info.is_typedef {
                if let Err(_e) = self.symbol_table.define_typedef(name, final_ty, span) {
                    self.report_error(SemanticError::Redefinition {
                        name,
                        first_def: span,
                        span,
                    });
                }
                self.ast.kinds[node.index()] = NodeKind::TypedefDecl(TypedefDeclData { name, ty: final_ty });
                nodes.push(node);
                continue;
            }

            let init_expr = init.initializer.map(|init_node| self.lower_expression(init_node));

            let is_func = final_ty.is_function();

            // Validate function specifiers (inline, _Noreturn)
            if !is_func {
                if spec_info.is_inline {
                    self.report_error(SemanticError::InvalidFunctionSpecifier {
                        spec: "inline".to_string(),
                        span,
                    });
                }
                if spec_info.is_noreturn {
                    self.report_error(SemanticError::InvalidFunctionSpecifier {
                        spec: "_Noreturn".to_string(),
                        span,
                    });
                }
            }

            if is_func {
                let func_decl = FunctionDeclData {
                    name,
                    ty: final_ty.ty(),
                    storage: spec_info.storage,
                    body: None,
                    scope_id: self.symbol_table.current_scope(),
                };
                self.check_redeclaration_compatibility(name, final_ty, span, spec_info.storage);

                if let Err(crate::semantic::symbol_table::SymbolTableError::InvalidRedefinition { existing, .. }) = self
                    .symbol_table
                    .define_function(name, final_ty.ty(), spec_info.storage, false, span)
                {
                    let first_def = self.symbol_table.get_symbol(existing).def_span;
                    self.report_error(SemanticError::Redefinition { name, first_def, span });
                }
                self.ast.kinds[node.index()] = NodeKind::FunctionDecl(func_decl);
                nodes.push(node);
            } else {
                let mut final_ty = final_ty;
                if let Some(ie) = init_expr
                    && let TypeKind::Array {
                        element_type,
                        size: ArraySizeType::Incomplete,
                    } = &self.registry.get(final_ty.ty()).kind
                {
                    let element_type = *element_type;
                    if let Some(deduced_size) = self.deduce_array_size_full(ie) {
                        let new_ty = self
                            .registry
                            .array_of(element_type, ArraySizeType::Constant(deduced_size));
                        final_ty = QualType::new(new_ty, final_ty.qualifiers());
                    }
                }

                let var_decl = VarDeclData {
                    name,
                    ty: final_ty,
                    storage: spec_info.storage,
                    init: init_expr,
                    alignment: spec_info.alignment.map(|a| a as u16),
                };
                self.check_redeclaration_compatibility(name, final_ty, span, spec_info.storage);

                if let Err(SymbolTableError::InvalidRedefinition { existing, .. }) = self.symbol_table.define_variable(
                    name,
                    final_ty,
                    spec_info.storage,
                    init_expr,
                    spec_info.alignment,
                    span,
                ) {
                    let first_def = self.symbol_table.get_symbol(existing).def_span;
                    self.report_error(SemanticError::Redefinition { name, first_def, span });
                }

                // Important: Ensure layout for variable definitions
                if self.registry.ensure_layout(final_ty.ty()).is_err() {
                    // Swallow error here - get_layout will panic or we can't do much.
                    // But for valid C code like 'int a[]', this fails.
                    // However, we only need layout if it's used.
                    // If we access it, get_layout panics.
                    // This ensure_layout call helps caching layout early and catching ICEs early if possible.
                    // But for 'extern int a[];', it returns error. We shouldn't error out.
                    // Just ignore error.
                }

                self.ast.kinds[node.index()] = NodeKind::VarDecl(var_decl);
                nodes.push(node);
            }
        }
        nodes
    }

    fn lower_node_rest(
        &mut self,
        parsed_ref: ParsedNodeRef,
        target_slots: Option<&[NodeRef]>,
    ) -> SmallVec<[NodeRef; 1]> {
        let parsed_node = self.parsed_ast.get_node(parsed_ref);
        let span = parsed_node.span;
        match &parsed_node.kind {
            ParsedNodeKind::Declaration(decl) => self.lower_declaration(decl, span, target_slots),
            ParsedNodeKind::StaticAssert(expr, msg) => {
                let node = self.get_or_push_slot(target_slots, span);
                let lowered_expr = self.lower_expression(*expr);
                self.ast.kinds[node.index()] = NodeKind::StaticAssert(lowered_expr, *msg);
                smallvec![node]
            }
            ParsedNodeKind::If(stmt) => {
                let node = self.get_or_push_slot(target_slots, span);
                let cond = self.lower_expression(stmt.condition);
                let then = self.lower_single_statement(stmt.then_branch);
                let else_branch = stmt.else_branch.map(|b| self.lower_single_statement(b));
                self.ast.kinds[node.index()] = NodeKind::If(IfStmt {
                    condition: cond,
                    then_branch: then,
                    else_branch,
                });
                smallvec![node]
            }
            ParsedNodeKind::While(stmt) => {
                let node = self.get_or_push_slot(target_slots, span);
                let cond = self.lower_expression(stmt.condition);
                let body = self.lower_single_statement(stmt.body);
                self.ast.kinds[node.index()] = NodeKind::While(WhileStmt { condition: cond, body });
                smallvec![node]
            }
            ParsedNodeKind::DoWhile(body, cond) => {
                let node = self.get_or_push_slot(target_slots, span);
                let b = self.lower_single_statement(*body);
                let c = self.lower_expression(*cond);
                self.ast.kinds[node.index()] = NodeKind::DoWhile(b, c);
                smallvec![node]
            }
            ParsedNodeKind::For(stmt) => {
                let node = self.get_or_push_slot(target_slots, span);
                let scope_id = self.symbol_table.push_scope();
                self.set_scope(node, scope_id);

                let init = stmt.init.map(|i| self.lower_node(i).first().cloned().unwrap());
                let cond = stmt.condition.map(|c| self.lower_expression(c));
                let inc = stmt.increment.map(|i| self.lower_expression(i));
                let body = self.lower_single_statement(stmt.body);
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
                let c = self.lower_expression(*cond);
                let b = self.lower_single_statement(*body);
                self.ast.kinds[node.index()] = NodeKind::Switch(c, b);
                smallvec![node]
            }
            ParsedNodeKind::Case(expr, stmt) => {
                let node = self.get_or_push_slot(target_slots, span);
                let e = self.lower_expression(*expr);
                let s = self.lower_single_statement(*stmt);
                self.ast.kinds[node.index()] = NodeKind::Case(e, s);
                smallvec![node]
            }
            ParsedNodeKind::CaseRange(start, end, stmt) => {
                let node = self.get_or_push_slot(target_slots, span);
                let s_expr = self.lower_expression(*start);
                let e_expr = self.lower_expression(*end);
                let s_stmt = self.lower_single_statement(*stmt);
                self.ast.kinds[node.index()] = NodeKind::CaseRange(s_expr, e_expr, s_stmt);
                smallvec![node]
            }
            ParsedNodeKind::Default(stmt) => {
                let node = self.get_or_push_slot(target_slots, span);
                let s = self.lower_single_statement(*stmt);
                self.ast.kinds[node.index()] = NodeKind::Default(s);
                smallvec![node]
            }
            ParsedNodeKind::Break => {
                let node = if let Some(target) = target_slots.and_then(|t| t.first()) {
                    self.ast.kinds[target.index()] = NodeKind::Break;
                    self.ast.spans[target.index()] = span;
                    *target
                } else {
                    self.ast.push_node(NodeKind::Break, span)
                };
                self.set_scope(node, self.symbol_table.current_scope());
                smallvec![node]
            }
            ParsedNodeKind::Continue => {
                let node = if let Some(target) = target_slots.and_then(|t| t.first()) {
                    self.ast.kinds[target.index()] = NodeKind::Continue;
                    self.ast.spans[target.index()] = span;
                    *target
                } else {
                    self.ast.push_node(NodeKind::Continue, span)
                };
                self.set_scope(node, self.symbol_table.current_scope());
                smallvec![node]
            }
            ParsedNodeKind::Goto(name) => {
                let sym = self.resolve_label(*name, span);
                let node = if let Some(target) = target_slots.and_then(|t| t.first()) {
                    self.ast.kinds[target.index()] = NodeKind::Goto(*name, sym);
                    self.ast.spans[target.index()] = span;
                    *target
                } else {
                    self.ast.push_node(NodeKind::Goto(*name, sym), span)
                };
                self.set_scope(node, self.symbol_table.current_scope());
                smallvec![node]
            }
            ParsedNodeKind::Label(name, inner) => {
                let node = self.get_or_push_slot(target_slots, span);
                let sym = self.define_label(*name, span);
                let s = self.lower_single_statement(*inner);
                self.ast.kinds[node.index()] = NodeKind::Label(*name, s, sym);
                smallvec![node]
            }
            ParsedNodeKind::Return(expr) => {
                let node = self.get_or_push_slot(target_slots, span);
                let e = expr.map(|x| self.lower_expression(x));
                self.ast.kinds[node.index()] = NodeKind::Return(e);
                smallvec![node]
            }
            ParsedNodeKind::ExpressionStatement(expr) => {
                let node = self.get_or_push_slot(target_slots, span);
                let e = expr.map(|x| self.lower_expression(x));
                self.ast.kinds[node.index()] = NodeKind::ExpressionStatement(e);
                smallvec![node]
            }
            ParsedNodeKind::BinaryOp(op, lhs, rhs) => {
                let node = self.get_or_push_slot(target_slots, span);
                let l = self.lower_expression(*lhs);
                let r = self.lower_expression(*rhs);
                self.ast.kinds[node.index()] = NodeKind::BinaryOp(*op, l, r);
                smallvec![node]
            }
            ParsedNodeKind::Assignment(op, lhs, rhs) => {
                let node = self.get_or_push_slot(target_slots, span);
                let l = self.lower_expression(*lhs);
                let r = self.lower_expression(*rhs);
                self.ast.kinds[node.index()] = NodeKind::Assignment(*op, l, r);
                smallvec![node]
            }
            ParsedNodeKind::UnaryOp(op, operand) => {
                let node = self.get_or_push_slot(target_slots, span);
                let o = self.lower_expression(*operand);
                self.ast.kinds[node.index()] = NodeKind::UnaryOp(*op, o);
                smallvec![node]
            }
            ParsedNodeKind::LiteralInt(val) => {
                let node = if let Some(target) = target_slots.and_then(|t| t.first()) {
                    self.ast.kinds[target.index()] = NodeKind::LiteralInt(*val);
                    self.ast.spans[target.index()] = span;
                    *target
                } else {
                    self.ast.push_node(NodeKind::LiteralInt(*val), span)
                };
                smallvec![node]
            }
            ParsedNodeKind::LiteralFloat(val) => {
                let node = if let Some(target) = target_slots.and_then(|t| t.first()) {
                    self.ast.kinds[target.index()] = NodeKind::LiteralFloat(*val);
                    self.ast.spans[target.index()] = span;
                    *target
                } else {
                    self.ast.push_node(NodeKind::LiteralFloat(*val), span)
                };
                smallvec![node]
            }
            ParsedNodeKind::LiteralChar(val) => {
                let node = if let Some(target) = target_slots.and_then(|t| t.first()) {
                    self.ast.kinds[target.index()] = NodeKind::LiteralChar(*val);
                    self.ast.spans[target.index()] = span;
                    *target
                } else {
                    self.ast.push_node(NodeKind::LiteralChar(*val), span)
                };
                smallvec![node]
            }
            ParsedNodeKind::LiteralString(val) => {
                let node = if let Some(target) = target_slots.and_then(|t| t.first()) {
                    self.ast.kinds[target.index()] = NodeKind::LiteralString(*val);
                    self.ast.spans[target.index()] = span;
                    *target
                } else {
                    self.ast.push_node(NodeKind::LiteralString(*val), span)
                };
                smallvec![node]
            }
            ParsedNodeKind::Ident(name) => {
                let sym = self.resolve_ident(*name, span);
                let node = if let Some(target) = target_slots.and_then(|t| t.first()) {
                    self.ast.kinds[target.index()] = NodeKind::Ident(*name, sym);
                    self.ast.spans[target.index()] = span;
                    *target
                } else {
                    self.ast.push_node(NodeKind::Ident(*name, sym), span)
                };
                smallvec![node]
            }
            ParsedNodeKind::FunctionCall(func, args) => {
                // Reserve a slot for the FunctionCall node to ensure parent < child index (when necessary)
                // If we have a target slot for the result, we can use it directly?
                // But FunctionCall needs to know ranges of args.
                // The structure is: CallNode -> FuncExpr, Arg1, Arg2...
                // FuncExpr and Args can be anywhere, but Args must be contiguous.

                let call_node_idx = self.get_or_push_slot(target_slots, span);

                let f = self.lower_expression(*func);

                // Reserve slots for arguments to ensure contiguity
                let mut arg_dummies = Vec::with_capacity(args.len());
                for _ in 0..args.len() {
                    arg_dummies.push(self.push_dummy(span));
                }

                // Lower arguments into reserved slots
                for (i, &arg_parsed_ref) in args.iter().enumerate() {
                    self.lower_expression_into(arg_parsed_ref, arg_dummies[i]);
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
                let b = self.lower_expression(*base);
                self.ast.kinds[node.index()] = NodeKind::MemberAccess(b, *member, *is_arrow);
                smallvec![node]
            }
            ParsedNodeKind::Cast(ty_name, expr) => {
                let node = self.get_or_push_slot(target_slots, span);
                let e = self.lower_expression(*expr);
                let ty = convert_to_qual_type(self, *ty_name, span)
                    .unwrap_or(QualType::unqualified(self.registry.type_error));
                self.ast.kinds[node.index()] = NodeKind::Cast(ty, e);
                smallvec![node]
            }
            ParsedNodeKind::PostIncrement(operand) => {
                let node = self.get_or_push_slot(target_slots, span);
                let o = self.lower_expression(*operand);
                self.ast.kinds[node.index()] = NodeKind::PostIncrement(o);
                smallvec![node]
            }
            ParsedNodeKind::PostDecrement(operand) => {
                let node = self.get_or_push_slot(target_slots, span);
                let o = self.lower_expression(*operand);
                self.ast.kinds[node.index()] = NodeKind::PostDecrement(o);
                smallvec![node]
            }
            ParsedNodeKind::IndexAccess(base, index) => {
                let node = self.get_or_push_slot(target_slots, span);
                let b = self.lower_expression(*base);
                let i = self.lower_expression(*index);
                self.ast.kinds[node.index()] = NodeKind::IndexAccess(b, i);
                smallvec![node]
            }
            ParsedNodeKind::TernaryOp(cond, then_branch, else_branch) => {
                let node = self.get_or_push_slot(target_slots, span);
                let c = self.lower_expression(*cond);
                let t = self.lower_expression(*then_branch);
                let e = self.lower_expression(*else_branch);
                self.ast.kinds[node.index()] = NodeKind::TernaryOp(c, t, e);
                smallvec![node]
            }
            ParsedNodeKind::GnuStatementExpression(stmt, expr) => {
                let node = self.get_or_push_slot(target_slots, span);
                let s = self.lower_expression(*stmt);
                let e = self.lower_expression(*expr);
                self.ast.kinds[node.index()] = NodeKind::GnuStatementExpression(s, e);
                smallvec![node]
            }
            ParsedNodeKind::SizeOfExpr(expr) => {
                let node = self.get_or_push_slot(target_slots, span);
                let e = self.lower_expression(*expr);
                self.ast.kinds[node.index()] = NodeKind::SizeOfExpr(e);
                smallvec![node]
            }
            ParsedNodeKind::SizeOfType(ty_name) => {
                let node = if let Some(target) = target_slots.and_then(|t| t.first()) {
                    let ty = convert_to_qual_type(self, *ty_name, span)
                        .unwrap_or(QualType::unqualified(self.registry.type_error));
                    self.ast.kinds[target.index()] = NodeKind::SizeOfType(ty);
                    self.ast.spans[target.index()] = span;
                    *target
                } else {
                    let ty = convert_to_qual_type(self, *ty_name, span)
                        .unwrap_or(QualType::unqualified(self.registry.type_error));
                    self.ast.push_node(NodeKind::SizeOfType(ty), span)
                };
                smallvec![node]
            }
            ParsedNodeKind::AlignOf(ty_name) => {
                let node = if let Some(target) = target_slots.and_then(|t| t.first()) {
                    let ty = convert_to_qual_type(self, *ty_name, span)
                        .unwrap_or(QualType::unqualified(self.registry.type_error));
                    self.ast.kinds[target.index()] = NodeKind::AlignOf(ty);
                    self.ast.spans[target.index()] = span;
                    *target
                } else {
                    let ty = convert_to_qual_type(self, *ty_name, span)
                        .unwrap_or(QualType::unqualified(self.registry.type_error));
                    self.ast.push_node(NodeKind::AlignOf(ty), span)
                };
                smallvec![node]
            }
            ParsedNodeKind::CompoundLiteral(ty_name, init) => {
                let node = self.get_or_push_slot(target_slots, span);
                let ty = convert_to_qual_type(self, *ty_name, span)
                    .unwrap_or(QualType::unqualified(self.registry.type_error));
                let i = self.lower_expression(*init);
                self.ast.kinds[node.index()] = NodeKind::CompoundLiteral(ty, i);
                smallvec![node]
            }
            ParsedNodeKind::GenericSelection(control, associations) => {
                let node = self.get_or_push_slot(target_slots, span);
                let c = self.lower_expression(*control);

                let assoc_len = associations.len() as u16;
                let mut assoc_dummies = Vec::new();
                for _ in 0..assoc_len {
                    assoc_dummies.push(self.push_dummy(span));
                }

                for (i, a) in associations.iter().enumerate() {
                    let ty = a.type_name.map(|t| {
                        convert_to_qual_type(self, t, span).unwrap_or(QualType::unqualified(self.registry.type_error))
                    });
                    let expr = self.lower_expression(a.result_expr);
                    let assoc_ref = assoc_dummies[i];
                    self.ast.kinds[assoc_ref.index()] =
                        NodeKind::GenericAssociation(GenericAssociationData { ty, result_expr: expr });
                    self.set_scope(assoc_ref, self.symbol_table.current_scope());
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
                    let expr = self.lower_expression(init.initializer);

                    let designator_count = init.designation.len() as u16;
                    let mut designator_dummies = Vec::with_capacity(designator_count as usize);

                    for _ in 0..designator_count {
                        designator_dummies.push(self.push_dummy(span));
                    }

                    for (j, d) in init.designation.iter().enumerate() {
                        let node_kind = match d {
                            ParsedDesignator::FieldName(name) => Designator::FieldName(*name),
                            ParsedDesignator::ArrayIndex(idx) => Designator::ArrayIndex(self.lower_expression(*idx)),
                            ParsedDesignator::GnuArrayRange(start, end) => {
                                Designator::GnuArrayRange(self.lower_expression(*start), self.lower_expression(*end))
                            }
                        };
                        let d_ref = designator_dummies[j];
                        self.ast.kinds[d_ref.index()] = NodeKind::Designator(node_kind);
                        // Designators don't really have scopes, but we can set it to current
                        self.set_scope(d_ref, self.symbol_table.current_scope());
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

                    let item_ref = init_dummies[i];
                    self.ast.kinds[item_ref.index()] = NodeKind::InitializerItem(di);
                    self.set_scope(item_ref, self.symbol_table.current_scope());
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

    pub(crate) fn lower_expression(&mut self, node: ParsedNodeRef) -> NodeRef {
        match self.lower_node(node).first().cloned() {
            Some(n) => n,
            None => self.push_dummy(SourceSpan::default()),
        }
    }

    pub(crate) fn lower_expression_into(&mut self, node: ParsedNodeRef, target: NodeRef) -> NodeRef {
        match self.lower_node_entry(node, Some(&[target])).first().cloned() {
            Some(n) => n,
            None => target, // Should not happen if node lowering respects target
        }
    }

    pub(crate) fn lower_single_statement(&mut self, node: ParsedNodeRef) -> NodeRef {
        self.lower_node(node)
            .first()
            .cloned()
            .unwrap_or_else(|| self.push_dummy(SourceSpan::default()))
    }

    fn resolve_ident(&mut self, name: NameId, span: SourceSpan) -> SymbolRef {
        if let Some((sym_ref, _)) = self.symbol_table.lookup_symbol(name) {
            sym_ref
        } else {
            self.report_error(SemanticError::UndeclaredIdentifier { name, span });
            SymbolRef::new(1).expect("SymbolRef 1 creation failed")
        }
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
        if let Some((sym_ref, _)) = self.symbol_table.lookup_label(name) {
            sym_ref
        } else {
            // Forward references are okay because of pre-scan
            // But if NOT even in pre-scan, then it's undeclared
            self.report_error(SemanticError::UndeclaredIdentifier { name, span });
            SymbolRef::new(1).unwrap()
        }
    }

    fn collect_labels(&mut self, node: ParsedNodeRef) {
        let parsed_node = self.parsed_ast.get_node(node);
        match &parsed_node.kind {
            ParsedNodeKind::Label(name, inner) => {
                let _ = self.define_label(*name, parsed_node.span);
                self.collect_labels(*inner);
            }
            ParsedNodeKind::CompoundStatement(stmts) => {
                for stmt in stmts {
                    self.collect_labels(*stmt);
                }
            }
            ParsedNodeKind::If(stmt) => {
                self.collect_labels(stmt.then_branch);
                if let Some(eb) = stmt.else_branch {
                    self.collect_labels(eb);
                }
            }
            ParsedNodeKind::While(stmt) => {
                self.collect_labels(stmt.body);
            }
            ParsedNodeKind::DoWhile(body, _) => {
                self.collect_labels(*body);
            }
            ParsedNodeKind::For(stmt) => {
                self.collect_labels(stmt.body);
            }
            ParsedNodeKind::Switch(_, body) => {
                self.collect_labels(*body);
            }
            ParsedNodeKind::Case(_, stmt) | ParsedNodeKind::CaseRange(_, _, stmt) | ParsedNodeKind::Default(stmt) => {
                self.collect_labels(*stmt);
            }
            _ => {}
        }
    }

    fn deduce_array_size_full(&self, init_node: NodeRef) -> Option<usize> {
        let node_kind = self.ast.get_kind(init_node);
        match node_kind {
            NodeKind::InitializerList(list_data) => {
                let mut max_index: i64 = -1;
                let mut current_index: i64 = 0;

                if list_data.init_len == 0 {
                    return Some(0);
                }

                for item_ref in list_data.init_start.range(list_data.init_len) {
                    let NodeKind::InitializerItem(init) = self.ast.get_kind(item_ref) else {
                        continue;
                    };
                    if init.designator_len > 0 {
                        let first_designator_ref = init.designator_start;
                        match self.ast.get_kind(first_designator_ref) {
                            NodeKind::Designator(d) => match d {
                                crate::ast::Designator::ArrayIndex(expr_ref) => {
                                    let const_ctx = ConstEvalCtx {
                                        ast: self.ast,
                                        symbol_table: self.symbol_table,
                                    };
                                    if let Some(val) = const_eval::eval_const_expr(&const_ctx, *expr_ref) {
                                        current_index = val;
                                    } else {
                                        return None;
                                    }
                                }
                                crate::ast::Designator::GnuArrayRange(start, end) => {
                                    let const_ctx = ConstEvalCtx {
                                        ast: self.ast,
                                        symbol_table: self.symbol_table,
                                    };
                                    if let (Some(start_val), Some(end_val)) = (
                                        const_eval::eval_const_expr(&const_ctx, *start),
                                        const_eval::eval_const_expr(&const_ctx, *end),
                                    ) {
                                        if start_val > end_val {
                                            return None;
                                        }
                                        current_index = end_val;
                                    } else {
                                        return None;
                                    }
                                }
                                crate::ast::Designator::FieldName(_) => {
                                    // Should not happen in array initializer
                                    return None;
                                }
                            },
                            _ => return None,
                        }
                    }

                    if current_index > max_index {
                        max_index = current_index;
                    }
                    current_index += 1;
                }

                if max_index >= 0 {
                    Some((max_index + 1) as usize)
                } else {
                    Some(0)
                }
            }
            NodeKind::LiteralString(name_id) => {
                let s = name_id.to_string();
                Some(s.len() + 1)
            }
            _ => None,
        }
    }
}
/// Extracts the bit-field width from a declarator if it exists.
fn extract_bit_field_width<'a>(
    declarator: &'a ParsedDeclarator,
    ctx: &mut LowerCtx,
) -> (Option<NonZeroU16>, &'a ParsedDeclarator) {
    if let ParsedDeclarator::BitField(base, expr_ref) = declarator {
        let node = ctx.parsed_ast.get_node(*expr_ref);
        let width = if let ParsedNodeKind::LiteralInt(val) = node.kind {
            if val > 0 && val <= 64 {
                // Bitfield width can be up to type width (e.g. 64)
                NonZeroU16::new(val as u16)
            } else {
                ctx.report_error(SemanticError::InvalidBitfieldWidth { span: node.span });
                None
            }
        } else {
            // Evaluator needed for non-literals.
            ctx.report_error(SemanticError::NonConstantBitfieldWidth { span: node.span });
            None
        };
        (width, base)
    } else {
        (None, declarator)
    }
}

/// Common logic for lowering struct members, used by both TypeSpecifier::Record lowering
/// and Declarator::AnonymousRecord handling.
pub(crate) fn lower_struct_members(
    members: &[ParsedDeclarationData],
    ctx: &mut LowerCtx,
    span: crate::ast::SourceSpan,
) -> Vec<StructMember> {
    let mut struct_members = Vec::new();
    let mut seen_names = HashMap::new();

    for decl in members {
        // Handle anonymous struct/union members (C11 6.7.2.1p13)
        // "An unnamed member of structure or union type with no tag is called an anonymous structure or anonymous union"
        if decl.init_declarators.is_empty() {
            let spec_info = lower_decl_specifiers(&decl.specifiers, ctx, span);

            // Check for illegal storage classes
            if spec_info.storage.is_some() {
                ctx.report_error(SemanticError::ConflictingStorageClasses { span });
            }

            if let Some(type_ref) = spec_info.base_type {
                let type_ref = ctx.registry.merge_qualifiers(type_ref, spec_info.qualifiers);

                // Check if it is a Record type (struct or union)
                if type_ref.is_record() {
                    let ty = ctx.registry.get(type_ref.ty());
                    if let TypeKind::Record { tag, .. } = &ty.kind {
                        // It must have no tag to be an anonymous member
                        if tag.is_none() {
                            struct_members.push(StructMember {
                                name: None,
                                member_type: type_ref,
                                bit_field_size: None,
                                span, // Use the parent span since DeclarationData doesn't have one
                            });
                        }
                    }
                }
            }
            continue;
        }

        // Hoist declaration specifier processing out of the loop
        let spec_info = lower_decl_specifiers(&decl.specifiers, ctx, span);

        // Check for illegal storage classes
        if spec_info.storage.is_some() {
            ctx.report_error(SemanticError::ConflictingStorageClasses { span });
        }

        for init_declarator in &decl.init_declarators {
            let (bit_field_size, base_declarator) = extract_bit_field_width(&init_declarator.declarator, ctx);

            let member_name = extract_name(base_declarator);

            if let Some(name) = member_name {
                if let Some(&first_def) = seen_names.get(&name) {
                    ctx.report_error(SemanticError::DuplicateMember {
                        name,
                        span: init_declarator.span,
                        first_def,
                    });
                } else {
                    seen_names.insert(name, init_declarator.span);
                }
            }

            let member_type = if let Some(base_type_ref) = spec_info.base_type {
                // Manually re-apply qualifiers from the base type.
                let ty = apply_declarator(base_type_ref, base_declarator, ctx, init_declarator.span);
                ctx.registry.merge_qualifiers(ty, spec_info.qualifiers)
            } else {
                QualType::unqualified(ctx.registry.type_int)
            };

            // Validate bit-field type
            if bit_field_size.is_some() && !member_type.is_integer() {
                ctx.report_error(SemanticError::InvalidBitfieldType {
                    ty: ctx.registry.display_qual_type(member_type),
                    span: init_declarator.span,
                });
            }

            struct_members.push(StructMember {
                name: member_name,
                member_type,
                bit_field_size,
                span: init_declarator.span,
            });
        }
    }
    struct_members
}
