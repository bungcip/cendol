//! SymbolResolver
//!
//! Responsibility
//! - Declaration Lowering (Declaration -> VarDecl/RecordDecl/EnumDecl/TypedefDecl, FunctionDef -> Function)
//! - Scope Construction
//! - Symbol Insertion to Symbol Table
//! - Making Sure Struct with body is is_complete = true
//!
//! This module implements the semantic lowering phase that bridges the gap between the
//! grammar-oriented parser AST and the type-resolved semantic AST (HIR). The lowering
//! phase handles all C-style declaration forms

use crate::ast::*;
use crate::diagnostic::{DiagnosticEngine, SemanticError};
use crate::semantic::symbol_table::{DefinitionState, SymbolTableError};
use crate::semantic::type_context::QualType;
use crate::semantic::{Namespace, ScopeId, Symbol, SymbolKind, SymbolTable, TypeContext, TypeRef};
use crate::source_manager::SourceSpan;

/// Extract identifier name from ParsedType declarator
fn extract_identifier_from_parsed_type(parsed_type: &ParsedType, ctx: &LowerCtx) -> Option<NameId> {
    extract_identifier_from_parsed_declarator_recursive(parsed_type.declarator, ctx)
}

/// Recursively extract identifier from parsed declarator
fn extract_identifier_from_parsed_declarator_recursive(
    declarator_ref: ParsedDeclRef,
    ctx: &LowerCtx,
) -> Option<NameId> {
    match ctx.ast.parsed_types.get_decl(declarator_ref) {
        ParsedDeclaratorNode::Identifier { name } => {
            // This is an identifier node with the actual name
            name
        }
        ParsedDeclaratorNode::Pointer { inner, .. } => {
            // Look inside the pointer for the identifier
            extract_identifier_from_parsed_declarator_recursive(inner, ctx)
        }
        ParsedDeclaratorNode::Array { inner, .. } => {
            // Look inside the array for the identifier
            extract_identifier_from_parsed_declarator_recursive(inner, ctx)
        }
        ParsedDeclaratorNode::Function { inner, .. } => {
            // Look inside the function for the identifier
            extract_identifier_from_parsed_declarator_recursive(inner, ctx)
        }
    }
}

/// Apply ParsedType declarator to create a semantic Type
fn apply_parsed_declarator(base_type: TypeRef, parsed_type: &ParsedType, ctx: &mut LowerCtx) -> QualType {
    // Start with the base type and apply declarator transformations
    let result_type = apply_parsed_declarator_recursive(base_type, parsed_type.declarator, ctx);
    // Combine the declarator result qualifiers with the parsed type qualifiers
    let combined_qualifiers = result_type.qualifiers | parsed_type.qualifiers;
    QualType::new(result_type.ty, combined_qualifiers)
}

/// Recursively apply parsed declarator to base type
fn apply_parsed_declarator_recursive(
    base_type: TypeRef,
    declarator_ref: ParsedDeclRef,
    ctx: &mut LowerCtx,
) -> QualType {
    // Get all the data we need upfront to avoid borrowing conflicts
    let (decl_type, qualifiers, inner, size, params, flags) = {
        match ctx.ast.parsed_types.get_decl(declarator_ref) {
            ParsedDeclaratorNode::Identifier { .. } => {
                return QualType::unqualified(base_type);
            }
            ParsedDeclaratorNode::Pointer { qualifiers, inner } => (0, Some(qualifiers), Some(inner), None, None, None),
            ParsedDeclaratorNode::Array { size, inner } => (1, None, Some(inner), Some(size.clone()), None, None),
            ParsedDeclaratorNode::Function { params, flags, inner } => {
                (2, None, Some(inner), None, Some(params), Some(flags))
            }
        }
    };

    match decl_type {
        0 => {
            // Pointer
            let inner_type = apply_parsed_declarator_recursive(base_type, inner.unwrap(), ctx);
            let pointer_type = ctx.type_ctx.pointer_to(inner_type.ty);
            QualType::new(pointer_type, qualifiers.unwrap())
        }
        1 => {
            // Array
            let element_type = apply_parsed_declarator_recursive(base_type, inner.unwrap(), ctx);
            let array_size = convert_parsed_array_size(&size.unwrap(), ctx);
            let array_type_ref = ctx.type_ctx.array_of(element_type.ty, array_size);
            QualType::unqualified(array_type_ref)
        }
        2 => {
            // Function
            let return_type = apply_parsed_declarator_recursive(base_type, inner.unwrap(), ctx);
            let return_type_ref = return_type.ty;

            // Process parameters separately to avoid borrowing conflicts in the closure
            let parsed_params: Vec<_> = ctx.ast.parsed_types.get_params(params.unwrap()).to_vec();
            let mut processed_params = Vec::new();
            for param in parsed_params {
                let param_type = convert_parsed_type_to_qual_type(ctx, param.ty, param.span).unwrap_or_else(|_|
                    // Create an error type if conversion fails
                    QualType::unqualified(ctx.type_ctx.type_int));
                processed_params.push(FunctionParameter {
                    param_type,
                    name: param.name,
                });
            }

            let function_type_ref =
                ctx.type_ctx
                    .function_type(return_type_ref, processed_params, flags.unwrap().is_variadic);
            QualType::unqualified(function_type_ref)
        }
        _ => {
            // This should never happen
            QualType::unqualified(base_type)
        }
    }
}

/// Convert ParsedArraySize to ArraySizeType
fn convert_parsed_array_size(size: &ParsedArraySize, _ctx: &mut LowerCtx) -> ArraySizeType {
    match size {
        ParsedArraySize::Expression { expr_ref: _, .. } => {
            // For now, treat as incomplete since we don't have expression evaluation
            ArraySizeType::Incomplete
        }
        ParsedArraySize::Star { .. } => ArraySizeType::Star,
        ParsedArraySize::Incomplete => ArraySizeType::Incomplete,
    }
}

/// Context for the semantic lowering phase
pub struct LowerCtx<'a, 'src> {
    pub ast: &'a mut Ast,
    pub diag: &'src mut DiagnosticEngine,
    pub symbol_table: &'a mut SymbolTable,
    pub scope_map: Vec<Option<ScopeId>>,
    // Track errors during lowering for early termination
    pub has_errors: bool,
    pub type_ctx: &'a mut TypeContext,
}

/// Evaluate a constant expression node to an i64 value
fn eval_const_expr(ctx: &LowerCtx, expr_node_ref: NodeRef) -> Option<i64> {
    let node = ctx.ast.get_node(expr_node_ref);
    match &node.kind {
        NodeKind::LiteralInt(val) => Some(*val),
        NodeKind::BinaryOp(op, left_ref, right_ref) => {
            let left_val = eval_const_expr(ctx, *left_ref)?;
            let right_val = eval_const_expr(ctx, *right_ref)?;
            match op {
                BinaryOp::Add => Some(left_val + right_val),
                BinaryOp::Sub => Some(left_val - right_val),
                BinaryOp::Mul => Some(left_val * right_val),
                BinaryOp::Div => Some(left_val / right_val),
                // TODO: Add other binary operations as needed
                _ => None,
            }
        }
        _ => None,
    }
}

impl<'a, 'src> LowerCtx<'a, 'src> {
    /// Create a new lowering context
    pub fn new(
        ast: &'a mut Ast,
        diag: &'src mut DiagnosticEngine,
        symbol_table: &'a mut SymbolTable,
        type_ctx: &'a mut TypeContext,
    ) -> Self {
        Self {
            ast,
            diag,
            symbol_table,
            scope_map: Vec::new(),
            has_errors: false,
            type_ctx,
        }
    }

    /// Report a semantic error and mark context as having errors
    pub fn report_error(&mut self, error: SemanticError) {
        self.has_errors = true;
        self.diag.report(error);
    }

    /// Check if the context has any errors
    pub fn has_errors(&self) -> bool {
        self.has_errors
    }

    fn set_scope(&mut self, node_ref: NodeRef, scope_id: ScopeId) {
        self.scope_map[(node_ref.get() - 1) as usize] = Some(scope_id);
    }
}

/// Information about declaration specifiers after processing
#[derive(Debug, Clone, Default)]
pub struct DeclSpecInfo {
    pub storage: Option<StorageClass>,
    pub qualifiers: TypeQualifiers,
    pub base_type: Option<QualType>,
    pub is_typedef: bool,
    pub is_inline: bool,
    pub is_noreturn: bool,
}

/// Main entry point for lowering a declaration
/// Returns a vector of semantic nodes (one for each declarator)
pub fn lower_declaration(ctx: &mut LowerCtx, decl_node: NodeRef) -> Vec<NodeRef> {
    // Get the declaration data from the AST node
    let (declaration_span, decl) = {
        let decl_node_data = ctx.ast.get_node(decl_node);
        let span = decl_node_data.span;
        let declaration_data = match &decl_node_data.kind {
            NodeKind::Declaration(d) => d.clone(),
            _ => unreachable!("Expected Declaration node"),
        };
        (span, declaration_data)
    };

    // Handle declarations with 0 init_declarators (type definitions)
    if decl.init_declarators.is_empty() {
        let type_def_node = lower_type_definition(&decl.specifiers, ctx, declaration_span);
        if let Some(type_def_node_ref) = type_def_node {
            return vec![type_def_node_ref];
        } else {
            return Vec::new();
        }
    }

    // 1. Parse and validate declaration specifiers
    let spec = lower_decl_specifiers(&decl.specifiers, ctx, declaration_span);

    // If we have errors in specifiers, return empty vector
    if ctx.has_errors() {
        return Vec::new();
    }

    // 2. Process init-declarators into semantic nodes
    let semantic_nodes: Vec<NodeRef> = decl
        .init_declarators
        .into_iter()
        .map(|init| lower_init_declarator(ctx, &spec, init, declaration_span))
        .collect();

    semantic_nodes
}

/// Process declaration specifiers into consolidated information
fn lower_decl_specifiers(specs: &[DeclSpecifier], ctx: &mut LowerCtx, span: SourceSpan) -> DeclSpecInfo {
    let mut info = DeclSpecInfo::default();

    for spec in specs {
        match spec {
            DeclSpecifier::StorageClass(sc) => {
                // Check for duplicate storage class
                if info.storage.replace(*sc).is_some() {
                    ctx.report_error(SemanticError::MultipleStorageClasses { span });
                }

                // Handle typedef storage class
                if *sc == StorageClass::Typedef {
                    info.is_typedef = true;
                }
            }

            DeclSpecifier::TypeQualifiers(q) => {
                info.qualifiers |= *q;
            }

            DeclSpecifier::TypeSpecifier(ts) => {
                let ty = resolve_type_specifier(ts, ctx, span).unwrap_or_else(|e| {
                    ctx.report_error(e);
                    QualType::unqualified(ctx.type_ctx.type_error)
                });
                info.base_type = merge_base_type(info.base_type, ty, ctx);
            }

            DeclSpecifier::FunctionSpecifiers(fs) => {
                if fs.contains(FunctionSpecifiers::INLINE) {
                    info.is_inline = true;
                }
                if fs.contains(FunctionSpecifiers::NORETURN) {
                    info.is_noreturn = true;
                }
            }

            DeclSpecifier::AlignmentSpecifier(_) => {
                // TODO: Handle alignment specifiers
            }

            DeclSpecifier::Attribute => {
                // TODO: Handle attributes
            }
        }
    }

    // Validate specifier combinations
    validate_specifier_combinations(&info, ctx, span);

    info
}

/// Convert a ParsedBaseTypeNode to a QualType
fn convert_parsed_base_type_to_qual_type(
    ctx: &mut LowerCtx,
    parsed_base: &ParsedBaseTypeNode,
    span: SourceSpan,
) -> Result<QualType, SemanticError> {
    match parsed_base {
        ParsedBaseTypeNode::Builtin(ts) => resolve_type_specifier(ts, ctx, span),
        ParsedBaseTypeNode::Struct { tag, members, is_union } => {
            // Handle struct/union from parsed types
            let existing_entry = tag.and_then(|tag_name| ctx.symbol_table.lookup_tag(tag_name));

            let type_ref_to_use = if let Some(tag_name) = tag {
                // Named struct/union
                if members.is_some() {
                    // This is a DEFINITION: struct T { ... }
                    let in_current_scope =
                        existing_entry.is_some_and(|(_, scope_id)| scope_id == ctx.symbol_table.current_scope());

                    if in_current_scope {
                        let (entry_ref, _) = existing_entry.unwrap();
                        let entry = ctx.symbol_table.get_symbol(entry_ref);

                        if entry.is_completed {
                            // Redeclaration error - for now just return it
                            entry.type_info
                        } else {
                            // Completing a forward declaration in current scope
                            entry.type_info
                        }
                    } else {
                        // Not in current scope (either not found or shadowing outer)
                        // Create a new record type
                        let new_type_ref = ctx.type_ctx.new_record(Some(*tag_name), *is_union);

                        // Add it to the symbol table in the current scope
                        let symbol_entry = Symbol {
                            name: *tag_name,
                            kind: SymbolKind::Record {
                                is_complete: false,
                                members: Vec::new(),
                                size: None,
                                alignment: None,
                            },
                            type_info: new_type_ref,
                            storage_class: None,
                            scope_id: ctx.symbol_table.current_scope(),
                            def_span: span,
                            def_state: DefinitionState::Defined,
                            is_referenced: false,
                            is_completed: false,
                        };
                        ctx.symbol_table
                            .add_symbol_in_namespace(*tag_name, symbol_entry, Namespace::Tag);
                        new_type_ref
                    }
                } else {
                    // This is a USAGE or FORWARD DECL: struct T; or struct T s;
                    if let Some((entry_ref, _)) = existing_entry {
                        // Found existing (either in current or outer scope)
                        let entry = ctx.symbol_table.get_symbol(entry_ref);
                        entry.type_info
                    } else {
                        // Not found anywhere, create an implicit forward declaration in current scope
                        let forward_ref = ctx.type_ctx.new_record(Some(*tag_name), *is_union);

                        let symbol_entry = Symbol {
                            name: *tag_name,
                            kind: SymbolKind::Record {
                                is_complete: false,
                                members: Vec::new(),
                                size: None,
                                alignment: None,
                            },
                            type_info: forward_ref,
                            storage_class: None,
                            scope_id: ctx.symbol_table.current_scope(),
                            def_span: span,
                            def_state: DefinitionState::Defined,
                            is_referenced: false,
                            is_completed: false,
                        };
                        ctx.symbol_table
                            .add_symbol_in_namespace(*tag_name, symbol_entry, Namespace::Tag);
                        forward_ref
                    }
                }
            } else {
                // Anonymous struct/union definition
                ctx.type_ctx.new_record(None, *is_union)
            };

            // Now handle members if it's a definition
            if let Some(members_range) = members {
                // Get the parsed members first to avoid borrowing conflicts
                let parsed_members: Vec<_> = ctx.ast.parsed_types.get_struct_members(*members_range).to_vec();

                // Process member types separately to avoid borrowing conflicts
                let mut member_types = Vec::new();
                for parsed_member in &parsed_members {
                    let member_type_ref = convert_parsed_type_to_qual_type(ctx, parsed_member.ty, span)?;
                    member_types.push(member_type_ref);
                }

                // Now create struct members with the processed types
                let mut struct_members = Vec::new();
                for (i, parsed_member) in parsed_members.iter().enumerate() {
                    struct_members.push(StructMember {
                        name: parsed_member.name,
                        member_type: member_types[i],
                        bit_field_size: parsed_member.bit_field_size.map(|size| {
                            // Convert from NonZeroU32 to NonZeroU16
                            std::num::NonZeroU16::new(size.get() as u16)
                                .unwrap_or_else(|| std::num::NonZeroU16::new(1).unwrap())
                        }),
                        span: parsed_member.span,
                    });
                }

                // Update the type in AST and SymbolTable
                ctx.type_ctx
                    .complete_record(type_ref_to_use, struct_members.clone(), None);

                if let Some(tag_name) = *tag
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
                        *entry_members = struct_members; // This is now the original value
                    }
                }
            }

            Ok(QualType::unqualified(type_ref_to_use))
        }
        ParsedBaseTypeNode::Enum { tag, enumerators } => {
            // Handle enum from parsed types
            let type_ref_to_use = if let Some(tag_name) = tag {
                let existing_entry = ctx.symbol_table.lookup_tag(*tag_name);
                if enumerators.is_some() {
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
                                name: *tag_name,
                                first_def,
                                span,
                            });
                        }
                        type_info
                    } else {
                        // Not found in current scope, create new entry
                        let new_type_ref = ctx.type_ctx.new_enum(Some(*tag_name), ctx.type_ctx.type_int);
                        let symbol_entry = Symbol {
                            name: *tag_name,
                            kind: SymbolKind::EnumTag { is_complete: false },
                            type_info: new_type_ref,
                            storage_class: None,
                            scope_id: ctx.symbol_table.current_scope(),
                            def_span: span,
                            def_state: DefinitionState::Defined,
                            is_referenced: false,
                            is_completed: false,
                        };
                        ctx.symbol_table
                            .add_symbol_in_namespace(*tag_name, symbol_entry, Namespace::Tag);
                        new_type_ref
                    }
                } else {
                    // This is a USAGE or FORWARD DECL: enum T; or enum T e;
                    if let Some((entry_ref, _)) = existing_entry {
                        let entry = ctx.symbol_table.get_symbol(entry_ref);
                        entry.type_info
                    } else {
                        // Implicit forward declaration
                        let forward_ref = ctx.type_ctx.new_enum(Some(*tag_name), ctx.type_ctx.type_int);

                        let symbol = Symbol {
                            name: *tag_name,
                            kind: SymbolKind::EnumTag { is_complete: false },
                            storage_class: None,
                            scope_id: ctx.symbol_table.current_scope(),
                            def_span: span,
                            def_state: DefinitionState::Defined,
                            type_info: forward_ref,
                            is_referenced: false,
                            is_completed: false,
                        };
                        ctx.symbol_table
                            .add_symbol_in_namespace(*tag_name, symbol, Namespace::Tag);
                        forward_ref
                    }
                }
            } else {
                // Anonymous enum definition
                ctx.type_ctx.new_enum(None, ctx.type_ctx.type_int)
            };

            // Process enumerators if it's a definition
            if let Some(enum_range) = enumerators {
                let parsed_enums = ctx.ast.parsed_types.get_enum_constants(*enum_range);
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
                    let entry = Symbol {
                        name: parsed_enum.name,
                        kind: SymbolKind::EnumConstant { value },
                        type_info: type_ref_to_use,
                        storage_class: None,
                        scope_id: ctx.symbol_table.current_scope(),
                        def_span: parsed_enum.span,
                        def_state: DefinitionState::Defined,
                        is_referenced: false,
                        is_completed: true,
                    };
                    ctx.symbol_table.add_symbol(parsed_enum.name, entry);
                }

                // Update the type in AST and SymbolTable
                let type_idx = (type_ref_to_use.get() - 1) as usize;
                let mut updated_type_kind = ctx.type_ctx.types[type_idx].kind.clone();
                if let TypeKind::Enum {
                    enumerators,
                    is_complete,
                    ..
                } = &mut updated_type_kind
                {
                    *enumerators = enumerators_list;
                    *is_complete = true;
                }
                ctx.type_ctx.types[type_idx].kind = updated_type_kind;

                if let Some(tag_name) = tag
                    && let Some((entry_ref, _)) = ctx.symbol_table.lookup_tag(*tag_name)
                {
                    let entry = ctx.symbol_table.get_symbol_mut(entry_ref);
                    entry.is_completed = true;
                    if let SymbolKind::EnumTag { is_complete } = &mut entry.kind {
                        *is_complete = true;
                    }
                }
            }

            Ok(QualType::unqualified(type_ref_to_use))
        }
        ParsedBaseTypeNode::Typedef(name) => {
            // Lookup typedef in symbol table
            if let Some((entry_ref, _scope_id)) = ctx.symbol_table.lookup_symbol(*name) {
                let entry = ctx.symbol_table.get_symbol(entry_ref);
                if let SymbolKind::Typedef { aliased_type } = entry.kind {
                    Ok(QualType::unqualified(aliased_type))
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
                Ok(QualType::unqualified(ctx.type_ctx.new_record(Some(*name), false)))
            }
        }
        ParsedBaseTypeNode::Error => {
            // Create an error type
            Ok(QualType::unqualified(ctx.type_ctx.type_error))
        }
    }
}

/// Convert a ParsedType to a TypeRef
fn convert_parsed_type_to_qual_type(
    ctx: &mut LowerCtx,
    parsed_type: ParsedType,
    span: SourceSpan,
) -> Result<QualType, SemanticError> {
    let base_type_node = {
        // borrow immutable hanya di dalam block ini
        let parsed_types = &ctx.ast.parsed_types;
        parsed_types.get_base_type(parsed_type.base)
    };

    let declarator_ref = parsed_type.declarator;
    let qualifiers = parsed_type.qualifiers;

    let base_type_ref = convert_parsed_base_type_to_qual_type(ctx, &base_type_node, span)?;

    let mut final_type = apply_parsed_declarator_recursive(base_type_ref.ty, declarator_ref, ctx);
    final_type.qualifiers |= qualifiers;

    Ok(final_type)
}

/// Resolve a type specifier to a QualType
fn resolve_type_specifier(ts: &TypeSpecifier, ctx: &mut LowerCtx, span: SourceSpan) -> Result<QualType, SemanticError> {
    match ts {
        TypeSpecifier::Void => Ok(QualType::unqualified(ctx.type_ctx.type_void)),
        TypeSpecifier::Char => Ok(QualType::unqualified(ctx.type_ctx.type_char)),
        TypeSpecifier::Short => Ok(QualType::unqualified(ctx.type_ctx.type_short)),
        TypeSpecifier::Int => Ok(QualType::unqualified(ctx.type_ctx.type_int)),
        TypeSpecifier::Long => Ok(QualType::unqualified(ctx.type_ctx.type_long)),
        TypeSpecifier::LongLong => Ok(QualType::unqualified(ctx.type_ctx.type_long_long)),
        TypeSpecifier::Float => Ok(QualType::unqualified(ctx.type_ctx.type_float)),
        TypeSpecifier::Double => Ok(QualType::unqualified(ctx.type_ctx.type_double)),
        TypeSpecifier::LongDouble => Ok(QualType::unqualified(ctx.type_ctx.type_long_double)),
        TypeSpecifier::Signed => {
            // Signed modifier - for now, default to signed int
            Ok(QualType::unqualified(ctx.type_ctx.type_int))
        }
        TypeSpecifier::Unsigned => {
            // Unsigned modifier - return a special marker type that will be handled in merge_base_type
            Ok(QualType::unqualified(ctx.type_ctx.type_uint))
        }
        TypeSpecifier::Bool => Ok(QualType::unqualified(ctx.type_ctx.type_bool)),
        TypeSpecifier::Complex => {
            // Complex types need a base type
            // For now, default to complex double
            let complex_type = ctx.type_ctx.complex_type(ctx.type_ctx.type_double);
            Ok(QualType::unqualified(complex_type))
        }
        TypeSpecifier::Atomic(parsed_type) => {
            // Convert the ParsedType to a TypeRef by applying the declarator to the base type
            // Use the convert_parsed_type_to_type_ref function to handle this properly
            convert_parsed_type_to_qual_type(ctx, *parsed_type, span)
        }
        TypeSpecifier::Record(is_union, tag, definition) => {
            // Properly handle struct/union types with their member declarations

            let existing_entry = tag.and_then(|tag_name| ctx.symbol_table.lookup_tag(tag_name));

            let type_ref_to_use = if let Some(tag_name) = tag {
                // Named struct/union
                if let Some(_def) = definition {
                    // This is a DEFINITION: struct T { ... }
                    let in_current_scope =
                        existing_entry.is_some_and(|(_, scope_id)| scope_id == ctx.symbol_table.current_scope());

                    if in_current_scope {
                        let (entry_ref, _) = existing_entry.unwrap();
                        let entry = ctx.symbol_table.get_symbol(entry_ref);

                        if entry.is_completed {
                            // Redeclaration error - for now just return it
                            entry.type_info
                        } else {
                            // Completing a forward declaration in current scope
                            entry.type_info
                        }
                    } else {
                        // Not in current scope (either not found or shadowing outer)
                        // Create a new record type
                        let new_type_ref = ctx.type_ctx.new_record(Some(*tag_name), *is_union);

                        // Add it to the symbol table in the current scope
                        let symbol_entry = Symbol {
                            name: *tag_name,
                            kind: SymbolKind::Record {
                                is_complete: false,
                                members: Vec::new(),
                                size: None,
                                alignment: None,
                            },
                            type_info: new_type_ref,
                            storage_class: None,
                            scope_id: ctx.symbol_table.current_scope(),
                            def_span: span,
                            def_state: DefinitionState::Defined,
                            is_referenced: false,
                            is_completed: false,
                        };
                        ctx.symbol_table
                            .add_symbol_in_namespace(*tag_name, symbol_entry, Namespace::Tag);
                        new_type_ref
                    }
                } else {
                    // This is a USAGE or FORWARD DECL: struct T; or struct T s;
                    if let Some((entry_ref, _)) = existing_entry {
                        // Found existing (either in current or outer scope)
                        let entry = ctx.symbol_table.get_symbol(entry_ref);
                        entry.type_info
                    } else {
                        // Not found anywhere, create an implicit forward declaration in current scope
                        let forward_ref = ctx.type_ctx.new_record(Some(*tag_name), *is_union);

                        let symbol_entry = Symbol {
                            name: *tag_name,
                            kind: SymbolKind::Record {
                                is_complete: false,
                                members: Vec::new(),
                                size: None,
                                alignment: None,
                            },
                            type_info: forward_ref,
                            storage_class: None,
                            scope_id: ctx.symbol_table.current_scope(),
                            def_span: span,
                            def_state: DefinitionState::Defined,
                            is_referenced: false,
                            is_completed: false,
                        };
                        ctx.symbol_table
                            .add_symbol_in_namespace(*tag_name, symbol_entry, Namespace::Tag);
                        forward_ref
                    }
                }
            } else {
                // Anonymous struct/union definition
                ctx.type_ctx.new_record(None, *is_union)
            };

            // Now handle members if it's a definition
            if let Some(def) = definition {
                let members = def
                    .members
                    .as_ref()
                    .map(|decls| {
                        let mut struct_members = Vec::new();
                        for decl in decls {
                            // Process anonymous struct/union members
                            if decl.init_declarators.is_empty()
                                && let Some((child_is_union, _, child_def)) = decl.specifiers.iter().find_map(|spec| {
                                    if let DeclSpecifier::TypeSpecifier(TypeSpecifier::Record(u, t, d)) = spec {
                                        Some((*u, *t, d))
                                    } else {
                                        None
                                    }
                                })
                            {
                                if let Some(d) = child_def
                                    && let Some(member_decls) = &d.members
                                {
                                    let anonymous_members =
                                        process_anonymous_struct_members(member_decls, child_is_union, ctx, span);
                                    struct_members.extend(anonymous_members);
                                }
                                continue;
                            }

                            for init_declarator in &decl.init_declarators {
                                if let Some(member_name) = extract_identifier(&init_declarator.declarator) {
                                    let member_type = if let Some(base_type_ref) =
                                        lower_decl_specifiers_for_member(&decl.specifiers, ctx, span)
                                    {
                                        let ty = apply_declarator_for_member(
                                            base_type_ref.ty,
                                            &init_declarator.declarator,
                                            ctx,
                                        );
                                        ty.ty
                                    } else {
                                        ctx.type_ctx.type_int
                                    };

                                    struct_members.push(StructMember {
                                        name: member_name,
                                        member_type: QualType::unqualified(member_type),
                                        bit_field_size: None,
                                        span,
                                    });
                                }
                            }
                        }
                        struct_members
                    })
                    .unwrap_or_default();

                // Update the type in AST and SymbolTable
                ctx.type_ctx.complete_record(type_ref_to_use, members.clone(), None);

                if let Some(tag_name) = tag
                    && let Some((entry_ref, _)) = ctx.symbol_table.lookup_tag(*tag_name)
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
                        *entry_members = members;
                    }
                }
            }

            Ok(QualType::unqualified(type_ref_to_use))
        }
        TypeSpecifier::Enum(tag, enumerators) => {
            // 1. Resolve or create the enum type (and its tag)
            let type_ref_to_use = if let Some(tag_name) = tag {
                let existing_entry = ctx.symbol_table.lookup_tag(*tag_name);
                if enumerators.is_some() {
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
                                name: *tag_name,
                                first_def,
                                span,
                            });
                        }
                        type_info
                    } else {
                        // Not found in current scope, create new entry
                        let new_type_ref = ctx.type_ctx.new_enum(Some(*tag_name), ctx.type_ctx.type_int);
                        let symbol_entry = Symbol {
                            name: *tag_name,
                            kind: SymbolKind::EnumTag { is_complete: false },
                            type_info: new_type_ref,
                            storage_class: None,
                            scope_id: ctx.symbol_table.current_scope(),
                            def_span: span,
                            def_state: DefinitionState::Defined,
                            is_referenced: false,
                            is_completed: false,
                        };
                        ctx.symbol_table
                            .add_symbol_in_namespace(*tag_name, symbol_entry, Namespace::Tag);
                        new_type_ref
                    }
                } else {
                    // This is a USAGE or FORWARD DECL: enum T; or enum T e;
                    if let Some((entry_ref, _)) = existing_entry {
                        let entry = ctx.symbol_table.get_symbol(entry_ref);
                        entry.type_info
                    } else {
                        // Implicit forward declaration
                        let forward_ref = ctx.type_ctx.new_enum(Some(*tag_name), ctx.type_ctx.type_int);
                        let symbol = Symbol {
                            name: *tag_name,
                            kind: SymbolKind::EnumTag { is_complete: false },
                            type_info: forward_ref,
                            storage_class: None,
                            scope_id: ctx.symbol_table.current_scope(),
                            def_span: span,
                            def_state: DefinitionState::Defined,
                            is_referenced: false,
                            is_completed: false,
                        };
                        ctx.symbol_table
                            .add_symbol_in_namespace(*tag_name, symbol, Namespace::Tag);
                        forward_ref
                    }
                }
            } else {
                // Anonymous enum definition
                ctx.type_ctx.new_enum(None, ctx.type_ctx.type_int)
            };

            // 2. Process enumerators if it's a definition
            if let Some(enums) = enumerators {
                let mut next_value = 0i64;
                let mut enumerators_list = Vec::new();

                for &enum_ref in enums {
                    let enum_node = ctx.ast.get_node(enum_ref);
                    if let NodeKind::EnumConstant(name, value_expr_ref) = &enum_node.kind {
                        let value = if let Some(v_ref) = value_expr_ref {
                            let val_node = ctx.ast.get_node(*v_ref);
                            if let NodeKind::LiteralInt(val) = val_node.kind {
                                val
                            } else {
                                0 // Should ideally evaluate expression
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
                        let entry = Symbol {
                            name: *name,
                            kind: SymbolKind::EnumConstant { value },
                            type_info: type_ref_to_use,
                            storage_class: None,
                            scope_id: ctx.symbol_table.current_scope(),
                            def_span: enum_node.span,
                            def_state: DefinitionState::Defined,
                            is_referenced: false,
                            is_completed: true,
                        };
                        ctx.symbol_table.add_symbol(*name, entry);
                    }
                }

                // Update the type in AST and SymbolTable
                let type_idx = (type_ref_to_use.get() - 1) as usize;
                let mut updated_type_kind = ctx.type_ctx.types[type_idx].kind.clone();
                if let TypeKind::Enum {
                    enumerators,
                    is_complete,
                    ..
                } = &mut updated_type_kind
                {
                    *enumerators = enumerators_list;
                    *is_complete = true;
                }
                ctx.type_ctx.types[type_idx].kind = updated_type_kind;

                if let Some(tag_name) = tag
                    && let Some((entry_ref, _)) = ctx.symbol_table.lookup_tag(*tag_name)
                {
                    let entry = ctx.symbol_table.get_symbol_mut(entry_ref);
                    entry.is_completed = true;
                    if let SymbolKind::EnumTag { is_complete } = &mut entry.kind {
                        *is_complete = true;
                    }
                }
            }

            Ok(QualType::unqualified(type_ref_to_use))
        }
        TypeSpecifier::TypedefName(name) => {
            // Lookup typedef in symbol table
            if let Some((entry_ref, _scope_id)) = ctx.symbol_table.lookup_symbol(*name) {
                let entry = ctx.symbol_table.get_symbol(entry_ref);
                if let SymbolKind::Typedef { aliased_type } = entry.kind {
                    Ok(QualType::unqualified(aliased_type))
                } else {
                    // Get the kind of the symbol as a string for the error message
                    let kind_string = format!("{:?}", entry.kind);
                    let found_kind_str = kind_string.split_whitespace().next().unwrap_or("symbol");
                    Err(SemanticError::ExpectedTypedefName {
                        found: format!("a {}", found_kind_str.to_lowercase()),
                        span,
                    })
                }
            } else {
                // Typedef not found during semantic lowering - this is expected
                // when typedefs are defined later in the same scope.
                // Create a forward reference that will be resolved during semantic analysis.
                // For now, create a placeholder record type with the expected structure.
                // This is a temporary solution - in a full implementation, we'd have a proper
                // forward reference mechanism.
                Ok(QualType::unqualified(ctx.type_ctx.new_record(Some(*name), false)))
            }
        }
    }
}

/// Merge base types according to C type combination rules
fn merge_base_type(existing: Option<QualType>, new_type: QualType, ctx: &mut LowerCtx) -> Option<QualType> {
    match existing {
        None => Some(new_type),
        Some(existing_ref) => {
            let existing_type = ctx.type_ctx.get(existing_ref.ty);
            let new_type_info = ctx.type_ctx.get(new_type.ty);

            // Handle signed/unsigned merging
            match (&existing_type.kind, &new_type_info.kind) {
                // Unsigned overrides signed for same base type
                (TypeKind::Int { is_signed: true }, TypeKind::Int { is_signed: false }) => Some(new_type),
                (TypeKind::Int { is_signed: false }, TypeKind::Int { is_signed: true }) => {
                    Some(existing_ref) // Keep unsigned
                }

                // Handle char type merging
                (TypeKind::Char { is_signed: true }, TypeKind::Int { is_signed: false }) => {
                    // unsigned char = char + unsigned
                    Some(QualType::unqualified(ctx.type_ctx.type_char_unsigned))
                }
                (TypeKind::Char { is_signed: false }, TypeKind::Int { is_signed: true }) => {
                    Some(existing_ref) // Keep unsigned char
                }

                // Handle short type merging
                (TypeKind::Short { is_signed: true }, TypeKind::Int { is_signed: false }) => {
                    // unsigned short = short + unsigned
                    Some(QualType::unqualified(ctx.type_ctx.type_short_unsigned))
                }
                (TypeKind::Short { is_signed: false }, TypeKind::Int { is_signed: true }) => {
                    Some(existing_ref) // Keep unsigned short
                }

                // Handle unsigned + char/short order
                (TypeKind::Int { is_signed: false }, TypeKind::Char { is_signed: true }) => {
                    // unsigned char = unsigned + char
                    Some(QualType::unqualified(ctx.type_ctx.type_char_unsigned))
                }
                (TypeKind::Int { is_signed: false }, TypeKind::Short { is_signed: true }) => {
                    // unsigned short = unsigned + short
                    Some(QualType::unqualified(ctx.type_ctx.type_short_unsigned))
                }

                // Handle unsigned + long/long long order
                (
                    TypeKind::Int { is_signed: false },
                    TypeKind::Long {
                        is_long_long: false, ..
                    },
                ) => {
                    // unsigned long = unsigned + long
                    Some(QualType::unqualified(ctx.type_ctx.type_long_unsigned))
                }
                (TypeKind::Int { is_signed: false }, TypeKind::Long { is_long_long: true, .. }) => {
                    // unsigned long long = unsigned + long long
                    Some(QualType::unqualified(ctx.type_ctx.type_long_long_unsigned))
                }

                // Long long overrides long
                (
                    TypeKind::Long {
                        is_long_long: false, ..
                    },
                    TypeKind::Long { is_long_long: true, .. },
                ) => Some(new_type),
                (
                    TypeKind::Long { is_long_long: true, .. },
                    TypeKind::Long {
                        is_long_long: false, ..
                    },
                ) => {
                    Some(existing_ref) // Keep long long
                }

                // For other combinations, keep the existing type
                // In a full implementation, we'd handle more complex cases
                _ => Some(existing_ref),
            }
        }
    }
}

/// Validate specifier combinations for semantic correctness
fn validate_specifier_combinations(info: &DeclSpecInfo, ctx: &mut LowerCtx, span: SourceSpan) {
    // Check typedef with other storage classes
    if info.is_typedef && info.storage.is_some_and(|s| s != StorageClass::Typedef) {
        ctx.report_error(SemanticError::ConflictingStorageClasses { span });
    }

    // TODO: Add more validation rules
    // - Check for invalid type combinations
    // - Check for conflicting specifiers
    // - Check for missing required specifiers
}

/// Create a type definition semantic node for declarations with 0 init_declarators
fn lower_type_definition(specifiers: &[DeclSpecifier], ctx: &mut LowerCtx, span: SourceSpan) -> Option<NodeRef> {
    // Find the type specifier
    let mut type_specifier = None;
    for spec in specifiers {
        if let DeclSpecifier::TypeSpecifier(ts) = spec {
            type_specifier = Some(ts);
            break;
        }
    }

    let type_spec = type_specifier?;

    match type_spec {
        TypeSpecifier::Record(is_union, tag, _definition) => {
            // Create the record type
            let record_type = match resolve_type_specifier(type_spec, ctx, span) {
                Ok(ty) => ty,
                Err(e) => {
                    ctx.report_error(e);
                    return None;
                }
            };

            // Create RecordDecl semantic node
            let record_decl = RecordDeclData {
                name: *tag,
                ty: record_type.ty,
                members: Vec::new(), // TODO: Extract members from definition
                is_union: *is_union,
            };

            let record_node = Node::new(NodeKind::RecordDecl(record_decl), span);
            Some(ctx.ast.push_node(record_node))
        }
        TypeSpecifier::Enum(tag, _enumerators) => {
            // Create the enum type
            let enum_type = match resolve_type_specifier(type_spec, ctx, span) {
                Ok(ty) => ty,
                Err(e) => {
                    ctx.report_error(e);
                    return None;
                }
            };

            // Create RecordDecl semantic node (reuse for enums)
            let record_decl = RecordDeclData {
                name: *tag,
                ty: enum_type.ty,
                members: Vec::new(), // TODO: Extract enumerators
                is_union: false,     // enums are not unions
            };

            let record_node = Node::new(NodeKind::RecordDecl(record_decl), span);
            Some(ctx.ast.push_node(record_node))
        }
        _ => None,
    }
}

/// Process an init-declarator into a semantic node
fn lower_init_declarator(ctx: &mut LowerCtx, spec: &DeclSpecInfo, init: InitDeclarator, span: SourceSpan) -> NodeRef {
    // 1. Resolve final type (base + declarator)
    let base_ty = spec.base_type.unwrap_or_else(|| {
        ctx.report_error(SemanticError::MissingTypeSpecifier { span });
        QualType::unqualified(ctx.type_ctx.type_error)
    });

    let name = extract_identifier(&init.declarator).expect("Anonymous declarations unsupported");

    // For simple identifiers without qualifiers, don't create a new type entry
    let final_ty = if let Declarator::Identifier(_, qualifiers, None) = &init.declarator {
        if qualifiers.is_empty() {
            // Simple case: just use the base type directly
            base_ty
        } else {
            // Has qualifiers, need to apply declarator
            apply_declarator(base_ty.ty, &init.declarator, ctx)
        }
    } else {
        // Complex case: apply declarator transformations and create new type
        apply_declarator(base_ty.ty, &init.declarator, ctx)
    };

    // 2. Handle typedefs
    if spec.is_typedef {
        let typedef_decl = TypedefDeclData { name, ty: final_ty };
        let typedef_node = ctx.ast.push_node(Node::new(NodeKind::TypedefDecl(typedef_decl), span));

        // Add typedef to symbol table to resolve forward references
        let symbol_entry = Symbol {
            name: name.as_str().into(),
            kind: SymbolKind::Typedef {
                aliased_type: final_ty.ty,
            },
            type_info: final_ty.ty,
            storage_class: Some(StorageClass::Typedef),
            scope_id: ctx.symbol_table.current_scope(),
            def_span: span,
            def_state: DefinitionState::Defined,
            is_referenced: false,
            is_completed: true,
        };

        ctx.symbol_table.add_symbol(name, symbol_entry);

        return typedef_node;
    }

    // 3. Distinguish between functions and variables
    let type_info = ctx.type_ctx.get(final_ty.ty);
    if matches!(type_info.kind, TypeKind::Function { .. }) {
        let func_decl = FunctionDeclData {
            name,
            ty: final_ty.ty,
            storage: spec.storage,
            body: None,
        };
        let node = ctx.ast.push_node(Node::new(NodeKind::FunctionDecl(func_decl), span));

        let symbol_entry = Symbol {
            name: name.as_str().into(),
            kind: SymbolKind::Function {
                is_inline: false,
                is_variadic: false,
                parameters: Vec::new(), // FIXME: fill this...
            },
            type_info: final_ty.ty,
            storage_class: spec.storage,
            scope_id: ctx.symbol_table.current_scope(),
            def_span: span,
            def_state: DefinitionState::DeclaredOnly,
            is_referenced: false,
            is_completed: true,
        };
        ctx.symbol_table.add_symbol(name, symbol_entry);

        node
    } else {
        let var_decl = VarDeclData {
            name,
            ty: final_ty,
            storage: spec.storage,
            init: init.initializer,
        };

        let def_state = if var_decl.init.is_some() {
            DefinitionState::Defined
        } else {
            DefinitionState::Tentative
        };

        let node = ctx.ast.push_node(Node::new(NodeKind::VarDecl(var_decl), span));

        let symbol_entry = Symbol {
            name: name.as_str().into(),
            kind: SymbolKind::Variable {
                is_global: ctx.symbol_table.current_scope() == ScopeId::GLOBAL,
                initializer: init.initializer,
            },
            type_info: final_ty.ty,
            storage_class: spec.storage,
            scope_id: ctx.symbol_table.current_scope(),
            def_span: span,
            def_state,
            is_referenced: false,
            is_completed: true,
        };

        if ctx.symbol_table.current_scope() == ScopeId::GLOBAL {
            match ctx.symbol_table.merge_global_symbol(name, symbol_entry) {
                Ok(_) => {}
                Err(e) => {
                    let SymbolTableError::InvalidRedefinition { name, existing } = e;
                    let existing = ctx.symbol_table.get_symbol(existing);
                    ctx.diag.report(SemanticError::Redefinition {
                        name,
                        first_def: existing.def_span,
                        span,
                    });
                }
            }
        } else {
            ctx.symbol_table.add_symbol(name, symbol_entry);
        }

        node
    }
}

fn lower_function_parameters(params: &[ParamData], ctx: &mut LowerCtx) -> Vec<FunctionParameter> {
    params
        .iter()
        .map(|param| {
            let span = SourceSpan::empty(); // FIXME: Get a proper span for parameter declarations
            let spec_info = lower_decl_specifiers(&param.specifiers, ctx, span);

            // C standard: if type specifier is missing in a parameter, it defaults to int.
            let base_ty = spec_info
                .base_type
                .unwrap_or_else(|| QualType::unqualified(ctx.type_ctx.type_int));

            let final_ty = if let Some(declarator) = &param.declarator {
                apply_declarator(base_ty.ty, declarator, ctx)
            } else {
                base_ty
            };
            FunctionParameter {
                param_type: final_ty,
                name: param.declarator.as_ref().and_then(extract_identifier),
            }
        })
        .collect()
}

/// Apply declarator transformations to a base type
fn apply_declarator(base_type: TypeRef, declarator: &Declarator, ctx: &mut LowerCtx) -> QualType {
    match declarator {
        Declarator::Pointer(qualifiers, next) => {
            let pointee_type = if let Some(next_decl) = next {
                apply_declarator(base_type, next_decl, ctx)
            } else {
                QualType::unqualified(base_type)
            };

            let pointer_type_ref = ctx.type_ctx.pointer_to(pointee_type.ty);
            QualType::new(pointer_type_ref, *qualifiers)
        }
        Declarator::Identifier(_, qualifiers, _) => {
            let base_type_ref = base_type;
            QualType::new(base_type_ref, *qualifiers)
        }
        Declarator::Array(base, size) => {
            let element_type = apply_declarator(base_type, base, ctx);
            let array_size = match size {
                ArraySize::Expression { expr, qualifiers: _ } => {
                    if let Some(const_val) = eval_const_expr(ctx, *expr) {
                        if const_val > 0 {
                            ArraySizeType::Constant(const_val as usize)
                        } else {
                            ctx.report_error(SemanticError::InvalidArraySize {
                                span: ctx.ast.get_node(*expr).span,
                            });
                            ArraySizeType::Incomplete
                        }
                    } else {
                        // TODO: Handle non-constant array sizes (VLAs)
                        ArraySizeType::Incomplete
                    }
                }
                ArraySize::Star { qualifiers: _ } => ArraySizeType::Star,
                ArraySize::Incomplete => ArraySizeType::Incomplete,
                ArraySize::VlaSpecifier {
                    is_static: _,
                    qualifiers: _,
                    size: _,
                } => {
                    // TODO: Handle VLA specifiers
                    ArraySizeType::Incomplete
                }
            };

            let array_type_ref = ctx.type_ctx.array_of(element_type.ty, array_size);
            QualType::unqualified(array_type_ref)
        }
        Declarator::Function {
            inner: base,
            params,
            is_variadic,
        } => {
            // Check for function pointer: a pointer declarator inside the function base
            if let Declarator::Pointer(qualifiers, Some(inner_base)) = &**base {
                // This is a pointer to a function.
                // The `base_type` applies to the return type of the function.
                let return_type = apply_declarator(base_type, inner_base, ctx);

                let parameters = lower_function_parameters(params, ctx);

                // Build the function type first
                let function_type_ref = ctx.type_ctx.function_type(return_type.ty, parameters, *is_variadic);
                let pointer_type_ref = ctx.type_ctx.pointer_to(function_type_ref);
                return QualType::new(pointer_type_ref, *qualifiers);
            }

            // This is a regular function declaration.
            let return_type = apply_declarator(base_type, base, ctx);
            let parameters = lower_function_parameters(params, ctx);

            let function_type_ref = ctx.type_ctx.function_type(return_type.ty, parameters, *is_variadic);
            QualType::unqualified(function_type_ref)
        }
        Declarator::AnonymousRecord(_, _) => {
            // TODO: Handle anonymous struct/union
            QualType::unqualified(base_type)
        }
        Declarator::BitField(base, _) => {
            // TODO: Handle bit fields
            apply_declarator(base_type, base, ctx)
        }
        Declarator::Abstract => QualType::unqualified(base_type),
    }
}

/// Main entry point for running semantic lowering on an entire AST
pub fn run_symbol_resolver(
    ast: &mut Ast,
    diag: &mut DiagnosticEngine,
    symbol_table: &mut SymbolTable,
    type_ctx: &mut TypeContext,
) -> Vec<Option<ScopeId>> {
    // Check if we have a root node to start traversal from
    let node_length = ast.nodes.len();
    let root_node_ref = ast.get_root();

    // Create lowering context
    let mut lower_ctx = LowerCtx::new(ast, diag, symbol_table, type_ctx);

    // initial size of scope map
    lower_ctx.scope_map.resize(node_length, None);

    // Perform recursive scope-aware lowering
    lower_node_recursive(&mut lower_ctx, root_node_ref);
    lower_ctx.scope_map
}

fn lower_node_recursive(ctx: &mut LowerCtx, node_ref: NodeRef) {
    let node_kind = {
        let node = ctx.ast.get_node(node_ref);
        node.kind.clone()
    };

    match node_kind {
        NodeKind::TranslationUnit(nodes) => {
            ctx.symbol_table.set_current_scope(ScopeId::GLOBAL);
            ctx.set_scope(node_ref, ScopeId::GLOBAL);

            for node in nodes {
                lower_node_recursive(ctx, node);
            }
        }
        NodeKind::FunctionDef(func_def) => {
            // Extract function name from the ParsedType declarator
            let func_name = extract_identifier_from_parsed_type(&func_def.declarator, ctx)
                .unwrap_or_else(|| NameId::new("anonymous_function"));

            // Extract the return type from the function definition's specifiers
            let return_type_ref =
                lower_decl_specifiers_for_function_return(&func_def.specifiers, ctx, ctx.ast.get_node(node_ref).span)
                    .unwrap_or_else(|| QualType::unqualified(ctx.type_ctx.type_int));

            // Create the function type with the correct return type by applying the declarator
            let declarator_type = apply_parsed_declarator(return_type_ref.ty, &func_def.declarator, ctx);
            let function_type_ref = declarator_type.ty;

            // Extract parameters from the function type for the symbol entry
            let parameters = if let TypeKind::Function { parameters, .. } = &ctx.type_ctx.get(function_type_ref).kind {
                parameters.clone()
            } else {
                Vec::new()
            };

            let symbol_entry = Symbol {
                name: func_name,
                kind: SymbolKind::Function {
                    is_inline: false,
                    is_variadic: false,
                    parameters: parameters.clone(),
                },
                type_info: function_type_ref,
                storage_class: None,
                scope_id: ScopeId::GLOBAL,
                def_span: ctx.ast.get_node(node_ref).span,
                def_state: DefinitionState::Defined,
                is_referenced: false,
                is_completed: true,
            };

            let symbol_entry_ref = ctx.symbol_table.add_symbol(func_name, symbol_entry);

            let param_scope_id = ctx.symbol_table.push_scope();
            ctx.set_scope(node_ref, param_scope_id);

            // Create normalized parameters for the FunctionData
            let normalized_params = parameters
                .into_iter()
                .map(|param| {
                    // Create a symbol entry for the parameter
                    let param_symbol_entry = Symbol {
                        name: param.name.unwrap_or_else(|| NameId::new("unnamed_param")),
                        kind: SymbolKind::Variable {
                            is_global: false,
                            initializer: None,
                        },
                        type_info: param.param_type.ty,
                        storage_class: None,
                        scope_id: ctx.symbol_table.current_scope(),
                        def_span: ctx.ast.get_node(node_ref).span,
                        def_state: DefinitionState::Defined,
                        is_referenced: false,
                        is_completed: true,
                    };

                    let param_symbol_ref = ctx.symbol_table.add_symbol(param_symbol_entry.name, param_symbol_entry);

                    crate::ast::ParamDecl {
                        symbol: param_symbol_ref,
                        ty: param.param_type,
                    }
                })
                .collect();

            // Create the Function semantic node
            let function_data = crate::ast::FunctionData {
                symbol: symbol_entry_ref,
                ty: function_type_ref,
                params: normalized_params,
                body: func_def.body,
            };

            // Replace the FunctionDef node with the Function node
            let function_node = Node::new(NodeKind::Function(function_data), ctx.ast.get_node(node_ref).span);
            ctx.ast.replace_node(node_ref, function_node);

            // Now process the function body with proper scope management
            lower_node_recursive(ctx, func_def.body);
            ctx.symbol_table.pop_scope();
        }
        NodeKind::CompoundStatement(nodes) => {
            let scope_id = ctx.symbol_table.push_scope();
            ctx.set_scope(node_ref, scope_id);

            for node in nodes {
                lower_node_recursive(ctx, node);
            }
            ctx.symbol_table.pop_scope();
        }
        NodeKind::Declaration(_) => {
            let semantic_nodes = lower_declaration(ctx, node_ref);

            if !semantic_nodes.is_empty() {
                if semantic_nodes.len() == 1 {
                    // Single declarator case: replace the original declaration node with the semantic node
                    let semantic_node_data = ctx.ast.get_node(semantic_nodes[0]).clone();
                    ctx.ast.replace_node(node_ref, semantic_node_data);
                } else {
                    // Multi-declarator case: create a DeclarationList containing all semantic nodes
                    let original_node = ctx.ast.get_node(node_ref);
                    let compound_node = Node::new(NodeKind::DeclarationList(semantic_nodes), original_node.span);
                    ctx.ast.replace_node(node_ref, compound_node);
                }
            }
        }
        NodeKind::For(for_stmt) => {
            let scope_id = ctx.symbol_table.push_scope();
            ctx.set_scope(node_ref, scope_id);

            if let Some(init) = for_stmt.init {
                lower_node_recursive(ctx, init);
            }
            if let Some(cond) = for_stmt.condition {
                lower_node_recursive(ctx, cond);
            }
            if let Some(inc) = for_stmt.increment {
                lower_node_recursive(ctx, inc);
            }
            lower_node_recursive(ctx, for_stmt.body);
            ctx.symbol_table.pop_scope();
        }
        // Other nodes that might contain statements/declarations
        NodeKind::If(if_stmt) => {
            lower_node_recursive(ctx, if_stmt.then_branch);
            if let Some(else_branch) = if_stmt.else_branch {
                lower_node_recursive(ctx, else_branch);
            }
        }
        NodeKind::While(while_stmt) => {
            lower_node_recursive(ctx, while_stmt.body);
        }
        NodeKind::DoWhile(body, _) => {
            lower_node_recursive(ctx, body);
        }
        NodeKind::Switch(_, body) => {
            lower_node_recursive(ctx, body);
        }
        NodeKind::Label(name, stmt, _) => {
            let label_ty = ctx.type_ctx.type_void; // void for now
            let entry = Symbol {
                name,
                kind: SymbolKind::Label {
                    is_defined: true,
                    is_used: true,
                },
                type_info: label_ty,
                storage_class: None,
                scope_id: ctx.symbol_table.current_scope(),
                def_span: ctx.ast.get_node(node_ref).span,
                def_state: DefinitionState::Defined,
                is_referenced: false,
                is_completed: true,
            };
            ctx.symbol_table.add_symbol_in_namespace(name, entry, Namespace::Label);
            lower_node_recursive(ctx, stmt);
        }
        NodeKind::ParsedCast(parsed_type, expr_node) => {
            // Convert ParsedType to TypeRef
            let type_ref = convert_parsed_type_to_qual_type(ctx, parsed_type, ctx.ast.get_node(node_ref).span)
                .unwrap_or_else(|_| {
                    // Create an error type if conversion fails
                    QualType::unqualified(ctx.type_ctx.type_error)
                });
            // Replace the ParsedCast node with a Cast node
            let cast_node = Node::new(NodeKind::Cast(type_ref, expr_node), ctx.ast.get_node(node_ref).span);
            ctx.ast.replace_node(node_ref, cast_node);
            lower_node_recursive(ctx, expr_node);
        }
        NodeKind::ParsedSizeOfType(parsed_type) => {
            // Convert ParsedType to TypeRef
            let type_ref = convert_parsed_type_to_qual_type(ctx, parsed_type, ctx.ast.get_node(node_ref).span)
                .unwrap_or_else(|_| {
                    // Create an error type if conversion fails
                    QualType::unqualified(ctx.type_ctx.type_error)
                });
            // Replace the ParsedSizeOfType node with a SizeOfType node
            let size_of_node = Node::new(NodeKind::SizeOfType(type_ref), ctx.ast.get_node(node_ref).span);
            ctx.ast.replace_node(node_ref, size_of_node);
        }
        NodeKind::ParsedCompoundLiteral(parsed_type, initializer_node) => {
            // Convert ParsedType to TypeRef
            let type_ref = convert_parsed_type_to_qual_type(ctx, parsed_type, ctx.ast.get_node(node_ref).span)
                .unwrap_or_else(|_| {
                    // Create an error type if conversion fails
                    QualType::unqualified(ctx.type_ctx.type_error)
                });
            // Replace the ParsedCompoundLiteral node with a CompoundLiteral node
            let compound_literal_node = Node::new(
                NodeKind::CompoundLiteral(type_ref, initializer_node),
                ctx.ast.get_node(node_ref).span,
            );
            ctx.ast.replace_node(node_ref, compound_literal_node);
            lower_node_recursive(ctx, initializer_node);
        }
        NodeKind::ParsedAlignOf(parsed_type) => {
            // Convert ParsedType to TypeRef
            let type_ref = convert_parsed_type_to_qual_type(ctx, parsed_type, ctx.ast.get_node(node_ref).span)
                .unwrap_or_else(|_| {
                    // Create an error type if conversion fails
                    QualType::unqualified(ctx.type_ctx.type_error)
                });
            // Replace the ParsedAlignOf node with an AlignOf node
            let align_of_node = Node::new(NodeKind::AlignOf(type_ref), ctx.ast.get_node(node_ref).span);
            ctx.ast.replace_node(node_ref, align_of_node);
        }
        _ => {}
    }
}

/// Lower declaration specifiers for function return type
fn lower_decl_specifiers_for_function_return(
    specs: &[DeclSpecifier],
    ctx: &mut LowerCtx,
    span: SourceSpan,
) -> Option<QualType> {
    let mut merged_type = None;

    for spec in specs {
        if let DeclSpecifier::TypeSpecifier(ts) = spec {
            match resolve_type_specifier(ts, ctx, span) {
                Ok(ty) => {
                    merged_type = merge_base_type(merged_type, ty, ctx);
                }
                Err(_) => continue,
            }
        }
    }

    merged_type
}

/// Lower declaration specifiers for struct members (simplified version)
fn lower_decl_specifiers_for_member(specs: &[DeclSpecifier], ctx: &mut LowerCtx, span: SourceSpan) -> Option<QualType> {
    for spec in specs {
        if let DeclSpecifier::TypeSpecifier(ts) = spec {
            match resolve_type_specifier(ts, ctx, span) {
                Ok(ty) => return Some(ty),
                Err(_) => continue,
            }
        }
    }
    None
}

/// Apply declarator for struct members (simplified version)
fn apply_declarator_for_member(base_type: TypeRef, declarator: &Declarator, ctx: &mut LowerCtx) -> QualType {
    match declarator {
        Declarator::Identifier(_, qualifiers, _) => {
            let base_type_ref = base_type;
            QualType::new(base_type_ref, *qualifiers)
        }
        Declarator::Pointer(qualifiers, next) => {
            let pointee_type = if let Some(next_decl) = next {
                apply_declarator_for_member(base_type, next_decl, ctx)
            } else {
                QualType::unqualified(base_type)
            };

            let pointer_type_ref = ctx.type_ctx.pointer_to(pointee_type.ty);
            QualType::new(pointer_type_ref, *qualifiers)
        }
        Declarator::Array(base, size) => {
            let element_type = apply_declarator_for_member(base_type, base, ctx);
            let array_size = match size {
                ArraySize::Expression { expr, qualifiers: _ } => {
                    if let Some(const_val) = eval_const_expr(ctx, *expr) {
                        if const_val > 0 {
                            ArraySizeType::Constant(const_val as usize)
                        } else {
                            ctx.report_error(SemanticError::InvalidArraySize {
                                span: ctx.ast.get_node(*expr).span,
                            });
                            ArraySizeType::Incomplete
                        }
                    } else {
                        // VLA in struct is a GNU extension, not supported yet
                        ArraySizeType::Incomplete
                    }
                }
                ArraySize::Star { qualifiers: _ } => ArraySizeType::Star,
                ArraySize::Incomplete => ArraySizeType::Incomplete,
                ArraySize::VlaSpecifier {
                    is_static: _,
                    qualifiers: _,
                    size: _,
                } => {
                    // TODO: Handle VLA specifiers
                    ArraySizeType::Incomplete
                }
            };

            let array_type_ref = ctx.type_ctx.array_of(element_type.ty, array_size);
            QualType::unqualified(array_type_ref)
        }
        // For other declarator types, just return the base type
        _ => QualType::unqualified(base_type),
    }
}

/// Process anonymous struct/union members by flattening them into the containing struct
fn process_anonymous_struct_members(
    member_decls: &[DeclarationData],
    _is_union: bool,
    ctx: &mut LowerCtx,
    span: SourceSpan,
) -> Vec<StructMember> {
    let mut flattened_members = Vec::new();

    for decl in member_decls {
        // Check if this is a nested anonymous struct/union
        let is_nested_anonymous = decl.specifiers.len() == 1
            && decl.specifiers.iter().any(|spec| {
                matches!(
                    spec,
                    DeclSpecifier::TypeSpecifier(TypeSpecifier::Record(_, None, Some(_)))
                )
            });

        if is_nested_anonymous {
            // This is a nested anonymous struct/union - recursively flatten its members
            if let Some((nested_is_union, _, Some(definition))) = decl.specifiers.iter().find_map(|spec| {
                if let DeclSpecifier::TypeSpecifier(TypeSpecifier::Record(is_union, tag, definition)) = spec {
                    Some((is_union, tag, definition))
                } else {
                    None
                }
            }) && let Some(nested_decls) = &definition.members
            {
                let nested_members = process_anonymous_struct_members(nested_decls, *nested_is_union, ctx, span);
                flattened_members.extend(nested_members);
            }
        } else {
            // This is a regular member - process it normally
            for init_declarator in &decl.init_declarators {
                if let Some(member_name) = extract_identifier(&init_declarator.declarator) {
                    // Get the member type from declaration specifiers
                    let member_type =
                        if let Some(base_type_ref) = lower_decl_specifiers_for_member(&decl.specifiers, ctx, span) {
                            // Apply the declarator to get the final member type
                            let member_type_with_declarator =
                                apply_declarator_for_member(base_type_ref.ty, &init_declarator.declarator, ctx);
                            member_type_with_declarator
                        } else {
                            QualType::unqualified(ctx.type_ctx.type_int)
                        };

                    flattened_members.push(StructMember {
                        name: member_name,
                        member_type: member_type,
                        bit_field_size: None,
                        span,
                    });
                }
            }
        }
    }

    flattened_members
}
