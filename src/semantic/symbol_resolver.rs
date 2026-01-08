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

use crate::ast::{nodes::TypeQualifier, utils::extract_identifier, *};
use crate::diagnostic::{DiagnosticEngine, SemanticError};
use crate::semantic::const_eval::{self, ConstEvalCtx};
use crate::semantic::struct_lowering::lower_struct_members;
use crate::semantic::symbol_table::{DefinitionState, SymbolTableError};
use crate::semantic::{
    ArraySizeType, EnumConstant, ScopeId, StructMember, SymbolKind, SymbolTable, TypeKind, TypeQualifiers, TypeRef,
    TypeRegistry,
};
use crate::semantic::{FunctionParameter, QualType};
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
    ctx.registry.merge_qualifiers(result_type, parsed_type.qualifiers)
}

/// Recursively apply parsed declarator to base type
fn apply_parsed_declarator_recursive(
    current_type: TypeRef,
    declarator_ref: ParsedDeclRef,
    ctx: &mut LowerCtx,
) -> QualType {
    let declarator_node = ctx.ast.parsed_types.get_decl(declarator_ref);

    match declarator_node {
        ParsedDeclaratorNode::Identifier { .. } => QualType::unqualified(current_type),
        ParsedDeclaratorNode::Pointer { qualifiers, inner } => {
            // Pointer
            // Apply Pointer modifier to the current type first (Top-Down)
            let pointer_type = ctx.registry.pointer_to(current_type);
            let modified_current = pointer_type;
            let result = apply_parsed_declarator_recursive(modified_current, inner, ctx);
            ctx.registry.merge_qualifiers(result, qualifiers)
        }
        ParsedDeclaratorNode::Array { size, inner } => {
            // Array
            let array_size = convert_parsed_array_size(&size, ctx);
            let array_type_ref = ctx.registry.array_of(current_type, array_size);

            apply_parsed_declarator_recursive(array_type_ref, inner, ctx)
        }
        ParsedDeclaratorNode::Function { params, flags, inner } => {
            // Function
            // Process parameters separately
            let parsed_params: Vec<_> = ctx.ast.parsed_types.get_params(params).to_vec();
            let mut processed_params = Vec::new();
            for param in parsed_params {
                let param_type = convert_parsed_type_to_qual_type(ctx, param.ty, param.span).unwrap_or_else(|_| {
                    // Create an error type if conversion fails
                    QualType::unqualified(ctx.registry.type_int)
                });

                // Apply array-to-pointer decay for function parameters
                let decayed_param_type = ctx.registry.decay(param_type);

                processed_params.push(FunctionParameter {
                    param_type: decayed_param_type,
                    name: param.name,
                });
            }

            let function_type_ref = ctx
                .registry
                .function_type(current_type, processed_params, flags.is_variadic);

            apply_parsed_declarator_recursive(function_type_ref, inner, ctx)
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

/// Helper function to deduce array size from initializer
fn deduce_array_size(ctx: &LowerCtx, init_node: NodeRef) -> Option<usize> {
    let node = ctx.ast.get_node(init_node);
    match &node.kind {
        NodeKind::InitializerList(inits) => {
            let mut max_index: i64 = -1;
            let mut current_index: i64 = 0;

            // If list is empty (GCC extension), size is 0
            if inits.is_empty() {
                return Some(0);
            }

            for init in inits {
                // Check for array index designator
                if let Some(first_designator) = init.designation.first() {
                    match first_designator {
                        crate::ast::Designator::ArrayIndex(expr_ref) => {
                            let const_ctx = ConstEvalCtx { ast: ctx.ast };
                            if let Some(val) = const_eval::eval_const_expr(&const_ctx, *expr_ref) {
                                current_index = val;
                            } else {
                                // Non-constant index in initializer -> can't deduce size
                                return None;
                            }
                        }
                        crate::ast::Designator::GnuArrayRange(start, end) => {
                            let const_ctx = ConstEvalCtx { ast: ctx.ast };
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
                            // Field designator on array element -> applies to current element
                            // No change to current_index
                        }
                    }
                }

                if current_index > max_index {
                    max_index = current_index;
                }

                // Advance current_index for next element
                current_index += 1;
            }

            if max_index < 0 {
                Some(0)
            } else {
                Some((max_index + 1) as usize)
            }
        }
        NodeKind::LiteralString(name_id) => {
            // String literal initialization: char a[] = "foo";
            // Size is len + 1 (including null terminator)
            let s = name_id.to_string();
            Some(s.len() + 1)
        }
        _ => None,
    }
}

/// Helper function to resolve array size logic
fn resolve_array_size(size: Option<NodeRef>, ctx: &mut LowerCtx) -> ArraySizeType {
    if let Some(expr) = size {
        let const_eval_ctx = ConstEvalCtx { ast: ctx.ast };
        if let Some(const_val) = const_eval::eval_const_expr(&const_eval_ctx, expr) {
            if const_val > 0 {
                ArraySizeType::Constant(const_val as usize)
            } else {
                ctx.report_error(SemanticError::InvalidArraySize {
                    span: ctx.ast.get_node(expr).span,
                });
                ArraySizeType::Incomplete
            }
        } else {
            // TODO: Handle non-constant array sizes (VLAs)
            ArraySizeType::Incomplete
        }
    } else {
        // Should not happen as parser ensures size is Some
        ArraySizeType::Incomplete
    }
}

/// Context for the semantic lowering phase
pub(crate) struct LowerCtx<'a, 'src> {
    pub(crate) ast: &'a mut Ast,
    pub(crate) diag: &'src mut DiagnosticEngine,
    pub(crate) symbol_table: &'a mut SymbolTable,
    pub(crate) scope_map: Vec<Option<ScopeId>>,
    // Track errors during lowering for early termination
    pub(crate) has_errors: bool,
    pub(crate) registry: &'a mut TypeRegistry,
}

impl<'a, 'src> LowerCtx<'a, 'src> {
    /// Create a new lowering context
    pub(crate) fn new(
        ast: &'a mut Ast,
        diag: &'src mut DiagnosticEngine,
        symbol_table: &'a mut SymbolTable,
        registry: &'a mut TypeRegistry,
    ) -> Self {
        Self {
            ast,
            diag,
            symbol_table,
            scope_map: Vec::new(),
            has_errors: false,
            registry,
        }
    }

    /// Report a semantic error and mark context as having errors
    pub(crate) fn report_error(&mut self, error: SemanticError) {
        self.has_errors = true;
        self.diag.report(error);
    }

    /// Check if the context has any errors
    pub(crate) fn has_errors(&self) -> bool {
        self.has_errors
    }

    fn set_scope(&mut self, node_ref: NodeRef, scope_id: ScopeId) {
        self.scope_map[(node_ref.get() - 1) as usize] = Some(scope_id);
    }
}

/// Information about declaration specifiers after processing
#[derive(Debug, Clone, Default)]
pub(crate) struct DeclSpecInfo {
    pub(crate) storage: Option<StorageClass>,
    pub(crate) qualifiers: TypeQualifiers,
    pub(crate) base_type: Option<QualType>,
    pub(crate) is_typedef: bool,
    pub(crate) is_inline: bool,
    pub(crate) is_noreturn: bool,
    pub(crate) alignment: Option<u32>,
}

/// Main entry point for lowering a declaration
/// Returns a vector of semantic node data (one for each declarator)
pub(crate) fn lower_declaration(ctx: &mut LowerCtx, decl_node: NodeRef) -> Vec<NodeKind> {
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
            // Extract the node kind from the created node
            let node_kind = ctx.ast.get_node(type_def_node_ref).kind.clone();
            return vec![node_kind];
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

    // 2. Process init-declarators into semantic node data
    let semantic_nodes: Vec<NodeKind> = decl
        .init_declarators
        .into_iter()
        .map(|init| {
            let span = if init.span.is_empty() {
                declaration_span
            } else {
                init.span
            };
            create_semantic_node_data(ctx, &spec, init, span)
        })
        .collect();

    semantic_nodes
}

/// Process declaration specifiers into consolidated information
pub(crate) fn lower_decl_specifiers(specs: &[DeclSpecifier], ctx: &mut LowerCtx, span: SourceSpan) -> DeclSpecInfo {
    let mut info = DeclSpecInfo::default();

    for spec in specs {
        match spec {
            DeclSpecifier::StorageClass(sc) => {
                // Check for duplicate storage class
                if info.storage.replace(*sc).is_some() {
                    ctx.report_error(SemanticError::ConflictingStorageClasses { span });
                }

                // Handle typedef storage class
                if *sc == StorageClass::Typedef {
                    info.is_typedef = true;
                }
            }

            DeclSpecifier::TypeQualifier(q) => {
                let qualifier = match q {
                    TypeQualifier::Const => TypeQualifiers::CONST,
                    TypeQualifier::Volatile => TypeQualifiers::VOLATILE,
                    TypeQualifier::Restrict => TypeQualifiers::RESTRICT,
                    TypeQualifier::Atomic => TypeQualifiers::ATOMIC,
                };
                info.qualifiers |= qualifier;
            }

            DeclSpecifier::TypeSpecifier(ts) => {
                let ty = resolve_type_specifier(ts, ctx, span).unwrap_or_else(|e| {
                    ctx.report_error(e);
                    QualType::unqualified(ctx.registry.type_error)
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

            DeclSpecifier::AlignmentSpecifier(spec) => {
                let align = match spec {
                    ParsedAlignmentSpecifier::Type(parsed_type) => {
                        let ty = convert_parsed_type_to_qual_type(ctx, *parsed_type, span).unwrap_or_else(|_| {
                            // Error already reported by convert_parsed_type_to_qual_type if it failed
                            QualType::unqualified(ctx.registry.type_int) // Default fallback
                        });

                        // Layout must be complete to get alignment
                        match ctx.registry.ensure_layout(ty.ty()) {
                            Ok(layout) => layout.alignment as u32,
                            Err(e) => {
                                ctx.report_error(e);
                                1 // Default
                            }
                        }
                    }
                    ParsedAlignmentSpecifier::Expr(expr_ref) => {
                        let const_ctx = ConstEvalCtx { ast: ctx.ast };
                        if let Some(val) = const_eval::eval_const_expr(&const_ctx, *expr_ref) {
                            if val == 0 {
                                // "If the constant expression evaluates to zero, the alignment specifier shall have no effect."
                                0 // Return 0 to indicate no effect
                            } else if val < 0 {
                                ctx.report_error(SemanticError::InvalidAlignment {
                                    value: val,
                                    span: ctx.ast.get_node(*expr_ref).span,
                                });
                                1
                            } else {
                                // Must be power of 2
                                if (val & (val - 1)) != 0 {
                                    ctx.report_error(SemanticError::InvalidAlignment {
                                        value: val,
                                        span: ctx.ast.get_node(*expr_ref).span,
                                    });
                                    1
                                } else {
                                    val as u32
                                }
                            }
                        } else {
                            ctx.report_error(SemanticError::NonConstantAlignment {
                                span: ctx.ast.get_node(*expr_ref).span,
                            });
                            1
                        }
                    }
                };

                // "The alignment of the object is that of the strictest alignment specified"
                info.alignment = Some(info.alignment.unwrap_or(0).max(align));
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
            let is_definition = members.is_some();
            let type_ref = resolve_record_tag(ctx, *tag, *is_union, is_definition, span)?;

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

    let final_type = apply_parsed_declarator_recursive(base_type_ref.ty(), declarator_ref, ctx);
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
                let entry = ctx.symbol_table.get_symbol(entry_ref);

                if entry.is_completed {
                    // Redeclaration error - for now just return the type
                    // The caller might want to check this, but consistent with existing logic we just return it
                    Ok(entry.type_info)
                } else {
                    // Completing a forward declaration in current scope
                    Ok(entry.type_info)
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
                Ok(entry.type_info)
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
                Ok(type_info)
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
                Ok(entry.type_info)
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
fn resolve_type_specifier(ts: &TypeSpecifier, ctx: &mut LowerCtx, span: SourceSpan) -> Result<QualType, SemanticError> {
    match ts {
        TypeSpecifier::Void => Ok(QualType::unqualified(ctx.registry.type_void)),
        TypeSpecifier::Char => Ok(QualType::unqualified(ctx.registry.type_char)),
        TypeSpecifier::Short => Ok(QualType::unqualified(ctx.registry.type_short)),
        TypeSpecifier::Int => Ok(QualType::unqualified(ctx.registry.type_int)),
        TypeSpecifier::Long => Ok(QualType::unqualified(ctx.registry.type_long)),
        TypeSpecifier::LongLong => Ok(QualType::unqualified(ctx.registry.type_long_long)),
        TypeSpecifier::Float => Ok(QualType::unqualified(ctx.registry.type_float)),
        TypeSpecifier::Double => Ok(QualType::unqualified(ctx.registry.type_double)),
        TypeSpecifier::LongDouble => Ok(QualType::unqualified(ctx.registry.type_long_double)),
        TypeSpecifier::Signed => {
            // Signed modifier - for now, default to signed int
            Ok(QualType::unqualified(ctx.registry.type_int))
        }
        TypeSpecifier::Unsigned => {
            // Unsigned modifier - return a special marker type that will be handled in merge_base_type
            Ok(QualType::unqualified(ctx.registry.type_int_unsigned))
        }
        TypeSpecifier::Bool => Ok(QualType::unqualified(ctx.registry.type_bool)),
        TypeSpecifier::Complex => {
            // Complex types need a base type
            // For now, default to complex double
            let complex_type = ctx.registry.complex_type(ctx.registry.type_double);
            Ok(QualType::unqualified(complex_type))
        }
        TypeSpecifier::Atomic(parsed_type) => {
            // Convert the ParsedType to a TypeRef by applying the declarator to the base type
            // Use the convert_parsed_type_to_type_ref function to handle this properly
            convert_parsed_type_to_qual_type(ctx, *parsed_type, span)
        }
        TypeSpecifier::Record(is_union, tag, definition) => {
            let is_definition = definition.is_some();
            let type_ref = resolve_record_tag(ctx, *tag, *is_union, is_definition, span)?;

            // Now handle members if it's a definition
            if let Some(def) = definition {
                let members = def
                    .members
                    .as_ref()
                    .map(|decls| lower_struct_members(decls, ctx, span))
                    .unwrap_or_default();

                complete_record_symbol(ctx, *tag, type_ref, members)?;
            }

            Ok(QualType::unqualified(type_ref))
        }
        TypeSpecifier::Enum(tag, enumerators) => {
            let is_definition = enumerators.is_some();
            let type_ref_to_use = resolve_enum_tag(ctx, *tag, is_definition, span)?;

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
                        let _ = ctx
                            .symbol_table
                            .define_enum_constant(*name, value, type_ref_to_use, enum_node.span);
                    }
                }

                complete_enum_symbol(ctx, *tag, type_ref_to_use, enumerators_list)?;
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
                Ok(QualType::unqualified(ctx.registry.declare_record(Some(*name), false)))
            }
        }
    }
}

/// Merge base types according to C type combination rules
fn merge_base_type(existing: Option<QualType>, new_type: QualType, ctx: &mut LowerCtx) -> Option<QualType> {
    match existing {
        None => Some(new_type),
        Some(existing_ref) => {
            let existing_type = ctx.registry.get(existing_ref.ty());
            let new_type_info = ctx.registry.get(new_type.ty());

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
                    Some(QualType::unqualified(ctx.registry.type_char_unsigned))
                }
                (TypeKind::Char { is_signed: false }, TypeKind::Int { is_signed: true }) => {
                    Some(existing_ref) // Keep unsigned char
                }

                // Handle short type merging
                (TypeKind::Short { is_signed: true }, TypeKind::Int { is_signed: false }) => {
                    // unsigned short = short + unsigned
                    Some(QualType::unqualified(ctx.registry.type_short_unsigned))
                }
                (TypeKind::Short { is_signed: false }, TypeKind::Int { is_signed: true }) => {
                    Some(existing_ref) // Keep unsigned short
                }

                // Handle unsigned + char/short order
                (TypeKind::Int { is_signed: false }, TypeKind::Char { is_signed: true }) => {
                    // unsigned char = unsigned + char
                    Some(QualType::unqualified(ctx.registry.type_char_unsigned))
                }
                (TypeKind::Int { is_signed: false }, TypeKind::Short { is_signed: true }) => {
                    // unsigned short = unsigned + short
                    Some(QualType::unqualified(ctx.registry.type_short_unsigned))
                }

                // Handle unsigned + long/long long order
                (
                    TypeKind::Int { is_signed: false },
                    TypeKind::Long {
                        is_long_long: false, ..
                    },
                ) => {
                    // unsigned long = unsigned + long
                    Some(QualType::unqualified(ctx.registry.type_long_unsigned))
                }
                (TypeKind::Int { is_signed: false }, TypeKind::Long { is_long_long: true, .. }) => {
                    // unsigned long long = unsigned + long long
                    Some(QualType::unqualified(ctx.registry.type_long_long_unsigned))
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
                ty: record_type.ty(),
                members: {
                    if let TypeKind::Record { members, .. } = &ctx.registry.get(record_type.ty()).kind {
                        members
                            .iter()
                            .map(|m| FieldDeclData {
                                name: m.name,
                                ty: m.member_type,
                            })
                            .collect()
                    } else {
                        Vec::new()
                    }
                },
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

            // Create EnumDecl semantic node
            let enum_decl = EnumDeclData {
                name: *tag,
                ty: enum_type.ty(),
                members: if let TypeKind::Enum { enumerators, .. } = &ctx.registry.get(enum_type.ty()).kind {
                    enumerators
                        .iter()
                        .map(|e| EnumMember {
                            name: e.name,
                            value: e.value,
                            span: e.span,
                        })
                        .collect()
                } else {
                    Vec::new()
                },
            };

            let enum_node = Node::new(NodeKind::EnumDecl(enum_decl), span);
            Some(ctx.ast.push_node(enum_node))
        }
        _ => None,
    }
}

/// Check if a declarator represents a function declaration (not just a function pointer)
fn is_function_declarator(declarator: &Declarator) -> bool {
    match declarator {
        Declarator::Function { .. } => true,
        Declarator::Pointer(_, Some(inner)) => is_function_declarator(inner),
        _ => false,
    }
}

/// Create the semantic node data for an init-declarator without adding it to the AST
fn create_semantic_node_data(
    ctx: &mut LowerCtx,
    spec: &DeclSpecInfo,
    init: InitDeclarator,
    span: SourceSpan,
) -> NodeKind {
    // 1. Resolve final type (base + declarator)
    let base_ty = spec.base_type.unwrap_or_else(|| {
        ctx.report_error(SemanticError::MissingTypeSpecifier { span });
        QualType::unqualified(ctx.registry.type_error)
    });

    let name = extract_identifier(&init.declarator).expect("Anonymous declarations unsupported");

    // For simple identifiers without qualifiers, don't create a new type entry
    let mut final_ty = if let Declarator::Identifier(_, qualifiers) = &init.declarator {
        if qualifiers.is_empty() {
            // Simple case: just use the base type directly
            base_ty
        } else {
            // Has qualifiers, need to apply declarator
            apply_declarator(base_ty.ty(), &init.declarator, ctx)
        }
    } else {
        // Complex case: apply declarator transformations and create new type
        apply_declarator(base_ty.ty(), &init.declarator, ctx)
    };

    // Check for incomplete array with initializer and deduce size
    // We need to extract info first to avoid borrow conflicts with ctx.registry
    let array_deduction_info = {
        if final_ty.is_array() {
            let ty = ctx.registry.get(final_ty.ty());
            if let TypeKind::Array {
                element_type,
                size: ArraySizeType::Incomplete,
            } = &ty.kind
            {
                Some(*element_type)
            } else {
                None
            }
        } else {
            None
        }
    };

    if let Some(element_type) = array_deduction_info
        && let Some(init_node) = init.initializer
        && let Some(new_size) = deduce_array_size(ctx, init_node)
    {
        let new_ty_ref = ctx.registry.array_of(element_type, ArraySizeType::Constant(new_size));

        // Preserve qualifiers from the original type
        final_ty = QualType::new(new_ty_ref, final_ty.qualifiers());

        // Ensure layout is computed for the new type so sizeof() works
        let _ = ctx.registry.ensure_layout(new_ty_ref);
    }

    // 2. Handle typedefs
    if spec.is_typedef {
        let typedef_decl = TypedefDeclData { name, ty: final_ty };

        // Add typedef to symbol table to resolve forward references
        if let Err(e) = ctx.symbol_table.define_typedef(name, final_ty.ty(), span) {
            let SymbolTableError::InvalidRedefinition { name, existing } = e;
            let existing_symbol = ctx.symbol_table.get_symbol(existing);
            ctx.report_error(SemanticError::Redefinition {
                name,
                first_def: existing_symbol.def_span,
                span,
            });
        }

        return NodeKind::TypedefDecl(typedef_decl);
    }

    // 3. Distinguish between functions and variables
    // Check if the declarator is a function declarator (even if the final type is pointer to function)
    let is_function = is_function_declarator(&init.declarator);

    if is_function {
        // Extract function type information
        // Optimization: avoid cloning Type if possible, use TypeRef checks
        let final_ty_ref = final_ty.ty();

        let function_type_ref = if final_ty_ref.is_function() {
            final_ty_ref
        } else {
            // Not a function type (variable, pointer, function pointer, etc.)
            let var_decl = VarDeclData {
                name,
                ty: final_ty,
                storage: spec.storage,
                init: init.initializer,
                alignment: spec.alignment,
            };

            if let Err(e) =
                ctx.symbol_table
                    .define_variable(name, final_ty.ty(), init.initializer, spec.alignment, span)
            {
                let SymbolTableError::InvalidRedefinition { name, existing } = e;
                let existing = ctx.symbol_table.get_symbol(existing);
                ctx.diag.report(SemanticError::Redefinition {
                    name,
                    first_def: existing.def_span,
                    span,
                });
            }

            return NodeKind::VarDecl(var_decl);
        };

        let func_decl = FunctionDeclData {
            name,
            ty: function_type_ref, // Use the function type, not the pointer to function type
            storage: spec.storage,
            body: None,
        };

        if let Err(e) = ctx.symbol_table.define_function(name, function_type_ref, false, span) {
            let SymbolTableError::InvalidRedefinition { name, existing } = e;
            let existing = ctx.symbol_table.get_symbol(existing);
            ctx.diag.report(SemanticError::Redefinition {
                name,
                first_def: existing.def_span,
                span,
            });
        }

        NodeKind::FunctionDecl(func_decl)
    } else {
        let var_decl = VarDeclData {
            name,
            ty: final_ty,
            storage: spec.storage,
            init: init.initializer,
            alignment: spec.alignment,
        };

        if let Err(e) = ctx
            .symbol_table
            .define_variable(name, final_ty.ty(), init.initializer, spec.alignment, span)
        {
            let SymbolTableError::InvalidRedefinition { name, existing } = e;
            let existing = ctx.symbol_table.get_symbol(existing);
            ctx.diag.report(SemanticError::Redefinition {
                name,
                first_def: existing.def_span,
                span,
            });
        }

        NodeKind::VarDecl(var_decl)
    }
}

fn lower_function_parameters(params: &[ParamData], ctx: &mut LowerCtx) -> Vec<FunctionParameter> {
    params
        .iter()
        .map(|param| {
            let span = param.span;
            let spec_info = lower_decl_specifiers(&param.specifiers, ctx, span);

            // C standard: if type specifier is missing in a parameter, it defaults to int.
            let base_ty = spec_info
                .base_type
                .unwrap_or_else(|| QualType::unqualified(ctx.registry.type_int));

            let final_ty = if let Some(declarator) = &param.declarator {
                apply_declarator(base_ty.ty(), declarator, ctx)
            } else {
                base_ty
            };

            // Apply array-to-pointer decay for function parameters (C11 6.7.6.3)
            let decayed_ty = ctx.registry.decay(final_ty);

            FunctionParameter {
                param_type: decayed_ty,
                name: param.declarator.as_ref().and_then(extract_identifier),
            }
        })
        .collect()
}

/// Apply declarator transformations to a base type
pub(crate) fn apply_declarator(base_type: TypeRef, declarator: &Declarator, ctx: &mut LowerCtx) -> QualType {
    match declarator {
        Declarator::Pointer(qualifiers, next) => {
            let pointer_type_ref = ctx.registry.pointer_to(base_type);

            if let Some(next_decl) = next {
                let result = apply_declarator(pointer_type_ref, next_decl, ctx);
                ctx.registry.merge_qualifiers(result, *qualifiers)
            } else {
                QualType::new(pointer_type_ref, *qualifiers)
            }
        }
        Declarator::Identifier(_, qualifiers) => {
            let base_type_ref = base_type;
            ctx.registry
                .merge_qualifiers(QualType::unqualified(base_type_ref), *qualifiers)
        }
        Declarator::Array(base, size) => {
            let array_size = match size {
                ArraySize::Expression { expr, qualifiers: _ } => resolve_array_size(Some(*expr), ctx),
                ArraySize::Star { qualifiers: _ } => ArraySizeType::Star,
                ArraySize::Incomplete => ArraySizeType::Incomplete,
                ArraySize::VlaSpecifier {
                    is_static: _,
                    qualifiers: _,
                    size,
                } => resolve_array_size(*size, ctx),
            };

            let array_type_ref = ctx.registry.array_of(base_type, array_size);
            apply_declarator(array_type_ref, base, ctx)
        }
        Declarator::Function {
            inner: base,
            params,
            is_variadic,
        } => {
            let parameters = lower_function_parameters(params, ctx);
            let function_type_ref = ctx.registry.function_type(base_type, parameters, *is_variadic);
            apply_declarator(function_type_ref, base, ctx)
        }
        Declarator::AnonymousRecord(is_union, members) => {
            // Create a new record type for the anonymous struct/union
            let record_type_ref = ctx.registry.declare_record(None, *is_union);

            // Process members using the extracted logic
            // Use the current node's span if available (we don't have it directly here, so we rely on members' spans mostly)
            // But we need a span for lower_struct_members. We can use SourceSpan::empty() if we don't have one,
            // or pass it down. apply_declarator doesn't take span.
            // However, members themselves have spans in DeclarationData.
            let struct_members = lower_struct_members(members, ctx, SourceSpan::empty());

            // Complete the record type
            ctx.registry.complete_record(record_type_ref, struct_members);

            if let Err(e) = ctx.registry.ensure_layout(record_type_ref) {
                ctx.report_error(e);
                QualType::unqualified(ctx.registry.type_error)
            } else {
                // Return the new record type
                QualType::unqualified(record_type_ref)
            }
        }
        Declarator::BitField(base, _) => {
            // TODO: Handle bit fields
            apply_declarator(base_type, base, ctx)
        }
        Declarator::Abstract => QualType::unqualified(base_type),
    }
}

/// Finalize tentative definitions by converting them to defined state
/// This implements C11 6.9.2 semantics for tentative definitions
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

/// Main entry point for running semantic lowering on an entire AST
pub(crate) fn run_symbol_resolver(
    ast: &mut Ast,
    diag: &mut DiagnosticEngine,
    symbol_table: &mut SymbolTable,
    registry: &mut TypeRegistry,
) -> Vec<Option<ScopeId>> {
    // Check if we have a root node to start traversal from
    let node_length = ast.nodes.len();
    let root_node_ref = ast.get_root();

    // Finalize tentative definitions before any processing
    // This must happen before creating the LowerCtx to avoid borrow conflicts
    finalize_tentative_definitions(symbol_table);

    // Create lowering context
    let mut lower_ctx = LowerCtx::new(ast, diag, symbol_table, registry);

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
                    .unwrap_or_else(|| QualType::unqualified(ctx.registry.type_int));

            // Create the function type with the correct return type by applying the declarator
            let declarator_type = apply_parsed_declarator(return_type_ref.ty(), &func_def.declarator, ctx);
            let function_type_ref = declarator_type.ty();

            // Extract parameters from the function type for the symbol entry
            // This still requires accessing the registry because params are stored in TypeKind::Function
            let parameters = if let TypeKind::Function { parameters, .. } = &ctx.registry.get(function_type_ref).kind {
                parameters.clone()
            } else {
                Vec::new()
            };

            let symbol_entry_ref = ctx
                .symbol_table
                .define_function(
                    func_name,
                    function_type_ref,
                    true, // is_definition
                    ctx.ast.get_node(node_ref).span,
                )
                .expect("Function definition failed");

            let param_scope_id = ctx.symbol_table.push_scope();
            ctx.set_scope(node_ref, param_scope_id);

            // Create normalized parameters for the FunctionData
            let normalized_params = parameters
                .into_iter()
                .map(|param| {
                    // Create a symbol entry for the parameter
                    let param_symbol_ref = ctx
                        .symbol_table
                        .define_variable(
                            param.name.unwrap_or_else(|| NameId::new("unnamed_param")),
                            param.param_type.ty(),
                            None, // No initializer
                            None, // No alignment
                            ctx.ast.get_node(node_ref).span,
                        )
                        .unwrap();

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
                    // Single declarator case: replace the original declaration node with the semantic node data
                    let semantic_node_kind = semantic_nodes[0].clone();
                    let original_span = ctx.ast.get_node(node_ref).span;
                    ctx.ast
                        .replace_node(node_ref, Node::new(semantic_node_kind, original_span));
                    // After replacement, recurse into the semantic node to process its children
                    if let NodeKind::VarDecl(var_decl) = &semantic_nodes[0]
                        && let Some(init_expr) = var_decl.init
                    {
                        lower_node_recursive(ctx, init_expr);
                    }
                } else {
                    // Multi-declarator case: create a DeclarationList containing all semantic nodes
                    let original_span = ctx.ast.get_node(node_ref).span;
                    let semantic_node_refs: Vec<NodeRef> = semantic_nodes
                        .into_iter()
                        .map(|kind| ctx.ast.push_node(Node::new(kind, original_span)))
                        .collect();
                    let compound_node = Node::new(NodeKind::DeclarationList(semantic_node_refs), original_span);
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
            lower_node_recursive(ctx, if_stmt.condition);
            lower_node_recursive(ctx, if_stmt.then_branch);
            if let Some(else_branch) = if_stmt.else_branch {
                lower_node_recursive(ctx, else_branch);
            }
        }
        NodeKind::While(while_stmt) => {
            lower_node_recursive(ctx, while_stmt.condition);
            lower_node_recursive(ctx, while_stmt.body);
        }
        NodeKind::DoWhile(body, condition) => {
            lower_node_recursive(ctx, body);
            lower_node_recursive(ctx, condition);
        }
        NodeKind::Label(name, stmt, _) => {
            let label_ty = ctx.registry.type_void; // void for now
            let _ = ctx
                .symbol_table
                .define_label(name, label_ty, ctx.ast.get_node(node_ref).span);
            lower_node_recursive(ctx, stmt);
        }
        NodeKind::ParsedCast(parsed_type, expr_node) => {
            // Convert ParsedType to TypeRef
            let type_ref = convert_parsed_type_to_qual_type(ctx, parsed_type, ctx.ast.get_node(node_ref).span)
                .unwrap_or_else(|_| {
                    // Create an error type if conversion fails
                    QualType::unqualified(ctx.registry.type_error)
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
                    QualType::unqualified(ctx.registry.type_error)
                });

            // Ensure the type is complete before allowing sizeof
            if let Err(e) = ctx.registry.ensure_layout(type_ref.ty()) {
                ctx.report_error(e);
            }

            // Replace the ParsedSizeOfType node with a SizeOfType node
            let size_of_node = Node::new(NodeKind::SizeOfType(type_ref), ctx.ast.get_node(node_ref).span);
            ctx.ast.replace_node(node_ref, size_of_node);
        }
        NodeKind::ParsedCompoundLiteral(parsed_type, initializer_node) => {
            // Convert ParsedType to TypeRef
            let type_ref = convert_parsed_type_to_qual_type(ctx, parsed_type, ctx.ast.get_node(node_ref).span)
                .unwrap_or_else(|_| {
                    // Create an error type if conversion fails
                    QualType::unqualified(ctx.registry.type_error)
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
                    QualType::unqualified(ctx.registry.type_error)
                });
            // Replace the ParsedAlignOf node with an AlignOf node
            let align_of_node = Node::new(NodeKind::AlignOf(type_ref), ctx.ast.get_node(node_ref).span);
            ctx.ast.replace_node(node_ref, align_of_node);
        }
        // Expression nodes - recurse into subexpressions
        NodeKind::UnaryOp(_, expr) => {
            lower_node_recursive(ctx, expr);
        }
        NodeKind::BinaryOp(_, left, right) => {
            lower_node_recursive(ctx, left);
            lower_node_recursive(ctx, right);
        }
        NodeKind::TernaryOp(cond, then_branch, else_branch) => {
            lower_node_recursive(ctx, cond);
            lower_node_recursive(ctx, then_branch);
            lower_node_recursive(ctx, else_branch);
        }
        NodeKind::FunctionCall(func, args) => {
            lower_node_recursive(ctx, func);
            for arg in args {
                lower_node_recursive(ctx, arg);
            }
        }
        NodeKind::MemberAccess(obj, _, _) => {
            lower_node_recursive(ctx, obj);
        }
        NodeKind::IndexAccess(arr, idx) => {
            lower_node_recursive(ctx, arr);
            lower_node_recursive(ctx, idx);
        }
        NodeKind::Cast(_, expr) => {
            lower_node_recursive(ctx, expr);
        }
        NodeKind::SizeOfExpr(expr) => {
            lower_node_recursive(ctx, expr);
        }
        NodeKind::SizeOfType(_) => {
            // Already resolved, no subexpressions
        }
        NodeKind::AlignOf(_) => {
            // Already resolved, no subexpressions
        }
        NodeKind::CompoundLiteral(_, init) => {
            lower_node_recursive(ctx, init);
        }
        NodeKind::ParsedGenericSelection(ctrl, assocs) => {
            lower_node_recursive(ctx, ctrl);
            let mut resolved_assocs = Vec::new();
            for assoc in assocs {
                lower_node_recursive(ctx, assoc.result_expr);
                let ty = match assoc.type_name {
                    Some(parsed_type) => {
                        match convert_parsed_type_to_qual_type(ctx, parsed_type, ctx.ast.get_node(node_ref).span) {
                            Ok(ty) => Some(ty),
                            Err(e) => {
                                ctx.report_error(e);
                                Some(QualType::unqualified(ctx.registry.type_error))
                            }
                        }
                    }
                    None => None,
                };
                resolved_assocs.push(ResolvedGenericAssociation {
                    ty,
                    result_expr: assoc.result_expr,
                });
            }
            let generic_node = Node::new(
                NodeKind::GenericSelection(ctrl, resolved_assocs),
                ctx.ast.get_node(node_ref).span,
            );
            ctx.ast.replace_node(node_ref, generic_node);
        }
        // Statement nodes that contain expressions
        NodeKind::ExpressionStatement(Some(expr)) => {
            lower_node_recursive(ctx, expr);
        }
        NodeKind::Return(Some(expr)) => {
            lower_node_recursive(ctx, expr);
        }
        NodeKind::Case(expr, stmt) => {
            lower_node_recursive(ctx, expr);
            lower_node_recursive(ctx, stmt);
        }
        NodeKind::CaseRange(start, end, stmt) => {
            lower_node_recursive(ctx, start);
            lower_node_recursive(ctx, end);
            lower_node_recursive(ctx, stmt);
        }
        NodeKind::Default(stmt) => {
            lower_node_recursive(ctx, stmt);
        }
        NodeKind::Switch(expr, body) => {
            lower_node_recursive(ctx, expr);
            lower_node_recursive(ctx, body);
        }
        // More expression nodes
        NodeKind::Assignment(_, lhs, rhs) => {
            lower_node_recursive(ctx, lhs);
            lower_node_recursive(ctx, rhs);
        }
        NodeKind::PostIncrement(expr) => {
            lower_node_recursive(ctx, expr);
        }
        NodeKind::PostDecrement(expr) => {
            lower_node_recursive(ctx, expr);
        }
        NodeKind::GnuStatementExpression(compound, result) => {
            lower_node_recursive(ctx, compound);
            lower_node_recursive(ctx, result);
        }
        NodeKind::VaArg(expr, _) => {
            lower_node_recursive(ctx, expr);
        }
        NodeKind::InitializerList(designated_inits) => {
            for designated_init in designated_inits {
                lower_node_recursive(ctx, designated_init.initializer);
                for designator in &designated_init.designation {
                    if let crate::ast::Designator::ArrayIndex(idx_expr) = designator {
                        lower_node_recursive(ctx, *idx_expr);
                    }
                }
            }
        }
        NodeKind::VarDecl(var_decl) => {
            // Recurse into initializer if present
            if let Some(init_expr) = var_decl.init {
                lower_node_recursive(ctx, init_expr);
            }
        }
        NodeKind::FunctionDecl(_) | NodeKind::TypedefDecl(_) | NodeKind::RecordDecl(_) | NodeKind::EnumDecl(_) => {
            // These semantic nodes don't have child expressions to lower
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
    let info = lower_decl_specifiers(specs, ctx, span);
    // Return types shouldn't have storage classes usually, but here we just want the type.
    info.base_type
        .map(|base| ctx.registry.merge_qualifiers(base, info.qualifiers))
}
