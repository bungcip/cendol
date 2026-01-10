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

use crate::ast::parsed::{ParsedDeclarator, ParsedNodeKind, ParsedNodeRef, ParsedTypeSpecifier};
use crate::ast::*;
use crate::diagnostic::{DiagnosticEngine, SemanticError};
use crate::semantic::const_eval::{self, ConstEvalCtx};
use crate::semantic::struct_lowering::lower_struct_members;
use crate::semantic::symbol_table::DefinitionState;
use crate::semantic::{
    ArraySizeType, EnumConstant, ScopeId, StructMember, SymbolKind, SymbolRef, SymbolTable, TypeKind, TypeQualifiers,
    TypeRef, TypeRegistry,
};
use crate::semantic::{FunctionParameter, QualType};
use crate::source_manager::SourceSpan;

/// Recursively apply parsed declarator to base type
fn apply_parsed_declarator_recursive(
    current_type: TypeRef,
    declarator_ref: ParsedDeclRef,
    ctx: &mut LowerCtx,
) -> QualType {
    let declarator_node = ctx.parsed_ast.parsed_types.get_decl(declarator_ref);

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
            // Array - using ParsedArraySize from convert helper (which needs update)
            let array_size = convert_parsed_array_size(&size, ctx);
            let array_type_ref = ctx.registry.array_of(current_type, array_size);

            apply_parsed_declarator_recursive(array_type_ref, inner, ctx)
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
fn convert_parsed_array_size(size: &ParsedArraySize, ctx: &mut LowerCtx) -> ArraySizeType {
    match size {
        ParsedArraySize::Expression { expr: _, .. } => {
            // Evaluate expression
            let _const_eval_ctx = ConstEvalCtx { ast: ctx.ast }; // Wait, ConstEval works on Ast?
            // Since we construct Ast on fly, we can only evaluate if constants are resolved.
            // But expressions in ParsedAst are ParsedNodeRef. ConstEval expects NodeRef (semantic).
            // This is a Catch-22 unless we lower expression first.
            // For now, defer evaluation or lower expression here.

            // TODO: Lower expression before evaluation
            ArraySizeType::Incomplete
        }
        ParsedArraySize::Star { .. } => ArraySizeType::Star,
        ParsedArraySize::Incomplete => ArraySizeType::Incomplete,
        ParsedArraySize::VlaSpecifier { .. } => ArraySizeType::Incomplete,
    }
}

/// Helper function to resolve array size logic
fn resolve_array_size(_size: Option<ParsedNodeRef>, _ctx: &mut LowerCtx) -> ArraySizeType {
    // Needs to lower and evaluate expression
    // TODO: Implement expression lowering here or defer
    // For now return Incomplete
    ArraySizeType::Incomplete
}

/// Context for the semantic lowering phase
pub(crate) struct LowerCtx<'a, 'src> {
    pub(crate) parsed_ast: &'a ParsedAst,
    pub(crate) ast: &'a mut Ast,
    pub(crate) diag: &'src mut DiagnosticEngine,
    pub(crate) symbol_table: &'a mut SymbolTable,
    pub(crate) scope_map: Vec<Option<ScopeId>>,
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

    fn set_scope(&mut self, node_ref: NodeRef, scope_id: ScopeId) {
        let idx = node_ref.index();
        if idx >= self.scope_map.len() {
            self.scope_map.resize(idx + 1, None);
        }
        self.scope_map[idx] = Some(scope_id);
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
                let parsed_members: Vec<_> = ctx.parsed_ast.parsed_types.get_struct_members(*members_range).to_vec();

                // Process member types separately to avoid borrowing conflicts
                let mut member_types = Vec::new();
                for parsed_member in &parsed_members {
                    let member_type_ref = convert_to_qual_type(ctx, parsed_member.ty, span)?;
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
            // Signed modifier - for now, default to signed int
            Ok(QualType::unqualified(ctx.registry.type_int))
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
                        // TODO: Evaluate value_expr_ref
                        // For now check for literal int if possible or 0
                        // But value_expr_ref is ParsedNodeRef.
                        let value = if let Some(v_ref) = value_expr_ref {
                            let val_node = ctx.parsed_ast.get_node(*v_ref);
                            if let ParsedNodeKind::LiteralInt(val) = val_node.kind {
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
        ParsedTypeSpecifier::TypedefName(name) => {
            // Lookup typedef in symbol table
            if let Some((entry_ref, _scope_id)) = ctx.symbol_table.lookup_symbol(*name) {
                let entry = ctx.symbol_table.get_symbol(entry_ref);
                if let SymbolKind::Typedef { aliased_type } = entry.kind {
                    Ok(QualType::unqualified(aliased_type))
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
                if info.storage.is_some() {
                    ctx.report_error(SemanticError::ConflictingStorageClasses { span });
                }
                if *sc == StorageClass::Typedef {
                    info.is_typedef = true;
                }
                info.storage = Some(*sc);
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
            ParsedDeclSpecifier::FunctionSpecifiers(fs) => {
                if fs.contains(FunctionSpecifiers::INLINE) {
                    info.is_inline = true;
                }
                if fs.contains(FunctionSpecifiers::NORETURN) {
                    info.is_noreturn = true;
                }
            }
            ParsedDeclSpecifier::AlignmentSpecifier(_align) => {
                // TODO: Handle alignment
            }
            ParsedDeclSpecifier::TypeSpecifier(ts) => {
                let ty = resolve_type_specifier(ts, ctx, span).unwrap_or_else(|e| {
                    ctx.report_error(e);
                    QualType::unqualified(ctx.registry.type_error)
                });
                info.base_type = merge_base_type(info.base_type, ty, ctx);
            }
            ParsedDeclSpecifier::Attribute => {
                // Ignore attributes for now
            }
        }
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
            let base_ty = spec_info
                .base_type
                .unwrap_or_else(|| QualType::unqualified(ctx.registry.type_int));

            let final_ty = if let Some(declarator) = &param.declarator {
                apply_ast_declarator(base_ty.ty(), declarator, ctx)
            } else {
                base_ty
            };

            // Apply array-to-pointer decay for function parameters (C11 6.7.6.3)
            let decayed_ty = ctx.registry.decay(final_ty);

            FunctionParameter {
                param_type: decayed_ty,
                name: param.declarator.as_ref().and_then(extract_identifier_from_declarator),
            }
        })
        .collect()
}

// Local helper to exact identifier from ParsedDeclarator (duplicate of struct_lowering one, should unify later)
fn extract_identifier_from_declarator(decl: &ParsedDeclarator) -> Option<NameId> {
    match decl {
        ParsedDeclarator::Identifier(name, _) => Some(*name),
        ParsedDeclarator::Pointer(_, inner) => inner.as_ref().and_then(|d| extract_identifier_from_declarator(d)),
        ParsedDeclarator::Array(inner, _) => extract_identifier_from_declarator(inner),
        ParsedDeclarator::Function { inner, .. } => extract_identifier_from_declarator(inner),
        ParsedDeclarator::BitField(inner, _) => extract_identifier_from_declarator(inner),
        _ => None,
    }
}

/// Apply declarator transformations to a base type
pub(crate) fn apply_ast_declarator(base_type: TypeRef, declarator: &ParsedDeclarator, ctx: &mut LowerCtx) -> QualType {
    match declarator {
        ParsedDeclarator::Pointer(qualifiers, next) => {
            let pointer_type_ref = ctx.registry.pointer_to(base_type);

            if let Some(next_decl) = next {
                let result = apply_ast_declarator(pointer_type_ref, next_decl, ctx);
                ctx.registry.merge_qualifiers(result, *qualifiers)
            } else {
                QualType::new(pointer_type_ref, *qualifiers)
            }
        }
        ParsedDeclarator::Identifier(_, qualifiers) => {
            let base_type_ref = base_type;
            ctx.registry
                .merge_qualifiers(QualType::unqualified(base_type_ref), *qualifiers)
        }
        ParsedDeclarator::Array(base, size) => {
            let array_size = match size {
                ParsedArraySize::Expression { expr, qualifiers: _ } => resolve_array_size(Some(*expr), ctx), // TODO: resolve_array_size needs ParsedNodeRef support
                ParsedArraySize::Star { qualifiers: _ } => ArraySizeType::Star,
                ParsedArraySize::Incomplete => ArraySizeType::Incomplete,
                ParsedArraySize::VlaSpecifier {
                    is_static: _,
                    qualifiers: _,
                    size,
                } => resolve_array_size(*size, ctx),
            };

            let array_type_ref = ctx.registry.array_of(base_type, array_size);
            apply_ast_declarator(array_type_ref, base, ctx)
        }
        ParsedDeclarator::Function {
            inner: base,
            params,
            is_variadic,
        } => {
            let parameters = lower_function_parameters(params, ctx);
            let function_type_ref = ctx.registry.function_type(base_type, parameters, *is_variadic);
            apply_ast_declarator(function_type_ref, base, ctx)
        }
        ParsedDeclarator::AnonymousRecord(is_union, members) => {
            // Use struct_lowering helper
            let record_type_ref = ctx.registry.declare_record(None, *is_union);
            let struct_members =
                crate::semantic::struct_lowering::lower_struct_members(members, ctx, SourceSpan::empty());
            ctx.registry.complete_record(record_type_ref, struct_members);
            let _ = ctx.registry.ensure_layout(record_type_ref);
            QualType::unqualified(record_type_ref)
        }
        ParsedDeclarator::BitField(base, _) => {
            // Bitfield logic handled in struct lowering usually. Here just type application.
            apply_ast_declarator(base_type, base, ctx)
        }
        ParsedDeclarator::Abstract => QualType::unqualified(base_type),
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

/// Main entry point for running symbol resolution on ParsedAst
pub(crate) fn run_symbol_resolver(
    parsed_ast: &ParsedAst,
    ast: &mut Ast,
    diag: &mut DiagnosticEngine,
    symbol_table: &mut SymbolTable,
    registry: &mut TypeRegistry,
) -> Vec<Option<ScopeId>> {
    // Check if we have a root node to start traversal from
    let root_node_ref = parsed_ast.get_root();

    // We also resize the semantic AST to hold expected number of nodes? No, we build it.
    // But we need scope map for SEMANTIC nodes.
    // We can't pre-size it easily because 1 parsed declaration -> N semantic declarations.
    // We'll let it grow.
    let _scope_map: Vec<Option<ScopeId>> = Vec::new();

    // Finalize tentative definitions
    finalize_tentative_definitions(symbol_table);

    // Create lowering context
    let mut lower_ctx = LowerCtx::new(parsed_ast, ast, diag, symbol_table, registry);

    // Perform recursive scope-aware lowering starting from root
    let semantic_roots = lower_ctx.lower_node_recursive(root_node_ref);

    // The result of lower_node_recursive(root) should be TranslationUnit(s).
    // But the Parser produces ONE TranslationUnit node.
    // All children are TopLevels.

    // We need to set the root of semantic AST.
    // The recursive call on Root (TranslationUnit) checks NodeKind::TranslationUnit and returns a new TranslationUnit node.
    if let Some(root) = semantic_roots.first() {
        lower_ctx.ast.set_root(*root);
    }

    lower_ctx.scope_map
}

impl<'a, 'src> LowerCtx<'a, 'src> {
    pub(crate) fn lower_node_recursive(&mut self, parsed_ref: ParsedNodeRef) -> Vec<NodeRef> {
        let parsed_node = self.parsed_ast.get_node(parsed_ref);
        let span = parsed_node.span;
        let kind = parsed_node.kind.clone();

        match kind {
            ParsedNodeKind::TranslationUnit(children) => {
                self.symbol_table.set_current_scope(ScopeId::GLOBAL);
                let mut semantic_children = Vec::new();
                for child in children {
                    let lowered = self.lower_node_recursive(child);
                    semantic_children.extend(lowered);
                }
                let tu_node = self.ast.push_node(NodeKind::TranslationUnit(semantic_children), span);
                self.set_scope(tu_node, ScopeId::GLOBAL);
                vec![tu_node]
            }
            ParsedNodeKind::CompoundStatement(stmts) => {
                let scope_id = self.symbol_table.push_scope();
                let mut semantic_stmts = Vec::new();
                for stmt in stmts {
                    semantic_stmts.extend(self.lower_node_recursive(stmt));
                }
                self.symbol_table.pop_scope();

                let node = self.ast.push_node(NodeKind::CompoundStatement(semantic_stmts), span);
                self.set_scope(node, scope_id);
                vec![node]
            }
            ParsedNodeKind::Declaration(decl_data) => {
                let mut nodes = Vec::new();
                let spec_info = lower_decl_specifiers(&decl_data.specifiers, self, span);

                if decl_data.init_declarators.is_empty() {
                    if let Some(ty) = spec_info.base_type {
                        // Extract needed data from registry to avoid borrowing self.registry during node creation
                        let record_data =
                            if let crate::semantic::types::TypeKind::Record {
                                tag, members, is_union, ..
                            } = &self.registry.get(ty.ty()).kind
                            {
                                Some((*tag, members.clone(), *is_union))
                            } else {
                                None
                            };

                        if let Some((tag, members, is_union)) = record_data {
                            // Reserve slot for RecordDecl to ensure parent < child index
                            let record_decl_idx = self.ast.push_node(NodeKind::Dummy, span);

                            let mut member_len = 0u16;
                            // We need to capture the start if there are members.
                            let member_start_idx = self.ast.kinds.len() as u32 + 1; // 1-based index
                            let member_start = NodeRef::new(member_start_idx).expect("NodeRef overflow");

                            for m in members {
                                let field_data = crate::ast::nodes::FieldDeclData {
                                    name: m.name,
                                    ty: m.member_type,
                                };
                                let field_node = self.ast.push_node(
                                    NodeKind::FieldDecl(field_data),
                                    m.span, // Use member span
                                );
                                self.set_scope(field_node, self.symbol_table.current_scope());
                                member_len += 1;
                            }

                            // Replace the reserved dummy node with the actual RecordDecl
                            self.ast.kinds[record_decl_idx.index()] =
                                NodeKind::RecordDecl(crate::ast::nodes::RecordDeclData {
                                    name: tag,
                                    ty: ty.ty(),
                                    member_start,
                                    member_len,
                                    is_union,
                                });

                            self.set_scope(record_decl_idx, self.symbol_table.current_scope());

                            return vec![record_decl_idx];
                        }

                        // Handle Enum
                        let enum_data = if let crate::semantic::types::TypeKind::Enum { tag, enumerators, .. } =
                            &self.registry.get(ty.ty()).kind
                        {
                            Some((*tag, enumerators.clone()))
                        } else {
                            None
                        };

                        if let Some((tag, enumerators)) = enum_data {
                            let members = enumerators
                                .iter()
                                .map(|e| crate::ast::nodes::EnumMember {
                                    name: e.name,
                                    value: e.value,
                                    span: e.span,
                                })
                                .collect();
                            let node = self.ast.push_node(
                                NodeKind::EnumDecl(EnumDeclData {
                                    name: tag,
                                    ty: ty.ty(),
                                    members,
                                }),
                                span,
                            );
                            self.set_scope(node, self.symbol_table.current_scope());
                            return vec![node];
                        }
                    }
                    return vec![];
                }

                for init in decl_data.init_declarators {
                    let base_ty = spec_info.base_type.unwrap_or_else(|| {
                        self.report_error(SemanticError::MissingTypeSpecifier { span });
                        QualType::unqualified(self.registry.type_error)
                    });

                    let final_ty = apply_ast_declarator(base_ty.ty(), &init.declarator, self);
                    let name = extract_identifier_from_declarator(&init.declarator)
                        .expect("Anonymous declaration unsupported");

                    if spec_info.is_typedef {
                        if let Err(_e) = self.symbol_table.define_typedef(name, final_ty.ty(), span) {
                            self.report_error(SemanticError::Redefinition {
                                name,
                                first_def: span,
                                span,
                            });
                        }
                        let node = self
                            .ast
                            .push_node(NodeKind::TypedefDecl(TypedefDeclData { name, ty: final_ty }), span);
                        self.set_scope(node, self.symbol_table.current_scope());
                        nodes.push(node);
                        continue;
                    }

                    let init_expr = init.initializer.map(|init_node| self.lower_expression(init_node));

                    let is_func = matches!(init.declarator, ParsedDeclarator::Function { .. });

                    if is_func {
                        let func_decl = FunctionDeclData {
                            name,
                            ty: final_ty.ty(),
                            storage: spec_info.storage,
                            body: None,
                        };
                        if let Err(crate::semantic::symbol_table::SymbolTableError::InvalidRedefinition {
                            existing,
                            ..
                        }) = self.symbol_table.define_function(name, final_ty.ty(), false, span)
                        {
                            let first_def = self.symbol_table.get_symbol(existing).def_span;
                            self.report_error(SemanticError::Redefinition { name, first_def, span });
                        }
                        let node = self.ast.push_node(NodeKind::FunctionDecl(func_decl), span);
                        self.set_scope(node, self.symbol_table.current_scope());
                        nodes.push(node);
                    } else {
                        // Array size deduction from initializer
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
                            alignment: spec_info.alignment,
                        };
                        if let Err(crate::semantic::symbol_table::SymbolTableError::InvalidRedefinition {
                            existing,
                            ..
                        }) =
                            self.symbol_table
                                .define_variable(name, final_ty.ty(), init_expr, spec_info.alignment, span)
                        {
                            let first_def = self.symbol_table.get_symbol(existing).def_span;
                            self.report_error(SemanticError::Redefinition { name, first_def, span });
                        }
                        let node = self.ast.push_node(NodeKind::VarDecl(var_decl), span);
                        self.set_scope(node, self.symbol_table.current_scope());
                        nodes.push(node);
                    }
                }
                nodes
            }
            ParsedNodeKind::FunctionDef(func_def) => {
                let spec_info = lower_decl_specifiers(&func_def.specifiers, self, span);
                let base_ty = spec_info
                    .base_type
                    .unwrap_or_else(|| QualType::unqualified(self.registry.type_int));

                let final_ty = apply_ast_declarator(base_ty.ty(), &func_def.declarator, self);
                let func_name = extract_identifier_from_declarator(&func_def.declarator)
                    .expect("Function definition must have a name");

                if let Err(crate::semantic::symbol_table::SymbolTableError::InvalidRedefinition { existing, .. }) =
                    self.symbol_table.define_function(func_name, final_ty.ty(), true, span)
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

                let _scope_id = self.symbol_table.push_scope();

                // Pre-scan labels for forward goto support
                self.collect_labels(func_def.body);

                let parameters = if let TypeKind::Function { parameters, .. } = &self.registry.get(final_ty.ty()).kind {
                    parameters.clone()
                } else {
                    vec![]
                };

                let mut params_decl = Vec::new();
                for param in parameters {
                    if let Some(pname) = param.name
                        && let Ok(sym) =
                            self.symbol_table
                                .define_variable(pname, param.param_type.ty(), None, None, span)
                    {
                        params_decl.push(ParamDecl {
                            symbol: sym,
                            ty: param.param_type,
                        });
                    }
                }

                let body_node = self.lower_single_statement(func_def.body);

                self.symbol_table.pop_scope();

                let node = self.ast.push_node(
                    NodeKind::Function(FunctionData {
                        symbol: func_sym_ref,
                        ty: final_ty.ty(),
                        params: params_decl,
                        body: body_node,
                    }),
                    span,
                );
                self.set_scope(node, self.symbol_table.current_scope());
                vec![node]
            }
            ParsedNodeKind::StaticAssert(expr, msg) => {
                let lowered_expr = self.lower_expression(expr);
                let node = self.ast.push_node(NodeKind::StaticAssert(lowered_expr, msg), span);
                self.set_scope(node, self.symbol_table.current_scope());
                vec![node]
            }
            ParsedNodeKind::If(stmt) => {
                let cond = self.lower_expression(stmt.condition);
                let then = self.lower_single_statement(stmt.then_branch);
                let else_branch = stmt.else_branch.map(|b| self.lower_single_statement(b));
                vec![self.ast.push_node(
                    NodeKind::If(crate::ast::IfStmt {
                        condition: cond,
                        then_branch: then,
                        else_branch,
                    }),
                    span,
                )]
            }
            ParsedNodeKind::While(stmt) => {
                let cond = self.lower_expression(stmt.condition);
                let body = self.lower_single_statement(stmt.body);
                vec![
                    self.ast
                        .push_node(NodeKind::While(crate::ast::WhileStmt { condition: cond, body }), span),
                ]
            }
            ParsedNodeKind::DoWhile(body, cond) => {
                let b = self.lower_single_statement(body);
                let c = self.lower_expression(cond);
                vec![self.ast.push_node(NodeKind::DoWhile(b, c), span)]
            }
            ParsedNodeKind::For(stmt) => {
                let scope_id = self.symbol_table.push_scope();
                let init = stmt
                    .init
                    .map(|i| self.lower_node_recursive(i).first().cloned().unwrap());
                let cond = stmt.condition.map(|c| self.lower_expression(c));
                let inc = stmt.increment.map(|i| self.lower_expression(i));
                let body = self.lower_single_statement(stmt.body);
                self.symbol_table.pop_scope();

                let node = self.ast.push_node(
                    NodeKind::For(crate::ast::ForStmt {
                        init,
                        condition: cond,
                        increment: inc,
                        body,
                    }),
                    span,
                );
                self.set_scope(node, scope_id);
                vec![node]
            }
            ParsedNodeKind::Switch(cond, body) => {
                let c = self.lower_expression(cond);
                let b = self.lower_single_statement(body);
                vec![self.ast.push_node(NodeKind::Switch(c, b), span)]
            }
            ParsedNodeKind::Case(expr, stmt) => {
                let e = self.lower_expression(expr);
                let s = self.lower_single_statement(stmt);
                vec![self.ast.push_node(NodeKind::Case(e, s), span)]
            }
            ParsedNodeKind::CaseRange(start, end, stmt) => {
                let s_expr = self.lower_expression(start);
                let e_expr = self.lower_expression(end);
                let s_stmt = self.lower_single_statement(stmt);
                vec![self.ast.push_node(NodeKind::CaseRange(s_expr, e_expr, s_stmt), span)]
            }
            ParsedNodeKind::Default(stmt) => {
                let s = self.lower_single_statement(stmt);
                vec![self.ast.push_node(NodeKind::Default(s), span)]
            }
            ParsedNodeKind::Break => {
                vec![self.ast.push_node(NodeKind::Break, span)]
            }
            ParsedNodeKind::Continue => {
                vec![self.ast.push_node(NodeKind::Continue, span)]
            }
            ParsedNodeKind::Goto(name) => {
                let sym = self.resolve_label(name, span);
                vec![self.ast.push_node(NodeKind::Goto(name, sym), span)]
            }
            ParsedNodeKind::Label(name, inner) => {
                let sym = self.define_label(name, span);
                let s = self.lower_single_statement(inner);
                vec![self.ast.push_node(NodeKind::Label(name, s, sym), span)]
            }
            ParsedNodeKind::Return(expr) => {
                let e = expr.map(|x| self.lower_expression(x));
                vec![self.ast.push_node(NodeKind::Return(e), span)]
            }
            ParsedNodeKind::ExpressionStatement(expr) => {
                let e = expr.map(|x| self.lower_expression(x));
                vec![self.ast.push_node(NodeKind::ExpressionStatement(e), span)]
            }
            ParsedNodeKind::BinaryOp(op, lhs, rhs) => {
                let l = self.lower_expression(lhs);
                let r = self.lower_expression(rhs);
                vec![self.ast.push_node(NodeKind::BinaryOp(op, l, r), span)]
            }
            ParsedNodeKind::Assignment(op, lhs, rhs) => {
                let l = self.lower_expression(lhs);
                let r = self.lower_expression(rhs);
                vec![self.ast.push_node(NodeKind::Assignment(op, l, r), span)]
            }
            ParsedNodeKind::UnaryOp(op, operand) => {
                let o = self.lower_expression(operand);
                vec![self.ast.push_node(NodeKind::UnaryOp(op, o), span)]
            }
            ParsedNodeKind::LiteralInt(val) => {
                vec![self.ast.push_node(NodeKind::LiteralInt(val), span)]
            }
            ParsedNodeKind::LiteralFloat(val) => {
                vec![self.ast.push_node(NodeKind::LiteralFloat(val), span)]
            }
            ParsedNodeKind::LiteralChar(val) => {
                vec![self.ast.push_node(NodeKind::LiteralChar(val), span)]
            }
            ParsedNodeKind::LiteralString(val) => {
                vec![self.ast.push_node(NodeKind::LiteralString(val), span)]
            }
            ParsedNodeKind::Ident(name) => {
                let sym = self.resolve_ident(name, span);
                vec![self.ast.push_node(NodeKind::Ident(name, sym), span)]
            }
            ParsedNodeKind::FunctionCall(func, args) => {
                let f = self.lower_expression(func);
                let a = args.iter().map(|arg| self.lower_expression(*arg)).collect();
                vec![self.ast.push_node(NodeKind::FunctionCall(f, a), span)]
            }
            ParsedNodeKind::MemberAccess(base, member, is_arrow) => {
                let b = self.lower_expression(base);
                vec![self.ast.push_node(NodeKind::MemberAccess(b, member, is_arrow), span)]
            }
            ParsedNodeKind::Cast(ty_name, expr) => {
                let e = self.lower_expression(expr);
                let ty = convert_to_qual_type(self, ty_name, span)
                    .unwrap_or(QualType::unqualified(self.registry.type_error));
                vec![self.ast.push_node(NodeKind::Cast(ty, e), span)]
            }
            ParsedNodeKind::PostIncrement(operand) => {
                let o = self.lower_expression(operand);
                vec![self.ast.push_node(NodeKind::PostIncrement(o), span)]
            }
            ParsedNodeKind::PostDecrement(operand) => {
                let o = self.lower_expression(operand);
                vec![self.ast.push_node(NodeKind::PostDecrement(o), span)]
            }
            ParsedNodeKind::IndexAccess(base, index) => {
                let b = self.lower_expression(base);
                let i = self.lower_expression(index);
                vec![self.ast.push_node(NodeKind::IndexAccess(b, i), span)]
            }
            ParsedNodeKind::TernaryOp(cond, then_branch, else_branch) => {
                let c = self.lower_expression(cond);
                let t = self.lower_expression(then_branch);
                let e = self.lower_expression(else_branch);
                vec![self.ast.push_node(NodeKind::TernaryOp(c, t, e), span)]
            }
            ParsedNodeKind::GnuStatementExpression(stmt, expr) => {
                let s = self.lower_expression(stmt);
                let e = self.lower_expression(expr);
                vec![self.ast.push_node(NodeKind::GnuStatementExpression(s, e), span)]
            }
            ParsedNodeKind::SizeOfExpr(expr) => {
                let e = self.lower_expression(expr);
                vec![self.ast.push_node(NodeKind::SizeOfExpr(e), span)]
            }
            ParsedNodeKind::SizeOfType(ty_name) => {
                let ty = convert_to_qual_type(self, ty_name, span)
                    .unwrap_or(QualType::unqualified(self.registry.type_error));
                vec![self.ast.push_node(NodeKind::SizeOfType(ty), span)]
            }
            ParsedNodeKind::AlignOf(ty_name) => {
                let ty = convert_to_qual_type(self, ty_name, span)
                    .unwrap_or(QualType::unqualified(self.registry.type_error));
                vec![self.ast.push_node(NodeKind::AlignOf(ty), span)]
            }
            ParsedNodeKind::CompoundLiteral(ty_name, init) => {
                let ty = convert_to_qual_type(self, ty_name, span)
                    .unwrap_or(QualType::unqualified(self.registry.type_error));
                let i = self.lower_expression(init);
                vec![self.ast.push_node(NodeKind::CompoundLiteral(ty, i), span)]
            }
            ParsedNodeKind::GenericSelection(control, associations) => {
                let c = self.lower_expression(control);
                let assoc = associations
                    .iter()
                    .map(|a| {
                        let ty = a.type_name.map(|t| {
                            convert_to_qual_type(self, t, span)
                                .unwrap_or(QualType::unqualified(self.registry.type_error))
                        });
                        let expr = self.lower_expression(a.result_expr);
                        ResolvedGenericAssociation { ty, result_expr: expr }
                    })
                    .collect();
                vec![self.ast.push_node(NodeKind::GenericSelection(c, assoc), span)]
            }
            ParsedNodeKind::VaArg(va_list, type_ref) => {
                let v = self.lower_expression(va_list);
                vec![self.ast.push_node(NodeKind::VaArg(v, type_ref), span)]
            }
            ParsedNodeKind::InitializerList(inits) => {
                let lowered_inits = inits
                    .iter()
                    .map(|init| {
                        let expr = self.lower_expression(init.initializer);
                        let designation = init
                            .designation
                            .iter()
                            .map(|d| match d {
                                ParsedDesignator::FieldName(name) => crate::ast::nodes::Designator::FieldName(*name),
                                ParsedDesignator::ArrayIndex(idx) => {
                                    crate::ast::nodes::Designator::ArrayIndex(self.lower_expression(*idx))
                                }
                                ParsedDesignator::GnuArrayRange(start, end) => {
                                    crate::ast::nodes::Designator::GnuArrayRange(
                                        self.lower_expression(*start),
                                        self.lower_expression(*end),
                                    )
                                }
                            })
                            .collect();

                        crate::ast::nodes::DesignatedInitializer {
                            designation,
                            initializer: expr,
                        }
                    })
                    .collect();
                vec![self.ast.push_node(NodeKind::InitializerList(lowered_inits), span)]
            }
            ParsedNodeKind::EmptyStatement => {
                vec![]
            }
            _ => {
                // For unhandled nodes (or Dummy), push a Dummy node to avoid ICE
                vec![self.ast.push_node(NodeKind::Dummy, span)]
            }
        }
    }

    pub(crate) fn lower_expression(&mut self, node: ParsedNodeRef) -> NodeRef {
        match self.lower_node_recursive(node).first().cloned() {
            Some(n) => n,
            None => self.ast.push_node(NodeKind::Dummy, SourceSpan::default()),
        }
    }

    pub(crate) fn lower_single_statement(&mut self, node: ParsedNodeRef) -> NodeRef {
        self.lower_node_recursive(node)
            .first()
            .cloned()
            .unwrap_or_else(|| self.ast.push_node(NodeKind::Dummy, SourceSpan::default()))
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
                let _ = self
                    .symbol_table
                    .define_label(*name, self.registry.type_void, parsed_node.span);
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
            NodeKind::InitializerList(inits) => {
                let mut max_index: i64 = -1;
                let mut current_index: i64 = 0;

                if inits.is_empty() {
                    return Some(0);
                }

                for init in inits {
                    if let Some(first_designator) = init.designation.first() {
                        match first_designator {
                            crate::ast::Designator::ArrayIndex(expr_ref) => {
                                let const_ctx = ConstEvalCtx { ast: self.ast };
                                if let Some(val) = const_eval::eval_const_expr(&const_ctx, *expr_ref) {
                                    current_index = val;
                                } else {
                                    return None;
                                }
                            }
                            crate::ast::Designator::GnuArrayRange(start, end) => {
                                let const_ctx = ConstEvalCtx { ast: self.ast };
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
