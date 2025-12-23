//! Semantic lowering phase - transforms parser AST declarations into type-resolved semantic nodes.
//!
//! This module implements the semantic lowering phase that bridges the gap between the
//! grammar-oriented parser AST and the type-resolved semantic AST (HIR). The lowering
//! phase handles all C-style declaration forms while maintaining strict error reporting
//! and symbol table integration.

use crate::ast::*;
use crate::diagnostic::{DiagnosticEngine, SemanticError};
use crate::semantic::symbol_table::{ScopeId, SymbolTable};
use crate::source_manager::SourceSpan;
use log::debug;

/// Context for the semantic lowering phase
pub struct LowerCtx<'a, 'src> {
    pub ast: &'a mut Ast,
    pub diag: &'src mut DiagnosticEngine,
    pub symbol_table: &'a mut SymbolTable,
    pub current_scope: ScopeId,
    // Track errors during lowering for early termination
    pub has_errors: bool,
}

impl<'a, 'src> LowerCtx<'a, 'src> {
    /// Create a new lowering context
    pub fn new(
        ast: &'a mut Ast,
        diag: &'src mut DiagnosticEngine,
        symbol_table: &'a mut SymbolTable,
        current_scope: ScopeId,
    ) -> Self {
        Self {
            ast,
            diag,
            symbol_table,
            current_scope,
            has_errors: false,
        }
    }

    /// Report a semantic error and mark context as having errors
    pub fn report_error(&mut self, error: SemanticError) {
        self.has_errors = true;
        self.diag.report_error(error);
    }

    /// Check if the context has any errors
    pub fn has_errors(&self) -> bool {
        self.has_errors
    }
}

/// Information about declaration specifiers after processing
#[derive(Debug, Clone, Default)]
pub struct DeclSpecInfo {
    pub storage: Option<StorageClass>,
    pub qualifiers: TypeQualifiers,
    pub base_type: Option<TypeRef>,
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
                    ctx.report_error(SemanticError::InvalidOperands {
                        message: "Duplicate storage class specifier".to_string(),
                        location: span,
                    });
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
                    // Create an error type
                    let error_type = Type {
                        kind: TypeKind::Error,
                        qualifiers: TypeQualifiers::empty(),
                        size: None,
                        alignment: None,
                    };
                    ctx.ast.push_type(error_type)
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

/// Resolve a type specifier to a TypeRef
fn resolve_type_specifier(ts: &TypeSpecifier, ctx: &mut LowerCtx, span: SourceSpan) -> Result<TypeRef, SemanticError> {
    match ts {
        TypeSpecifier::Void => Ok(ctx.ast.push_type(Type::new(TypeKind::Void))),
        TypeSpecifier::Char => Ok(ctx.ast.push_type(Type::new(TypeKind::Char { is_signed: true }))),
        TypeSpecifier::Short => Ok(ctx.ast.push_type(Type::new(TypeKind::Short { is_signed: true }))),
        TypeSpecifier::Int => Ok(ctx.ast.push_type(Type::new(TypeKind::Int { is_signed: true }))),
        TypeSpecifier::Long => Ok(ctx.ast.push_type(Type::new(TypeKind::Long {
            is_signed: true,
            is_long_long: false,
        }))),
        TypeSpecifier::LongLong => Ok(ctx.ast.push_type(Type::new(TypeKind::Long {
            is_signed: true,
            is_long_long: true,
        }))),
        TypeSpecifier::Float => Ok(ctx.ast.push_type(Type::new(TypeKind::Float))),
        TypeSpecifier::Double => Ok(ctx.ast.push_type(Type::new(TypeKind::Double { is_long_double: false }))),
        TypeSpecifier::LongDouble => Ok(ctx.ast.push_type(Type::new(TypeKind::Double { is_long_double: true }))),
        TypeSpecifier::Signed => {
            // Signed modifier - for now, default to signed int
            Ok(ctx.ast.push_type(Type::new(TypeKind::Int { is_signed: true })))
        }
        TypeSpecifier::Unsigned => {
            // Unsigned modifier - for now, default to unsigned int
            Ok(ctx.ast.push_type(Type::new(TypeKind::Int { is_signed: false })))
        }
        TypeSpecifier::Bool => Ok(ctx.ast.push_type(Type::new(TypeKind::Bool))),
        TypeSpecifier::Complex => {
            // Complex types need a base type
            // For now, default to complex double
            let base_type = ctx.ast.push_type(Type::new(TypeKind::Double { is_long_double: false }));
            Ok(ctx.ast.push_type(Type::new(TypeKind::Complex { base_type })))
        }
        TypeSpecifier::Atomic(inner_type) => Ok(ctx
            .ast
            .push_type(Type::new(TypeKind::Atomic { base_type: *inner_type }))),
        TypeSpecifier::Record(is_union, tag, definition) => {
            // Properly handle struct/union types with their member declarations
            debug!("Processing record definition: {:?}", definition);

            // Check if we already have a struct type with this tag
            let existing_type_ref = tag.and_then(|tag_name| {
                // Search for existing struct/union type with the same tag
                for (i, existing_type) in ctx.ast.types.iter().enumerate() {
                    if let TypeKind::Record { tag: existing_tag, .. } = &existing_type.kind
                        && existing_tag == &Some(tag_name)
                    {
                        return Some(TypeRef::new((i + 1) as u32).unwrap());
                    }
                }
                None
            });

            // For self-referential structs, if we don't find an existing one but have a definition,
            // create a forward reference first
            let forward_ref = if existing_type_ref.is_none() && tag.is_some() && definition.is_some() {
                let forward_type = Type::new(TypeKind::Record {
                    tag: *tag,
                    members: Vec::new(),
                    is_complete: false,
                    is_union: *is_union,
                });
                Some(ctx.ast.push_type(forward_type))
            } else {
                None
            };

            // Use the forward reference if we created one, otherwise use the existing reference
            let type_ref_to_update = existing_type_ref.or(forward_ref);

            if let Some(existing_ref) = type_ref_to_update {
                // For self-referential structs, check if we need to update with members
                let existing_type = ctx.ast.get_type(existing_ref);
                if let TypeKind::Record {
                    is_complete: existing_complete,
                    ..
                } = &existing_type.kind
                    && !existing_complete
                    && definition.is_some()
                {
                    debug!("Updating incomplete struct type with tag {:?} with members", tag);
                    // Create new type with members
                    let members = definition
                            .as_ref()
                            .and_then(|def| def.members.as_ref())
                            .map(|decls| {
                                debug!("Found {} member declarations", decls.len());
                                // Convert each struct member declaration to StructMember
                                let mut struct_members = Vec::new();
                                for (i, decl) in decls.iter().enumerate() {
                                    debug!("Processing member declaration {}: {:?}", i, decl);

                                    // Check if this is an anonymous struct/union declaration (no init_declarators)
                                    if decl.init_declarators.is_empty() {
                                        debug!("Found declaration with no init_declarators, checking for anonymous struct/union");
                                        if let Some((is_union, _, definition)) = decl.specifiers.iter().find_map(|spec| {
                                                if let DeclSpecifier::TypeSpecifier(TypeSpecifier::Record(is_union, tag, definition)) = spec {
                                                    Some((is_union, tag, definition))
                                                } else {
                                                    None
                                                }
                                            }) {
                                            debug!("Processing anonymous {} with definition", if *is_union { "union" } else { "struct" });
                                            // Recursively process the anonymous struct/union members
                                            if let Some(def) = definition
                                                && let Some(member_decls) = &def.members {
                                                    let anonymous_members = process_anonymous_struct_members(
                                                        member_decls, *is_union, ctx, span
                                                    );
                                                    struct_members.extend(anonymous_members);
                                                }
                                            continue; // Skip the normal processing for anonymous structs
                                        }
                                    }

                                    // Process each declarator in the member declaration
                                    for (j, init_declarator) in decl.init_declarators.iter().enumerate() {
                                        debug!("Processing declarator {}: {:?}", j, init_declarator);
                                        // Extract the member name and type
                                        if let Some(member_name) = extract_identifier(&init_declarator.declarator) {
                                            debug!("Found member name: {}", member_name);
                                            // Get the member type from declaration specifiers
                                            let member_type = if let Some(base_type_ref) =
                                                lower_decl_specifiers_for_member(&decl.specifiers, ctx, span)
                                            {
                                                // Apply the declarator to get the final member type
                                                let member_type_with_declarator =
                                                    apply_declarator_for_member(base_type_ref, &init_declarator.declarator, ctx);
                                                ctx.ast.push_type(member_type_with_declarator)
                                            } else {
                                                debug!("Failed to get base type, defaulting to int");
                                                // Default to int if type resolution fails
                                                ctx.ast.push_type(Type::new(TypeKind::Int { is_signed: true }))
                                            };

                                            struct_members.push(StructMember {
                                                name: member_name,
                                                member_type,
                                                bit_field_size: None,
                                                location: span,
                                            });
                                        } else {
                                            debug!("Failed to extract member name from declarator");
                                        }
                                    }
                                }
                                debug!("Created {} struct members", struct_members.len());
                                struct_members
                            })
                            .unwrap_or_default();

                    // Replace the existing type with the complete version
                    let complete_type = Type::new(TypeKind::Record {
                        tag: *tag,
                        members,
                        is_complete: true,
                        is_union: *is_union,
                    });

                    // Update the type in the AST
                    let type_index = (existing_ref.get() - 1) as usize;
                    debug!(
                        "Replacing incomplete struct type {} with complete version",
                        existing_ref.get()
                    );
                    ctx.ast.types[type_index] = complete_type;

                    // Update all pointer types that reference this struct to point to the complete version
                    debug!(
                        "Updating all pointer types that reference struct {}",
                        existing_ref.get()
                    );
                    for (i, ast_type) in ctx.ast.types.iter_mut().enumerate() {
                        if let TypeKind::Pointer { pointee } = &mut ast_type.kind
                            && pointee.get() == existing_ref.get()
                        {
                            debug!("Updating pointer type at index {} to point to complete struct", i + 1);
                            *pointee = existing_ref;
                        }
                    }
                }

                // Always return the existing struct reference
                debug!(
                    "Returning existing struct reference {} for tag {:?}",
                    existing_ref.get(),
                    tag
                );
                return Ok(existing_ref);
            } else {
                debug!("No existing type reference to update");
            }

            let members = definition
                .as_ref()
                .and_then(|def| def.members.as_ref())
                .map(|decls| {
                    debug!("Found {} member declarations", decls.len());
                    // Convert each struct member declaration to StructMember
                    let mut struct_members = Vec::new();
                    for (i, decl) in decls.iter().enumerate() {
                        debug!("Processing member declaration {}: {:?}", i, decl);

                        // Check if this is an anonymous struct/union declaration (no init_declarators)
                        if decl.init_declarators.is_empty() {
                            debug!("Found declaration with no init_declarators, checking for anonymous struct/union");
                            if let Some((is_union, _, definition)) = decl.specifiers.iter().find_map(|spec| {
                                if let DeclSpecifier::TypeSpecifier(TypeSpecifier::Record(is_union, tag, definition)) =
                                    spec
                                {
                                    Some((is_union, tag, definition))
                                } else {
                                    None
                                }
                            }) {
                                debug!(
                                    "Processing anonymous {} with definition",
                                    if *is_union { "union" } else { "struct" }
                                );
                                // Recursively process the anonymous struct/union members
                                if let Some(def) = definition
                                    && let Some(member_decls) = &def.members
                                {
                                    let anonymous_members =
                                        process_anonymous_struct_members(member_decls, *is_union, ctx, span);
                                    struct_members.extend(anonymous_members);
                                }
                                continue; // Skip the normal processing for anonymous structs
                            }
                        }

                        // Process each declarator in the member declaration
                        for (j, init_declarator) in decl.init_declarators.iter().enumerate() {
                            debug!("Processing declarator {}: {:?}", j, init_declarator);
                            // Extract the member name and type
                            if let Some(member_name) = extract_identifier(&init_declarator.declarator) {
                                debug!("Found member name: {}", member_name);
                                // Get the member type from declaration specifiers
                                let member_type = if let Some(base_type_ref) =
                                    lower_decl_specifiers_for_member(&decl.specifiers, ctx, span)
                                {
                                    // Apply the declarator to get the final member type
                                    let member_type_with_declarator =
                                        apply_declarator_for_member(base_type_ref, &init_declarator.declarator, ctx);
                                    ctx.ast.push_type(member_type_with_declarator)
                                } else {
                                    debug!("Failed to get base type, defaulting to int");
                                    // Default to int if type resolution fails
                                    ctx.ast.push_type(Type::new(TypeKind::Int { is_signed: true }))
                                };

                                struct_members.push(StructMember {
                                    name: member_name,
                                    member_type,
                                    bit_field_size: None,
                                    location: span,
                                });
                            } else {
                                debug!("Failed to extract member name from declarator");
                            }
                        }
                    }
                    debug!("Created {} struct members", struct_members.len());
                    struct_members
                })
                .unwrap_or_default();

            let final_type_ref = ctx.ast.push_type(Type::new(TypeKind::Record {
                tag: *tag,
                members,
                is_complete: definition.is_some(),
                is_union: *is_union,
            }));
            debug!(
                "Created new struct type with tag {:?}, is_complete: {}, type_ref: {}",
                tag,
                definition.is_some(),
                final_type_ref.get()
            );
            Ok(final_type_ref)
        }
        TypeSpecifier::Enum(tag, enumerators) => {
            // TODO: Handle enum types properly
            // For now, create a basic enum type
            let enumerators_list = enumerators
                .as_ref()
                .map(|enums| {
                    enums
                        .iter()
                        .map(|&enum_ref| {
                            let enum_node = ctx.ast.get_node(enum_ref);
                            if let NodeKind::EnumConstant(name, value) = &enum_node.kind {
                                EnumConstant {
                                    name: *name,
                                    value: value
                                        .as_ref()
                                        .map(|v| {
                                            let val_node = ctx.ast.get_node(*v);
                                            if let NodeKind::LiteralInt(val) = val_node.kind {
                                                val
                                            } else {
                                                0
                                            }
                                        })
                                        .unwrap_or(0),
                                    location: enum_node.span,
                                }
                            } else {
                                EnumConstant {
                                    name: Symbol::new(""),
                                    value: 0,
                                    location: enum_node.span,
                                }
                            }
                        })
                        .collect()
                })
                .unwrap_or_default();

            let base_type = ctx.ast.push_type(Type::new(TypeKind::Int { is_signed: true }));
            Ok(ctx.ast.push_type(Type::new(TypeKind::Enum {
                tag: *tag,
                base_type,
                enumerators: enumerators_list,
                is_complete: enumerators.is_some(),
            })))
        }
        TypeSpecifier::TypedefName(name) => {
            // Lookup typedef in symbol table
            debug!("Resolving typedef name: {}", name);
            if let Some((entry_ref, scope_id)) = ctx.symbol_table.lookup_symbol(*name) {
                let entry = ctx.symbol_table.get_symbol_entry(entry_ref);
                debug!(
                    "Found typedef '{}' in scope {} with aliased type {:?}",
                    name,
                    scope_id.get(),
                    entry.type_info
                );
                if let SymbolKind::Typedef { aliased_type } = entry.kind {
                    Ok(aliased_type)
                } else {
                    debug!("Symbol '{}' is not a typedef", name);
                    Err(SemanticError::IncompleteType {
                        name: *name,
                        location: span,
                    })
                }
            } else {
                debug!(
                    "Typedef '{}' not found during semantic lowering - creating forward reference",
                    name
                );
                // List all symbols in current scope for debugging
                let current_scope = ctx.symbol_table.get_scope(ctx.current_scope);
                debug!(
                    "Current scope symbols: {:?}",
                    current_scope.symbols.keys().collect::<Vec<_>>()
                );
                // Typedef not found during semantic lowering - this is expected
                // when typedefs are defined later in the same scope.
                // Create a forward reference that will be resolved during semantic analysis.
                // For now, create a placeholder record type with the expected structure.
                // This is a temporary solution - in a full implementation, we'd have a proper
                // forward reference mechanism.
                let forward_ref_type = Type {
                    kind: TypeKind::Record {
                        tag: Some(*name),    // Use typedef name as tag for lookup
                        members: Vec::new(), // Unknown at this point
                        is_complete: false,  // Mark as incomplete
                        is_union: false,
                    },
                    qualifiers: TypeQualifiers::empty(),
                    size: None,
                    alignment: None,
                };
                Ok(ctx.ast.push_type(forward_ref_type))
            }
        }
    }
}

/// Merge base types according to C type combination rules
fn merge_base_type(existing: Option<TypeRef>, new_type: TypeRef, ctx: &mut LowerCtx) -> Option<TypeRef> {
    match existing {
        None => Some(new_type),
        Some(existing_ref) => {
            let existing_type = ctx.ast.get_type(existing_ref);
            let new_type_info = ctx.ast.get_type(new_type);

            // Handle signed/unsigned merging
            match (&existing_type.kind, &new_type_info.kind) {
                // Unsigned overrides signed for same base type
                (TypeKind::Int { is_signed: true }, TypeKind::Int { is_signed: false }) => Some(new_type),
                (TypeKind::Int { is_signed: false }, TypeKind::Int { is_signed: true }) => {
                    Some(existing_ref) // Keep unsigned
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
        ctx.report_error(SemanticError::InvalidOperands {
            message: "Illegal storage class with typedef".to_string(),
            location: span,
        });
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
                ty: record_type,
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
                ty: enum_type,
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
    debug!(
        "Processing init-declarator for name {:?}",
        extract_identifier(&init.declarator)
    );
    debug!("Base type from spec: {:?}", spec.base_type);
    debug!("Is typedef: {}", spec.is_typedef);

    // 1. Resolve final type (base + declarator)
    let base_ty = spec.base_type.unwrap_or_else(|| {
        ctx.report_error(SemanticError::InvalidOperands {
            message: "Missing base type in declaration".to_string(),
            location: span,
        });
        // Create an error type
        let error_type = Type {
            kind: TypeKind::Error,
            qualifiers: TypeQualifiers::empty(),
            size: None,
            alignment: None,
        };
        ctx.ast.push_type(error_type)
    });

    let name = extract_identifier(&init.declarator).expect("Anonymous declarations unsupported");

    // For simple identifiers without qualifiers, don't create a new type entry
    let final_ty = if let Declarator::Identifier(_, qualifiers, None) = &init.declarator {
        if qualifiers.is_empty() {
            // Simple case: just use the base type directly
            debug!("Using base type directly for simple identifier '{}'", name);
            base_ty
        } else {
            // Has qualifiers, need to apply declarator
            let ty = apply_declarator(base_ty, &init.declarator, ctx);
            ctx.ast.push_type(ty)
        }
    } else {
        // Complex case: apply declarator transformations and create new type
        let ty = apply_declarator(base_ty, &init.declarator, ctx);
        ctx.ast.push_type(ty)
    };

    debug!("Final type for '{}': {:?}", name, final_ty);

    // 2. Handle typedefs
    if spec.is_typedef {
        debug!("Creating typedef for name '{}' with type {:?}", name, final_ty);
        let typedef_decl = TypedefDeclData { name, ty: final_ty };
        let typedef_node = ctx.ast.push_node(Node::new(NodeKind::TypedefDecl(typedef_decl), span));

        // Add typedef to symbol table to resolve forward references
        let symbol_entry = crate::ast::SymbolEntry {
            name: name.as_str().into(),
            kind: crate::ast::SymbolKind::Typedef { aliased_type: final_ty },
            type_info: final_ty,
            storage_class: Some(StorageClass::Typedef),
            scope_id: ctx.current_scope.get(),
            definition_span: span,
            is_defined: true,
            is_referenced: false,
            is_completed: true,
        };

        let entry_ref = ctx.symbol_table.add_symbol(name, symbol_entry);
        debug!(
            "Added typedef '{}' to symbol table with entry ref {:?}",
            name, entry_ref
        );

        return typedef_node;
    }

    // 3. Distinguish between functions and variables
    let type_info = ctx.ast.get_type(final_ty);
    if matches!(type_info.kind, TypeKind::Function { .. }) {
        let func_decl = FunctionDeclData {
            name,
            ty: final_ty,
            storage: spec.storage,
            body: None,
        };
        ctx.ast.push_node(Node::new(NodeKind::FunctionDecl(func_decl), span))
    } else {
        let var_decl = VarDeclData {
            name,
            ty: final_ty,
            storage: spec.storage,
            init: init.initializer,
        };
        ctx.ast.push_node(Node::new(NodeKind::VarDecl(var_decl), span))
    }
}

/// Apply declarator transformations to a base type
fn apply_declarator(base_type: TypeRef, declarator: &Declarator, ctx: &mut LowerCtx) -> Type {
    match declarator {
        Declarator::Pointer(qualifiers, next) => {
            let pointee_type = if let Some(next_decl) = next {
                apply_declarator(base_type, next_decl, ctx)
            } else {
                ctx.ast.get_type(base_type).clone()
            };

            let pointee_type_ref = ctx.ast.push_type(pointee_type);
            let mut pointer_type = Type::new(TypeKind::Pointer {
                pointee: pointee_type_ref,
            });
            pointer_type.qualifiers = *qualifiers;
            pointer_type
        }
        Declarator::Identifier(_, qualifiers, _) => {
            debug!(
                "apply_declarator: Identifier with base_type {:?}, qualifiers {:?}",
                base_type, qualifiers
            );
            let mut ty = ctx.ast.get_type(base_type).clone();
            ty.qualifiers |= *qualifiers;
            ty
        }
        Declarator::Array(base, size) => {
            let element_type = apply_declarator(base_type, base, ctx);
            let array_size = match size {
                ArraySize::Expression { expr: _, qualifiers: _ } => {
                    // TODO: Evaluate expression for constant size
                    ArraySizeType::Incomplete
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

            Type::new(TypeKind::Array {
                element_type: ctx.ast.push_type(element_type),
                size: array_size,
            })
        }
        Declarator::Function(base, params) => {
            let return_type = apply_declarator(base_type, base, ctx);

            // Convert parameters to function parameter types
            let parameters = params
                .iter()
                .map(|param| {
                    let param_type = if let Some(param_decl) = &param.declarator {
                        // Create a temporary base type for parameters
                        let temp_base = ctx.ast.push_type(Type::new(TypeKind::Int { is_signed: true }));
                        let param_ty = apply_declarator(temp_base, param_decl, ctx);
                        ctx.ast.push_type(param_ty)
                    } else {
                        // Abstract declarator - use base type
                        base_type
                    };

                    FunctionParameter {
                        param_type,
                        name: extract_identifier(param.declarator.as_ref().unwrap_or(&Declarator::Abstract)),
                    }
                })
                .collect();

            Type::new(TypeKind::Function {
                return_type: ctx.ast.push_type(return_type),
                parameters,
                is_variadic: false, // TODO: Detect variadic
            })
        }
        Declarator::AnonymousRecord(_, _) => {
            // TODO: Handle anonymous struct/union
            ctx.ast.get_type(base_type).clone()
        }
        Declarator::BitField(base, _) => {
            // TODO: Handle bit fields
            apply_declarator(base_type, base, ctx)
        }
        Declarator::Abstract => ctx.ast.get_type(base_type).clone(),
    }
}

/// Main entry point for running semantic lowering on an entire AST
pub fn run_semantic_lowering(ast: &mut Ast, diag: &mut DiagnosticEngine, symbol_table: &mut SymbolTable) {
    debug!("Starting semantic lowering phase");

    // Check if we have a root node to start traversal from
    let Some(_root_node) = ast.get_root_node() else {
        debug!("No root node found, skipping semantic lowering");
        return;
    };

    let root_node_ref = ast.root.unwrap();
    debug!("Starting semantic lowering from root node: {}", root_node_ref.get());

    // First, collect all declaration nodes without borrowing ast mutably
    let nodes_to_process = {
        let ast_ref = ast as *const Ast;
        let ast_immutable = unsafe { &*ast_ref };
        collect_declaration_nodes(ast_immutable, root_node_ref)
    };

    // Create lowering context
    let mut lower_ctx = LowerCtx::new(ast, diag, symbol_table, ScopeId::GLOBAL);

    // Process all declaration nodes in the AST
    for node_ref in nodes_to_process {
        let semantic_nodes = lower_declaration(&mut lower_ctx, node_ref);

        if !semantic_nodes.is_empty() {
            if semantic_nodes.len() == 1 {
                // Single declarator case: replace the original declaration node with the semantic node
                let semantic_node_data = lower_ctx.ast.get_node(semantic_nodes[0]);
                let semantic_node_clone = semantic_node_data.clone();
                lower_ctx.ast.replace_node(node_ref, semantic_node_clone);
            } else {
                // Multi-declarator case: create a CompoundStatement containing all semantic nodes
                let original_node = lower_ctx.ast.get_node(node_ref);
                let compound_node = Node::new(
                    NodeKind::CompoundStatement(semantic_nodes.clone()),
                    original_node.span, // Use actual span from original declaration
                );

                lower_ctx.ast.replace_node(node_ref, compound_node);
            }
        }
    }

    debug!("Semantic lowering complete");
}

/// Collect all declaration nodes from the AST
fn collect_declaration_nodes(ast: &Ast, root_node_ref: NodeRef) -> Vec<NodeRef> {
    let mut declarations = Vec::new();
    let mut stack = vec![root_node_ref];

    while let Some(node_ref) = stack.pop() {
        let node = ast.get_node(node_ref);

        match &node.kind {
            NodeKind::Declaration(_) => {
                declarations.push(node_ref);
            }
            NodeKind::FunctionDef(func_def) => {
                stack.push(func_def.body);
            }
            NodeKind::CompoundStatement(nodes) => {
                stack.extend(nodes.iter().rev());
            }
            NodeKind::For(for_stmt) => {
                if let Some(init_node_ref) = for_stmt.init {
                    let init_node = ast.get_node(init_node_ref);
                    if let NodeKind::Declaration(_) = &init_node.kind {
                        declarations.push(init_node_ref);
                    }
                }
                if let Some(condition) = for_stmt.condition {
                    stack.push(condition);
                }
                if let Some(increment) = for_stmt.increment {
                    stack.push(increment);
                }
                stack.push(for_stmt.body);
            }
            NodeKind::If(if_stmt) => {
                stack.push(if_stmt.condition);
                stack.push(if_stmt.then_branch);
                if let Some(else_branch) = if_stmt.else_branch {
                    stack.push(else_branch);
                }
            }
            NodeKind::While(while_stmt) => {
                stack.push(while_stmt.condition);
                stack.push(while_stmt.body);
            }
            NodeKind::DoWhile(body, condition) => {
                stack.push(*body);
                stack.push(*condition);
            }
            NodeKind::Switch(condition, body) => {
                stack.push(*condition);
                stack.push(*body);
            }
            NodeKind::Case(expr, stmt) => {
                stack.push(*expr);
                stack.push(*stmt);
            }
            NodeKind::CaseRange(start_expr, end_expr, stmt) => {
                stack.push(*start_expr);
                stack.push(*end_expr);
                stack.push(*stmt);
            }
            NodeKind::Default(stmt) => {
                stack.push(*stmt);
            }
            NodeKind::Label(_, stmt) => {
                stack.push(*stmt);
            }
            NodeKind::BinaryOp(_, left, right) => {
                stack.push(*left);
                stack.push(*right);
            }
            NodeKind::Assignment(_, lhs, rhs) => {
                stack.push(*lhs);
                stack.push(*rhs);
            }
            NodeKind::FunctionCall(func, args) => {
                stack.push(*func);
                for arg in args {
                    stack.push(*arg);
                }
            }
            NodeKind::Return(Some(expr_ref)) => {
                stack.push(*expr_ref);
            }
            NodeKind::UnaryOp(_, expr) => {
                stack.push(*expr);
            }
            NodeKind::Cast(_, expr) => {
                stack.push(*expr);
            }
            NodeKind::SizeOfExpr(expr) => {
                stack.push(*expr);
            }
            NodeKind::TernaryOp(cond, then_expr, else_expr) => {
                stack.push(*cond);
                stack.push(*then_expr);
                stack.push(*else_expr);
            }
            NodeKind::MemberAccess(obj, _, _) => {
                stack.push(*obj);
            }
            NodeKind::IndexAccess(array, index) => {
                stack.push(*array);
                stack.push(*index);
            }
            NodeKind::TranslationUnit(nodes) => {
                stack.extend(nodes.iter().rev());
            }
            NodeKind::ExpressionStatement(Some(expr_ref)) => {
                stack.push(*expr_ref);
            }
            _ => {
                // For other node types, we don't traverse further
            }
        }
    }

    declarations
}

/// Lower declaration specifiers for struct members (simplified version)
fn lower_decl_specifiers_for_member(specs: &[DeclSpecifier], ctx: &mut LowerCtx, span: SourceSpan) -> Option<TypeRef> {
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
fn apply_declarator_for_member(base_type: TypeRef, declarator: &Declarator, ctx: &mut LowerCtx) -> Type {
    match declarator {
        Declarator::Identifier(_, qualifiers, _) => {
            let mut ty = ctx.ast.get_type(base_type).clone();
            ty.qualifiers |= *qualifiers;
            ty
        }
        Declarator::Pointer(qualifiers, next) => {
            let pointee_type = if let Some(next_decl) = next {
                apply_declarator_for_member(base_type, next_decl, ctx)
            } else {
                ctx.ast.get_type(base_type).clone()
            };

            let mut pointer_type = Type::new(TypeKind::Pointer {
                pointee: ctx.ast.push_type(pointee_type),
            });
            pointer_type.qualifiers = *qualifiers;
            pointer_type
        }
        Declarator::Array(base, size) => {
            let element_type = apply_declarator_for_member(base_type, base, ctx);
            let array_size = match size {
                ArraySize::Expression { expr: _, qualifiers: _ } => {
                    // TODO: Evaluate expression for constant size
                    ArraySizeType::Incomplete
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

            Type::new(TypeKind::Array {
                element_type: ctx.ast.push_type(element_type),
                size: array_size,
            })
        }
        // For other declarator types, just return the base type
        _ => ctx.ast.get_type(base_type).clone(),
    }
}

/// Process anonymous struct/union members by flattening them into the containing struct
fn process_anonymous_struct_members(
    member_decls: &[DeclarationData],
    is_union: bool,
    ctx: &mut LowerCtx,
    span: SourceSpan,
) -> Vec<StructMember> {
    let mut flattened_members = Vec::new();

    debug!(
        "Processing anonymous {} with {} member declarations",
        if is_union { "union" } else { "struct" },
        member_decls.len()
    );

    for (i, decl) in member_decls.iter().enumerate() {
        debug!("Processing anonymous member declaration {}: {:?}", i, decl);

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
            }) {
                debug!("Found nested anonymous struct/union, recursing");
                if let Some(nested_decls) = &definition.members {
                    let nested_members = process_anonymous_struct_members(nested_decls, *nested_is_union, ctx, span);
                    flattened_members.extend(nested_members);
                }
            }
        } else {
            // This is a regular member - process it normally
            for init_declarator in &decl.init_declarators {
                if let Some(member_name) = extract_identifier(&init_declarator.declarator) {
                    debug!("Found anonymous member name: {}", member_name);

                    // Get the member type from declaration specifiers
                    let member_type =
                        if let Some(base_type_ref) = lower_decl_specifiers_for_member(&decl.specifiers, ctx, span) {
                            // Apply the declarator to get the final member type
                            let member_type_with_declarator =
                                apply_declarator_for_member(base_type_ref, &init_declarator.declarator, ctx);
                            ctx.ast.push_type(member_type_with_declarator)
                        } else {
                            debug!("Failed to get base type for anonymous member, defaulting to int");
                            ctx.ast.push_type(Type::new(TypeKind::Int { is_signed: true }))
                        };

                    flattened_members.push(StructMember {
                        name: member_name,
                        member_type,
                        bit_field_size: None,
                        location: span,
                    });
                } else {
                    debug!("Failed to extract member name from anonymous struct member");
                }
            }
        }
    }

    debug!("Flattened {} anonymous members", flattened_members.len());
    flattened_members
}
