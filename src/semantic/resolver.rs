//! Semantic lowering phase - transforms parser AST declarations into type-resolved semantic nodes.
//!
//! This module implements the semantic lowering phase that bridges the gap between the
//! grammar-oriented parser AST and the type-resolved semantic AST (HIR). The lowering
//! phase handles all C-style declaration forms while maintaining strict error reporting
//! and symbol table integration.

use crate::ast::*;
use crate::diagnostic::{DiagnosticEngine, SemanticError};
use crate::semantic::symbol_table::DefinitionState;
use crate::semantic::{Namespace, ScopeId, SymbolEntry, SymbolKind, SymbolTable};
use crate::source_manager::SourceSpan;

/// Context for the semantic lowering phase
pub struct LowerCtx<'a, 'src> {
    pub ast: &'a mut Ast,
    pub diag: &'src mut DiagnosticEngine,
    pub symbol_table: &'a mut SymbolTable,
    // Track errors during lowering for early termination
    pub has_errors: bool,
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
    pub fn new(ast: &'a mut Ast, diag: &'src mut DiagnosticEngine, symbol_table: &'a mut SymbolTable) -> Self {
        Self {
            ast,
            diag,
            symbol_table,
            has_errors: false,
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
                    ctx.report_error(SemanticError::TypeMismatch {
                        expected: "at most one storage class".to_string(),
                        found: "multiple storage classes".to_string(),
                        span,
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
            // Unsigned modifier - return a special marker type that will be handled in merge_base_type
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

            let existing_entry = tag.and_then(|tag_name| ctx.symbol_table.lookup_tag(tag_name));

            let type_ref_to_use = if let Some(tag_name) = tag {
                // Named struct/union
                if let Some(_def) = definition {
                    // This is a DEFINITION: struct T { ... }
                    let in_current_scope =
                        existing_entry.is_some_and(|(_, scope_id)| scope_id == ctx.symbol_table.current_scope());

                    if in_current_scope {
                        let (entry_ref, _) = existing_entry.unwrap();
                        let entry = ctx.symbol_table.get_symbol_entry(entry_ref);

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
                        let new_type = Type::new(TypeKind::Record {
                            tag: Some(*tag_name),
                            members: Vec::new(),
                            is_complete: false,
                            is_union: *is_union,
                        });
                        let new_type_ref = ctx.ast.push_type(new_type);

                        // Add it to the symbol table in the current scope
                        let symbol_entry = SymbolEntry {
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
                        let entry = ctx.symbol_table.get_symbol_entry(entry_ref);
                        entry.type_info
                    } else {
                        // Not found anywhere, create an implicit forward declaration in current scope
                        let forward_type = Type::new(TypeKind::Record {
                            tag: Some(*tag_name),
                            members: Vec::new(),
                            is_complete: false,
                            is_union: *is_union,
                        });
                        let forward_ref = ctx.ast.push_type(forward_type);

                        let symbol_entry = SymbolEntry {
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
                let new_type = Type::new(TypeKind::Record {
                    tag: None,
                    members: Vec::new(),
                    is_complete: false,
                    is_union: *is_union,
                });
                ctx.ast.push_type(new_type)
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
                                            base_type_ref,
                                            &init_declarator.declarator,
                                            ctx,
                                        );
                                        ctx.ast.push_type(ty)
                                    } else {
                                        ctx.ast.push_type(Type::new(TypeKind::Int { is_signed: true }))
                                    };

                                    struct_members.push(StructMember {
                                        name: member_name,
                                        member_type,
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
                let type_idx = (type_ref_to_use.get() - 1) as usize;
                let completed_type = Type::new(TypeKind::Record {
                    tag: *tag,
                    members: members.clone(),
                    is_complete: true,
                    is_union: *is_union,
                });
                ctx.ast.types[type_idx] = completed_type;

                if let Some(tag_name) = tag
                    && let Some((entry_ref, _)) = ctx.symbol_table.lookup_tag(*tag_name)
                {
                    let entry = ctx.symbol_table.get_symbol_entry_mut(entry_ref);
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

            Ok(type_ref_to_use)
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
                            let entry = ctx.symbol_table.get_symbol_entry(entry_ref);
                            (entry.is_completed, entry.def_span, entry.type_info)
                        };
                        if is_completed {
                            ctx.report_error(SemanticError::Redefinition {
                                name: *tag_name,
                                first_def,
                                second_def: span,
                            });
                        }
                        type_info
                    } else {
                        // Not found in current scope, create new entry
                        let new_type = Type::new(TypeKind::Enum {
                            tag: Some(*tag_name),
                            base_type: ctx.ast.push_type(Type::new(TypeKind::Int { is_signed: true })),
                            enumerators: Vec::new(),
                            is_complete: false,
                        });
                        let new_type_ref = ctx.ast.push_type(new_type);
                        let symbol_entry = SymbolEntry {
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
                        let entry = ctx.symbol_table.get_symbol_entry(entry_ref);
                        entry.type_info
                    } else {
                        // Implicit forward declaration
                        let forward_type = Type::new(TypeKind::Enum {
                            tag: Some(*tag_name),
                            base_type: ctx.ast.push_type(Type::new(TypeKind::Int { is_signed: true })),
                            enumerators: Vec::new(),
                            is_complete: false,
                        });
                        let forward_ref = ctx.ast.push_type(forward_type);
                        let symbol_entry = SymbolEntry {
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
                            .add_symbol_in_namespace(*tag_name, symbol_entry, Namespace::Tag);
                        forward_ref
                    }
                }
            } else {
                // Anonymous enum definition
                let new_type = Type::new(TypeKind::Enum {
                    tag: None,
                    base_type: ctx.ast.push_type(Type::new(TypeKind::Int { is_signed: true })),
                    enumerators: Vec::new(),
                    is_complete: false,
                });
                ctx.ast.push_type(new_type)
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
                        let entry = SymbolEntry {
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
                let mut updated_type_kind = ctx.ast.types[type_idx].kind.clone();
                if let TypeKind::Enum {
                    enumerators,
                    is_complete,
                    ..
                } = &mut updated_type_kind
                {
                    *enumerators = enumerators_list;
                    *is_complete = true;
                }
                ctx.ast.types[type_idx].kind = updated_type_kind;

                if let Some(tag_name) = tag
                    && let Some((entry_ref, _)) = ctx.symbol_table.lookup_tag(*tag_name)
                {
                    let entry = ctx.symbol_table.get_symbol_entry_mut(entry_ref);
                    entry.is_completed = true;
                    if let SymbolKind::EnumTag { is_complete } = &mut entry.kind {
                        *is_complete = true;
                    }
                }
            }

            Ok(type_ref_to_use)
        }
        TypeSpecifier::TypedefName(name) => {
            // Lookup typedef in symbol table
            if let Some((entry_ref, _scope_id)) = ctx.symbol_table.lookup_symbol(*name) {
                let entry = ctx.symbol_table.get_symbol_entry(entry_ref);
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

                // Handle char type merging
                (TypeKind::Char { is_signed: true }, TypeKind::Int { is_signed: false }) => {
                    // unsigned char = char + unsigned
                    Some(ctx.ast.push_type(Type::new(TypeKind::Char { is_signed: false })))
                }
                (TypeKind::Char { is_signed: false }, TypeKind::Int { is_signed: true }) => {
                    Some(existing_ref) // Keep unsigned char
                }

                // Handle short type merging
                (TypeKind::Short { is_signed: true }, TypeKind::Int { is_signed: false }) => {
                    // unsigned short = short + unsigned
                    Some(ctx.ast.push_type(Type::new(TypeKind::Short { is_signed: false })))
                }
                (TypeKind::Short { is_signed: false }, TypeKind::Int { is_signed: true }) => {
                    Some(existing_ref) // Keep unsigned short
                }

                // Handle unsigned + char/short order
                (TypeKind::Int { is_signed: false }, TypeKind::Char { is_signed: true }) => {
                    // unsigned char = unsigned + char
                    Some(ctx.ast.push_type(Type::new(TypeKind::Char { is_signed: false })))
                }
                (TypeKind::Int { is_signed: false }, TypeKind::Short { is_signed: true }) => {
                    // unsigned short = unsigned + short
                    Some(ctx.ast.push_type(Type::new(TypeKind::Short { is_signed: false })))
                }

                // Handle unsigned + long/long long order
                (
                    TypeKind::Int { is_signed: false },
                    TypeKind::Long {
                        is_long_long: false, ..
                    },
                ) => {
                    // unsigned long = unsigned + long
                    Some(ctx.ast.push_type(Type::new(TypeKind::Long {
                        is_signed: false,
                        is_long_long: false,
                    })))
                }
                (TypeKind::Int { is_signed: false }, TypeKind::Long { is_long_long: true, .. }) => {
                    // unsigned long long = unsigned + long long
                    Some(ctx.ast.push_type(Type::new(TypeKind::Long {
                        is_signed: false,
                        is_long_long: true,
                    })))
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
        ctx.report_error(SemanticError::TypeMismatch {
            expected: "at most one storage class".to_string(),
            found: "a mix of typedef and other storage classes".to_string(),
            span,
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
    // 1. Resolve final type (base + declarator)
    let base_ty = spec.base_type.unwrap_or_else(|| {
        ctx.report_error(SemanticError::TypeMismatch {
            expected: "a type specifier".to_string(),
            found: "no type specifier".to_string(),
            span,
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

    // 2. Handle typedefs
    if spec.is_typedef {
        let typedef_decl = TypedefDeclData { name, ty: final_ty };
        let typedef_node = ctx.ast.push_node(Node::new(NodeKind::TypedefDecl(typedef_decl), span));

        // Add typedef to symbol table to resolve forward references
        let symbol_entry = SymbolEntry {
            name: name.as_str().into(),
            kind: SymbolKind::Typedef { aliased_type: final_ty },
            type_info: final_ty,
            storage_class: Some(StorageClass::Typedef),
            scope_id: ctx.symbol_table.current_scope(),
            def_span: span,
            def_state: DefinitionState::Defined,
            is_referenced: false,
            is_completed: true,
        };

        let _entry_ref = ctx.symbol_table.add_symbol(name, symbol_entry);

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

fn lower_function_parameters(params: &[ParamData], ctx: &mut LowerCtx) -> Vec<FunctionParameter> {
    params
        .iter()
        .map(|param| {
            let span = SourceSpan::empty(); // FIXME: Get a proper span for parameter declarations
            let spec_info = lower_decl_specifiers(&param.specifiers, ctx, span);

            // C standard: if type specifier is missing in a parameter, it defaults to int.
            let base_ty = spec_info
                .base_type
                .unwrap_or_else(|| ctx.ast.push_type(Type::new(TypeKind::Int { is_signed: true })));

            let final_ty = if let Some(declarator) = &param.declarator {
                let ty = apply_declarator(base_ty, declarator, ctx);
                ctx.ast.push_type(ty)
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
            let mut ty = ctx.ast.get_type(base_type).clone();
            ty.qualifiers |= *qualifiers;
            ty
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

            Type::new(TypeKind::Array {
                element_type: ctx.ast.push_type(element_type),
                size: array_size,
            })
        }
        Declarator::Function(base, params) => {
            // Check for function pointer: a pointer declarator inside the function base
            if let Declarator::Pointer(qualifiers, Some(inner_base)) = &**base {
                // This is a pointer to a function.
                // The `base_type` applies to the return type of the function.
                let return_type = apply_declarator(base_type, inner_base, ctx);

                let parameters = lower_function_parameters(params, ctx);

                // Build the function type first
                let function_type = Type::new(TypeKind::Function {
                    return_type: ctx.ast.push_type(return_type),
                    parameters,
                    is_variadic: false, // TODO
                });
                let function_type_ref = ctx.ast.push_type(function_type);

                // Then wrap it in a pointer
                let mut pointer_type = Type::new(TypeKind::Pointer {
                    pointee: function_type_ref,
                });
                pointer_type.qualifiers = *qualifiers;
                return pointer_type;
            }

            // This is a regular function declaration.
            let return_type = apply_declarator(base_type, base, ctx);
            let parameters = lower_function_parameters(params, ctx);

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
pub fn run_symbol_resolver(ast: &mut Ast, diag: &mut DiagnosticEngine, symbol_table: &mut SymbolTable) {
    // Check if we have a root node to start traversal from
    let root_node_ref = ast.get_root();

    // Create lowering context
    let mut lower_ctx = LowerCtx::new(ast, diag, symbol_table);

    // Perform recursive scope-aware lowering
    lower_node_recursive(&mut lower_ctx, root_node_ref);
}

fn lower_node_recursive(ctx: &mut LowerCtx, node_ref: NodeRef) {
    let node_kind = {
        let node = ctx.ast.get_node(node_ref);
        node.kind.clone()
    };

    match node_kind {
        NodeKind::TranslationUnit(nodes) => {
            for node in nodes {
                lower_node_recursive(ctx, node);
            }
        }
        NodeKind::FunctionDef(func_def) => {
            // Extract function name from the declarator
            let func_name =
                extract_identifier(&func_def.declarator).unwrap_or_else(|| NameId::new("anonymous_function"));

            // Extract the return type from the function definition's specifiers
            let return_type_ref =
                lower_decl_specifiers_for_function_return(&func_def.specifiers, ctx, ctx.ast.get_node(node_ref).span)
                    .unwrap_or_else(|| ctx.ast.push_type(Type::new(TypeKind::Int { is_signed: true })));

            // Create the function type with the correct return type by applying the declarator
            let declarator_type = apply_declarator(return_type_ref, &func_def.declarator, ctx);
            let function_type_ref = ctx.ast.push_type(declarator_type);

            // Extract parameters from the function type for the symbol entry
            let parameters = if let TypeKind::Function { parameters, .. } = &ctx.ast.get_type(function_type_ref).kind {
                parameters.clone()
            } else {
                Vec::new()
            };

            // Switch to global scope to add the function
            let original_scope = ctx.symbol_table.current_scope();
            ctx.symbol_table.set_current_scope(ScopeId::GLOBAL);

            let symbol_entry = SymbolEntry {
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

            ctx.symbol_table.add_symbol(func_name, symbol_entry);

            // Restore original scope
            ctx.symbol_table.set_current_scope(original_scope);

            // Convert FunctionDef to Function semantic node
            // First, we need to get the symbol entry ref for the function we just added
            let (symbol_entry_ref, _) = ctx
                .symbol_table
                .lookup_symbol(func_name)
                .expect("Function should be in symbol table");

            // Create normalized parameters for the FunctionData
            let normalized_params = parameters
                .into_iter()
                .map(|param| {
                    // Create a symbol entry for the parameter
                    let param_symbol_entry = SymbolEntry {
                        name: param.name.unwrap_or_else(|| NameId::new("unnamed_param")),
                        kind: SymbolKind::Variable {
                            is_global: false,
                            initializer: None,
                        },
                        type_info: param.param_type,
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

            let function_node = Node::new(NodeKind::Function(function_data), ctx.ast.get_node(node_ref).span);
            let function_node_ref = ctx.ast.push_node(function_node);

            // Replace the FunctionDef node with the Function node
            ctx.ast
                .replace_node(node_ref, ctx.ast.get_node(function_node_ref).clone());

            // Now process the function body with proper scope management
            ctx.symbol_table.push_scope();
            lower_node_recursive(ctx, func_def.body);
            ctx.symbol_table.pop_scope();
        }
        NodeKind::CompoundStatement(nodes) => {
            ctx.symbol_table.push_scope();
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
            ctx.symbol_table.push_scope();
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
        NodeKind::Label(_, stmt) => {
            lower_node_recursive(ctx, stmt);
        }
        _ => {}
    }
}

/// Lower declaration specifiers for function return type
fn lower_decl_specifiers_for_function_return(
    specs: &[DeclSpecifier],
    ctx: &mut LowerCtx,
    span: SourceSpan,
) -> Option<TypeRef> {
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
                                apply_declarator_for_member(base_type_ref, &init_declarator.declarator, ctx);
                            ctx.ast.push_type(member_type_with_declarator)
                        } else {
                            ctx.ast.push_type(Type::new(TypeKind::Int { is_signed: true }))
                        };

                    flattened_members.push(StructMember {
                        name: member_name,
                        member_type,
                        bit_field_size: None,
                        span,
                    });
                }
            }
        }
    }

    flattened_members
}
