//! Declaration parsing module
//!
//! This module handles all declaration parsing logic, including type specifiers,
//! declarators, initializers, and top-level constructs like function definitions
//! and translation units.

use crate::ast::*;
use crate::diagnostic::ParseError;
use crate::lexer::{Token, TokenKind};
use crate::parser::declaration_core::parse_declaration_specifiers;
use crate::parser::utils::ParserExt;
use crate::source_manager::{SourceLoc, SourceSpan};
use log::debug;
use thin_vec::ThinVec;

use super::Parser;

/// Helper to extract function parameters from a potentially complex declarator
fn get_function_params(declarator: &Declarator) -> Option<&ThinVec<ParamData>> {
    let mut current = declarator;
    // Traverse the declarator to find the function part, which contains the parameters.
    // This handles cases like pointers to functions, e.g., `int (*f)(int a)`.
    loop {
        match current {
            Declarator::Function(_, params) => return Some(params),
            Declarator::Pointer(_, Some(inner)) | Declarator::Array(inner, _) | Declarator::BitField(inner, _) => {
                current = inner;
            }
            // These are terminal declarators that don't have parameters.
            Declarator::Identifier(_, _, _)
            | Declarator::AnonymousRecord(_, _)
            | Declarator::Abstract
            | Declarator::Pointer(_, None) => return None,
        }
    }
}

/// Parse a declaration
pub fn parse_declaration(parser: &mut Parser) -> Result<NodeRef, ParseError> {
    let trx = parser.start_transaction();
    let start_loc = trx.parser.current_token_span()?.start;

    debug!(
        "parse_declaration: starting at position {}, token {:?}",
        trx.parser.current_idx,
        trx.parser.current_token_kind()
    );

    // Check for _Static_assert (C11)
    if let Some(token) = trx.parser.accept(TokenKind::StaticAssert) {
        return parse_static_assert(trx.parser, token);
    }

    // Try to parse declaration specifiers
    let specifiers = match parse_declaration_specifiers(trx.parser) {
        Ok(specifiers) => {
            debug!(
                "parse_declaration: parsed {} specifiers, current token {:?}",
                specifiers.len(),
                trx.parser.current_token_kind()
            );
            debug!(
                "parse_declaration: current token after specifiers: {:?}",
                trx.parser.current_token_kind()
            );
            if let Some(last_specifier) = specifiers.last() {
                debug!(
                    "parse_declaration: last specifier type: {:?}",
                    match last_specifier {
                        DeclSpecifier::TypeSpecifier(ts) => std::mem::discriminant(ts),
                        _ => std::mem::discriminant(&TypeSpecifier::Void),
                    }
                );
            }
            specifiers
        }
        Err(e) => {
            return Err(e);
        }
    };

    // Special handling for struct/union/enum declarations
    // Check if any specifier is a struct/union/enum specifier (definition or forward declaration)
    let has_record_enum_type = specifiers.iter().any(|s| {
        matches!(
            s,
            DeclSpecifier::TypeSpecifier(TypeSpecifier::Record(_, _, _) | TypeSpecifier::Enum(_, _))
        )
    });
    let has_storage_class = specifiers.iter().any(|s| matches!(s, DeclSpecifier::StorageClass(_)));
    let is_record_enum_specifier = has_record_enum_type && !has_storage_class;

    // If we have a struct/union/enum specifier, we need to check if there are declarators following
    // The logic should be:
    // - If next token is semicolon: treat as record/enum declaration (definition or forward)
    // - If next token is declarator-starting token: continue with normal declaration parsing
    if is_record_enum_specifier {
        if let Some(semi) = trx.parser.accept(TokenKind::Semicolon) {
            // This is either:
            // 1. A pure struct/union/enum definition like "struct foo { ... };" or "enum E { ... };"
            // 2. A forward struct/union/enum declaration like "struct foo;" or "enum E;"
            // In both cases, consume the semicolon and create declaration with no declarators
            let declaration_data = DeclarationData {
                specifiers,
                init_declarators: ThinVec::new(),
            };

            let end_loc = semi.location.end;
            let span = SourceSpan::new(start_loc, end_loc);

            let node = trx.parser.push_node(NodeKind::Declaration(declaration_data), span);
            debug!(
                "parse_declaration: successfully parsed record/enum declaration, node_id={}",
                node.get()
            );
            trx.commit();
            return Ok(node);
        } else {
            // This is a record/enum specifier with declarators
            // Continue with normal declaration parsing (e.g., "struct foo { ... } var;")
            debug!("parse_declaration: record/enum specifier with declarators, continuing with normal parsing");
        }
    }

    // For all other cases, check if we have declarators
    let has_declarators = if trx.parser.is_token(TokenKind::Semicolon) {
        // Definitely no declarators
        false
    } else {
        // Check if we have a declarator-starting token
        // This includes: identifier, star, or left paren
        matches!(
            trx.parser.current_token_kind(),
            Some(TokenKind::Identifier(_)) | Some(TokenKind::Star) | Some(TokenKind::LeftParen)
        )
    };
    debug!("parse_declaration: has_declarators = {}", has_declarators);

    // If no declarators and this is not a record/enum definition, it's an error
    if !has_declarators {
        // Check if this looks like a record/enum definition
        // by looking at the last parsed specifier
        let message = if let Some(DeclSpecifier::TypeSpecifier(ts)) = specifiers.last() {
            match ts {
                TypeSpecifier::Record(_, _, _) => "Expected ';' after struct/union definition",
                TypeSpecifier::Enum(_, _) => "Expected ';' after enum definition",
                _ => "Expected declarator or identifier after type specifier",
            }
        } else {
            // No specifiers at all - this shouldn't happen
            "Expected type specifiers"
        };

        return Err(ParseError::SyntaxError {
            message: message.to_string(),
            location: trx.parser.current_token()?.location,
        });
    }

    // Parse init declarators
    let mut init_declarators = ThinVec::new();

    loop {
        let declarator_start_idx = trx.parser.current_idx;
        debug!(
            "parse_declaration: parsing declarator at position {}, token {:?}",
            declarator_start_idx,
            trx.parser.current_token_kind()
        );

        let declarator = match super::declarator::parse_declarator(trx.parser, None) {
            Ok(declarator) => {
                debug!(
                    "parse_declaration: parsed declarator, current token {:?}",
                    trx.parser.current_token_kind()
                );
                declarator
            }
            Err(e) => {
                return Err(e);
            }
        };

        let initializer = if trx.parser.accept(TokenKind::Assign).is_some() {
            debug!(
                "parse_declaration: found '=', parsing initializer at position {}",
                trx.parser.current_idx
            );
            match super::declaration_core::parse_initializer(trx.parser) {
                Ok(initializer) => {
                    debug!(
                        "parse_declaration: parsed initializer, now at position {} with token {:?}",
                        trx.parser.current_idx,
                        trx.parser.current_token_kind()
                    );
                    Some(initializer)
                }
                Err(e) => {
                    return Err(e);
                }
            }
        } else {
            None
        };

        init_declarators.push(InitDeclarator {
            declarator,
            initializer,
        });

        if !trx.parser.is_token(TokenKind::Comma) {
            break;
        }
        trx.parser.advance(); // consume comma
    }

    // Check for __attribute__ after declarator (GCC extension)
    if trx.parser.is_token(TokenKind::Attribute) {
        debug!("parse_declaration: found __attribute__ after declarator, parsing it");
        if let Err(_e) = super::declaration_core::parse_attribute(trx.parser) {
            debug!("parse_declaration: failed to parse __attribute__: {:?}", _e);
        }
    }

    // Check for semicolon at current position
    debug!(
        "parse_declaration: expecting semicolon, current token {:?}",
        trx.parser.current_token_kind()
    );
    let semicolon_token = if let Some(token) = trx.parser.accept(TokenKind::Semicolon) {
        token
    } else {
        return Err(ParseError::SyntaxError {
            message: "Expected ';' after declaration".to_string(),
            location: trx.parser.current_token()?.location,
        });
    };

    let end_loc = semicolon_token.location.end;

    let span = SourceSpan::new(start_loc, end_loc);

    // Track typedef and variable names for disambiguation
    let is_typedef = specifiers
        .iter()
        .any(|s| matches!(s, DeclSpecifier::StorageClass(StorageClass::Typedef)));
    for init_declarator in &init_declarators {
        if let Some(name) = trx.parser.get_declarator_name(&init_declarator.declarator) {
            if is_typedef {
                debug!("Adding typedef name: {:?}", name);
                trx.parser.add_typedef(name);
            } else {
                debug!("Adding variable to current scope: {:?}", name);
                // Create a dummy SymbolEntry for now. The semantic analysis phase will create a real one.
                let dummy_entry = SymbolEntry {
                    name,
                    kind: SymbolKind::Variable {
                        is_global: false,
                        is_static: false,
                        is_extern: false,
                        initializer: None,
                    },
                    type_info: TypeRef::new(1).unwrap(), // Dummy type
                    storage_class: None,
                    scope_id: 0, // Dummy scope
                    definition_span: SourceSpan::empty(),
                    is_defined: true,
                    is_referenced: false,
                    is_completed: true,
                };
                trx.parser.add_variable_to_current_scope(name, dummy_entry);
            }
        }
    }

    let declaration_data = DeclarationData {
        specifiers,
        init_declarators,
    };

    let node = trx.parser.push_node(NodeKind::Declaration(declaration_data), span);
    debug!(
        "parse_declaration: successfully parsed declaration, node_id={}",
        node.get()
    );
    trx.commit();
    Ok(node)
}

/// Parse function definition
pub fn parse_function_definition(parser: &mut Parser) -> Result<NodeRef, ParseError> {
    let start_loc = parser.current_token()?.location.start;

    // Parse declaration specifiers
    let specifiers = parse_declaration_specifiers(parser)?;

    // Parse declarator (should be a function declarator)
    let declarator = super::declarator::parse_declarator(parser, None)?;

    // A function definition introduces a new scope for its parameters.
    parser.enter_scope();

    // Extract parameter names from the declarator and add them to the new scope.
    if let Some(params) = get_function_params(&declarator) {
        for param in params {
            if let Some(declarator) = &param.declarator {
                if let Some(name) = parser.get_declarator_name(declarator) {
                    let dummy_entry = SymbolEntry {
                        name,
                        kind: SymbolKind::Variable {
                            is_global: false,
                            is_static: false,
                            is_extern: false,
                            initializer: None,
                        },
                        type_info: TypeRef::new(1).unwrap(), // Dummy type
                        storage_class: None,
                        scope_id: 0, // Dummy scope
                        definition_span: SourceSpan::empty(),
                        is_defined: true,
                        is_referenced: false,
                        is_completed: true,
                    };
                    parser.add_variable_to_current_scope(name, dummy_entry);
                }
            }
        }
    }

    // Parse function body. `parse_compound_statement` will also create a new scope for the body
    // and correctly handle exiting both the body scope and the parameter scope.
    let (body, body_end_loc) = super::statements::parse_compound_statement(parser)?;

    // After parsing the body, the parameter scope is no longer needed.
    parser.exit_scope();

    let span = SourceSpan::new(start_loc, body_end_loc);

    let function_def = FunctionDefData {
        specifiers,
        declarator,
        body,
    };

    let node = parser.push_node(NodeKind::FunctionDef(function_def), span);
    Ok(node)
}

/// Parse translation unit (top level)
pub fn parse_translation_unit(parser: &mut Parser) -> Result<NodeRef, ParseError> {
    let start_loc = parser.current_token()?.location.start;
    let mut end_loc = SourceLoc::empty();

    let mut top_level_declarations = Vec::new();
    let mut iteration_count = 0;
    const MAX_ITERATIONS: usize = 1000; // Prevent infinite loops

    while let Some(token) = parser.try_current_token() {
        if token.kind == TokenKind::EndOfFile {
            end_loc = token.location.end;
            break;
        }

        // Prevent infinite loops by limiting iterations
        iteration_count += 1;
        if iteration_count > MAX_ITERATIONS {
            debug!(
                "Parser exceeded maximum iteration limit at token {:?}, position {}",
                token.kind, parser.current_idx
            );
            return Err(ParseError::SyntaxError {
                message: format!(
                    "Parser exceeded maximum iteration limit - possible infinite loop at token {:?}",
                    token.kind
                ),
                location: token.location,
            });
        }

        let initial_idx = parser.current_idx;

        // Try parsing as declaration first
        match parse_declaration(parser) {
            Ok(declaration) => {
                top_level_declarations.push(declaration);
            }
            Err(_) => {
                // If declaration parsing failed, try function definition
                // Reset to initial position for backtracking
                parser.current_idx = initial_idx;
                match parse_function_definition(parser) {
                    Ok(func_def) => {
                        top_level_declarations.push(func_def);
                    }
                    Err(e) => {
                        parser.diag.report_parse_error(e);
                        parser.synchronize();
                    }
                }
            }
        }
    }

    let span = SourceSpan::new(start_loc, end_loc);
    let node = parser.push_node(NodeKind::TranslationUnit(top_level_declarations), span);

    parser.ast.set_root_node(node);

    Ok(node)
}

/// Parse static assert (C11)
pub fn parse_static_assert(parser: &mut Parser, start_token: Token) -> Result<NodeRef, ParseError> {
    // already consumed `_Static_assert`
    let start_loc = start_token.location.start;
    parser.expect(TokenKind::LeftParen)?;

    let condition = parser.parse_expr_min()?;

    parser.expect(TokenKind::Comma)?;

    let token = parser.try_current_token().ok_or_else(|| ParseError::SyntaxError {
        message: "Expected string literal in _Static_assert".to_string(),
        location: SourceSpan::empty(),
    })?;

    let message = match token.kind {
        TokenKind::StringLiteral(symbol) => symbol,
        _ => {
            return Err(ParseError::UnexpectedToken {
                expected_tokens: "string literal".to_string(),
                found: token.kind,
                location: token.location,
            });
        }
    };

    parser.advance();
    parser.expect(TokenKind::RightParen)?;
    let semicolon_token = parser.expect(TokenKind::Semicolon)?;
    let end_loc = semicolon_token.location.end;
    let span = SourceSpan::new(start_loc, end_loc);
    let node = parser.push_node(NodeKind::StaticAssert(condition, message), span);
    Ok(node)
}
