//! Declaration parsing module
//!
//! This module handles all declaration parsing logic, including type specifiers,
//! declarators, initializers, and top-level constructs like function definitions
//! and translation units.

use crate::ast::*;
use crate::diagnostic::ParseError;
use crate::lexer::{Token, TokenKind};
use crate::source_manager::{SourceLoc, SourceSpan};
use log::debug;
use symbol_table::GlobalSymbol as Symbol;
use thin_vec::ThinVec;

use super::Parser;

/// Parse a declaration
pub fn parse_declaration(parser: &mut Parser) -> Result<NodeRef, ParseError> {
    let start_span = parser.current_token()?.location.start;
    let initial_idx = parser.current_idx; // Save initial position for potential rollback
    let saved_diagnostic_count = parser.diag.diagnostics.len();

    debug!(
        "parse_declaration: starting at position {}, token {:?}",
        initial_idx,
        parser.current_token_kind()
    );

    // Check for _Static_assert (C11)
    if let Some(token) = parser.accept(TokenKind::StaticAssert) {
        return parse_static_assert(parser, token);
    }

    // Try to parse declaration specifiers
    let specifiers = match super::declaration_core::parse_declaration_specifiers(parser) {
        Ok(specifiers) => {
            debug!(
                "parse_declaration: parsed {} specifiers, current token {:?}",
                specifiers.len(),
                parser.current_token_kind()
            );
            debug!(
                "parse_declaration: current token after specifiers: {:?}",
                parser.current_token_kind()
            );
            if let Some(last_specifier) = specifiers.last() {
                debug!(
                    "parse_declaration: last specifier type: {:?}",
                    std::mem::discriminant(&last_specifier.type_specifier)
                );
            }
            specifiers
        }
        Err(e) => {
            // If declaration specifiers parsing fails, roll back completely
            parser.current_idx = initial_idx;
            parser.diag.diagnostics.truncate(saved_diagnostic_count);
            debug!(
                "parse_declaration: specifier parsing failed, rolled back to {}",
                initial_idx
            );
            return Err(e);
        }
    };

    // Special handling for struct/union/enum declarations
    // Check if any specifier is a struct/union/enum specifier (definition or forward declaration)
    let is_record_enum_specifier = specifiers.iter().any(|s| matches!(&s.type_specifier, TypeSpecifier::Record(_, _, _) | TypeSpecifier::Enum(_, _)) && s.storage_class.is_none());

    // If we have a struct/union/enum specifier, we need to check if there are declarators following
    // The logic should be:
    // - If next token is semicolon: treat as record/enum declaration (definition or forward)
    // - If next token is declarator-starting token: continue with normal declaration parsing
    if is_record_enum_specifier {
        if parser.matches(&[TokenKind::Semicolon]) {
            // This is either:
            // 1. A pure struct/union/enum definition like "struct foo { ... };" or "enum E { ... };"
            // 2. A forward struct/union/enum declaration like "struct foo;" or "enum E;"
            // In both cases, consume the semicolon and create declaration with no declarators
            parser.expect(TokenKind::Semicolon)?;

            let declaration_data = DeclarationData {
                specifiers,
                init_declarators: ThinVec::new(),
            };

            let end_span = parser.current_token()?.location.end;
            let span = SourceSpan::new(start_span, end_span);

            let node = parser
                .ast
                .push_node(Node::new(NodeKind::Declaration(declaration_data), span));
            debug!(
                "parse_declaration: successfully parsed record/enum declaration, node_id={}",
                node.get()
            );
            return Ok(node);
        } else {
            // This is a record/enum specifier with declarators
            // Continue with normal declaration parsing (e.g., "struct foo { ... } var;")
            debug!(
                "parse_declaration: record/enum specifier with declarators, continuing with normal parsing"
            );
        }
    }

    // For all other cases, check if we have declarators
    let has_declarators = if parser.matches(&[TokenKind::Semicolon]) {
        // Definitely no declarators
        false
    } else {
        // Check if we have a declarator-starting token
        // This includes: identifier, star, or left paren
        matches!(
            parser.current_token_kind(),
            Some(TokenKind::Identifier(_)) | Some(TokenKind::Star) | Some(TokenKind::LeftParen)
        )
    };
    debug!("parse_declaration: has_declarators = {}", has_declarators);

    // If no declarators and this is not a record/enum definition, it's an error
    if !has_declarators {
        // Check if this looks like a record/enum definition
        // by looking at the last parsed specifier
        if let Some(last_specifier) = specifiers.last() {
            match &last_specifier.type_specifier {
                TypeSpecifier::Record(_, _tag, _definition) => {
                    // This should not happen due to the check above, but just in case
                    parser.current_idx = initial_idx;
                    parser.diag.diagnostics.truncate(saved_diagnostic_count);
                    debug!(
                        "parse_declaration: record definition with no declarators and no semicolon, rolled back to {}",
                        initial_idx
                    );
                    return Err(ParseError::SyntaxError {
                        message: "Expected ';' after struct/union definition".to_string(),
                        location: parser.current_token()?.location,
                    });
                }
                TypeSpecifier::Enum(_tag, _definition) => {
                    // This should not happen due to the check above, but just in case
                    parser.current_idx = initial_idx;
                    parser.diag.diagnostics.truncate(saved_diagnostic_count);
                    debug!(
                        "parse_declaration: enum definition with no declarators and no semicolon, rolled back to {}",
                        initial_idx
                    );
                    return Err(ParseError::SyntaxError {
                        message: "Expected ';' after enum definition".to_string(),
                        location: parser.current_token()?.location,
                    });
                }
                _ => {
                    // Not a record/enum definition, this is likely an error
                    // But let's rollback and let the statement parser handle it
                    parser.current_idx = initial_idx;
                    parser.diag.diagnostics.truncate(saved_diagnostic_count);
                    debug!(
                        "parse_declaration: no declarators found, rolled back to {}",
                        initial_idx
                    );
                    return Err(ParseError::SyntaxError {
                        message: "Expected declarator or identifier after type specifier"
                            .to_string(),
                        location: parser.current_token()?.location,
                    });
                }
            }
        } else {
            // No specifiers at all - this shouldn't happen
            parser.current_idx = initial_idx;
            parser.diag.diagnostics.truncate(saved_diagnostic_count);
            debug!(
                "parse_declaration: no specifiers, rolled back to {}",
                initial_idx
            );
            return Err(ParseError::SyntaxError {
                message: "Expected type specifiers".to_string(),
                location: parser.current_token()?.location,
            });
        }
    }

    // Parse init declarators
    let mut init_declarators = ThinVec::new();

    loop {
        let declarator_start_idx = parser.current_idx;
        debug!(
            "parse_declaration: parsing declarator at position {}, token {:?}",
            declarator_start_idx,
            parser.current_token_kind()
        );

        let declarator = match super::declarator::parse_declarator(parser, None) {
            Ok(declarator) => {
                debug!(
                    "parse_declaration: parsed declarator, current token {:?}",
                    parser.current_token_kind()
                );
                declarator
            }
            Err(e) => {
                // If declarator parsing fails, roll back completely
                parser.current_idx = initial_idx;
                parser.diag.diagnostics.truncate(saved_diagnostic_count);
                debug!(
                    "parse_declaration: declarator parsing failed, rolled back to {}",
                    initial_idx
                );
                return Err(e);
            }
        };

        let _initializer_start_idx = parser.current_idx;
        let initializer = if parser.matches(&[TokenKind::Assign]) {
            parser.advance(); // consume '='
            debug!(
                "parse_declaration: found '=', parsing initializer at position {}",
                parser.current_idx
            );
            match super::declaration_core::parse_initializer(parser) {
                Ok(initializer) => {
                    debug!(
                        "parse_declaration: parsed initializer, now at position {} with token {:?}",
                        parser.current_idx,
                        parser.current_token_kind()
                    );
                    Some(initializer)
                }
                Err(e) => {
                    // If initializer parsing fails, roll back completely
                    parser.current_idx = initial_idx;
                    parser.diag.diagnostics.truncate(saved_diagnostic_count);
                    debug!(
                        "parse_declaration: initializer parsing failed, rolled back to {}",
                        initial_idx
                    );
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

        if !parser.matches(&[TokenKind::Comma]) {
            break;
        }
        parser.advance(); // consume comma
    }

    // Check for semicolon at current position
    debug!(
        "parse_declaration: expecting semicolon, current token {:?}",
        parser.current_token_kind()
    );
    let semicolon_token = if parser.matches(&[TokenKind::Semicolon]) {
        parser.advance().ok_or_else(|| ParseError::SyntaxError {
            message: "Unexpected end of input".to_string(),
            location: SourceSpan::empty(),
        })?
    } else {
        // If semicolon is missing, roll back completely
        parser.current_idx = initial_idx;
        parser.diag.diagnostics.truncate(saved_diagnostic_count);
        debug!(
            "parse_declaration: missing semicolon, rolled back to {}",
            initial_idx
        );
        return Err(ParseError::SyntaxError {
            message: "Expected ';' after declaration".to_string(),
            location: parser.current_token()?.location,
        });
    };

    let end_span = semicolon_token.location.end;

    let span = SourceSpan::new(start_span, end_span);

    // Track typedef names for disambiguation
    for specifier in &specifiers {
        if specifier.storage_class == Some(StorageClass::Typedef) {
            for init_declarator in &init_declarators {
                if let Some(name) = parser.get_declarator_name(&init_declarator.declarator) {
                    parser.add_typedef(name);
                }
            }
        }
    }

    let declaration_data = DeclarationData {
        specifiers,
        init_declarators,
    };

    let node = parser
        .ast
        .push_node(Node::new(NodeKind::Declaration(declaration_data), span));
    debug!(
        "parse_declaration: successfully parsed declaration, node_id={}",
        node.get()
    );
    Ok(node)
}














/// Parse function definition
pub fn parse_function_definition(parser: &mut Parser) -> Result<NodeRef, ParseError> {
    let start_span = parser.current_token()?.location.start;

    // Parse declaration specifiers
    let specifiers = super::declaration_core::parse_declaration_specifiers(parser)?;

    // Parse declarator (should be a function declarator)
    let declarator = super::declarator::parse_declarator(parser, None)?;

    // Parse function body
    let (body, body_end_span) = super::statements::parse_compound_statement(parser)?;

    let span = SourceSpan::new(start_span, body_end_span);

    let function_def = FunctionDefData {
        specifiers,
        declarator,
        body,
    };

    let node = parser
        .ast
        .push_node(Node::new(NodeKind::FunctionDef(function_def), span));
    Ok(node)
}

/// Parse translation unit (top level)
pub fn parse_translation_unit(parser: &mut Parser) -> Result<NodeRef, ParseError> {
    let start_span = parser.current_token()?.location.start;
    let mut end_span = SourceLoc::empty();

    let mut top_level_declarations = Vec::new();
    let mut iteration_count = 0;
    const MAX_ITERATIONS: usize = 1000; // Prevent infinite loops

    while let Some(token) = parser.try_current_token() {
        if token.kind == TokenKind::EndOfFile {
            end_span = token.location.end;
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

    let span = SourceSpan::new(start_span, end_span);
    let node = parser.ast.push_node(Node::new(
        NodeKind::TranslationUnit(top_level_declarations),
        span,
    ));

    parser.ast.set_root_node(node);

    Ok(node)
}

/// Check if current tokens indicate start of a declaration
pub fn is_declaration_start(parser: &Parser) -> bool {
    debug!(
        "is_declaration_start: checking token {:?}",
        parser.current_token_kind()
    );
    if let Some(token) = parser.try_current_token() {
        match token.kind {
            TokenKind::Typedef
            | TokenKind::Extern
            | TokenKind::Static
            | TokenKind::Auto
            | TokenKind::Register
            | TokenKind::ThreadLocal
            | TokenKind::Const
            | TokenKind::Volatile
            | TokenKind::Restrict
            | TokenKind::Atomic
            | TokenKind::Inline
            | TokenKind::Noreturn
            | TokenKind::Void
            | TokenKind::Char
            | TokenKind::Short
            | TokenKind::Int
            | TokenKind::Long
            | TokenKind::Float
            | TokenKind::Double
            | TokenKind::Signed
            | TokenKind::Unsigned
            | TokenKind::Bool
            | TokenKind::Complex
            | TokenKind::Struct
            | TokenKind::Union
            | TokenKind::Enum
            | TokenKind::Alignas => true,
            TokenKind::Identifier(symbol) => {
                // Check if it's a typedef name
                let is_type = parser.is_type_name(symbol);
                debug!(
                    "is_declaration_start: identifier {:?}, is_type_name={}",
                    symbol, is_type
                );
                is_type
            }
            // Exclude sizeof and other expression-only keywords that might be mistaken for type names
            TokenKind::Sizeof | TokenKind::Alignof | TokenKind::Generic => false,
            _ => false,
        }
    } else {
        false
    }
}

/// Check if current token starts a type name
pub fn is_type_name_start(parser: &Parser) -> bool {
    debug!(
        "is_type_name_start: checking token {:?} at position {}",
        parser.current_token_kind(),
        parser.current_idx
    );

    if let Some(token) = parser.try_current_token() {
        let result = matches!(
            token.kind,
            TokenKind::Void
                | TokenKind::Char
                | TokenKind::Short
                | TokenKind::Int
                | TokenKind::Long
                | TokenKind::Float
                | TokenKind::Double
                | TokenKind::Signed
                | TokenKind::Unsigned
                | TokenKind::Bool
                | TokenKind::Complex
                | TokenKind::Struct
                | TokenKind::Union
                | TokenKind::Enum
                | TokenKind::Const
                | TokenKind::Volatile
                | TokenKind::Restrict
                | TokenKind::Atomic
        );

        // For identifiers, only consider them type name starts if they are actually typedef names
        let is_identifier_type = if let TokenKind::Identifier(symbol) = token.kind {
            parser.is_type_name(symbol)
        } else {
            false
        };

        let final_result = result || is_identifier_type;

        debug!(
            "is_type_name_start: token {:?} is type name start: {} (direct: {}, identifier: {})",
            token.kind, final_result, result, is_identifier_type
        );
        final_result
    } else {
        debug!("is_type_name_start: no token available");
        false
    }
}

/// Parse static assert (C11)
pub fn parse_static_assert(parser: &mut Parser, start_token: Token) -> Result<NodeRef, ParseError> {
    // already consumed `_Static_assert`
    let start_span = start_token.location.start;
    parser.expect(TokenKind::LeftParen)?;

    let condition_result = super::expressions::parse_expression(parser, super::expressions::BindingPower::MIN)?;
    let condition = match condition_result {
        super::ParseExprOutput::Expression(node) => node,
        _ => {
            return Err(ParseError::SyntaxError {
                message: "Expected expression in _Static_assert condition".to_string(),
                location: parser.current_token().unwrap().location,
            });
        }
    };

    parser.expect(TokenKind::Comma)?;

    let token = parser
        .try_current_token()
        .ok_or_else(|| ParseError::SyntaxError {
            message: "Expected string literal in _Static_assert".to_string(),
            location: SourceSpan::empty(),
        })?;

    let message = match token.kind {
        TokenKind::StringLiteral(symbol) => symbol,
        _ => {
            return Err(ParseError::UnexpectedToken {
                expected: vec![TokenKind::StringLiteral(Symbol::new(""))],
                found: token.kind,
                location: token.location,
            });
        }
    };

    parser.advance();
    parser.expect(TokenKind::RightParen)?;
    let semicolon_token = parser.expect(TokenKind::Semicolon)?;
    let end_span = semicolon_token.location.end;

    let span = SourceSpan::new(start_span, end_span);

    let node = parser.ast.push_node(Node::new(NodeKind::StaticAssert(condition, message), span));
    Ok(node)
}