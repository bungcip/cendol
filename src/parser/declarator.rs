//! Declarator parsing module
//!
//! This module handles the parsing of C declarators, which are the most complex
//! part of C's declaration syntax. Declarators can be nested and include pointers,
//! arrays, and functions.

use crate::ast::*;
use crate::diagnostic::ParseError;
use crate::lexer::TokenKind;
use crate::source_manager::SourceSpan;
use log::debug;
use symbol_table::GlobalSymbol as Symbol;

use super::Parser;

/// Helper enum for reconstructing complex declarators
#[derive(Debug)]
enum DeclaratorComponent {
    Pointer(TypeQualifiers),
}

/// Parse declarator
pub fn parse_declarator(
    parser: &mut Parser,
    initial_declarator: Option<Symbol>,
) -> Result<Declarator, ParseError> {
    let mut declarator_chain: Vec<DeclaratorComponent> = Vec::new();
    let mut _current_qualifiers = TypeQualifiers::empty();

    // Parse leading pointers and their qualifiers
    while parser.matches(&[TokenKind::Star]) {
        parser.advance(); // Consume '*'
        _current_qualifiers = parse_type_qualifiers(parser)?;
        declarator_chain.push(DeclaratorComponent::Pointer(_current_qualifiers));
        _current_qualifiers = TypeQualifiers::empty(); // Reset for next component
    }

    // Parse direct declarator (identifier or parenthesized declarator)
    let base_declarator = if parser.matches(&[TokenKind::LeftParen]) {
        parser.advance(); // Consume '('
        let inner_declarator = parse_declarator(parser, None)?;
        parser.expect(TokenKind::RightParen)?; // Consume ')'
        inner_declarator
    } else if let Some(ident_symbol) = initial_declarator {
        Declarator::Identifier(ident_symbol, TypeQualifiers::empty(), None)
    } else if let Some(token) = parser.try_current_token() {
        if let TokenKind::Identifier(symbol) = token.kind {
            parser.advance(); // Consume identifier
            Declarator::Identifier(symbol, TypeQualifiers::empty(), None)
        } else if parser.is_abstract_declarator_start() {
            parse_abstract_declarator(parser)?
        } else {
            return Err(ParseError::UnexpectedToken {
                expected: vec![
                    TokenKind::Star,
                    TokenKind::LeftParen,
                    TokenKind::LeftBracket,
                    TokenKind::Identifier(Symbol::new("")),
                ],
                found: token.kind,
                location: token.location,
            });
        }
    } else {
        return Err(ParseError::SyntaxError {
            message: "Expected declarator".to_string(),
            location: SourceSpan::empty(),
        });
    };

    // Parse trailing array and function declarators
    let mut current_base = base_declarator;
    loop {
        if parser.matches(&[TokenKind::LeftBracket]) {
            // Array declarator
            parser.advance(); // Consume '['
            let array_size = parse_array_size(parser)?;
            parser.expect(TokenKind::RightBracket)?; // Consume ']'
            current_base = Declarator::Array(Box::new(current_base), array_size);
        } else if parser.matches(&[TokenKind::LeftParen]) {
            // Function declarator
            parser.advance(); // Consume '('
            let parameters = parse_function_parameters(parser)?;
            parser.expect(TokenKind::RightParen)?; // Consume ')'
            current_base = Declarator::Function(Box::new(current_base), parameters);
        } else {
            break;
        }
    }

    // Reconstruct the declarator chain in reverse order
    let mut final_declarator = current_base;
    for component in declarator_chain.into_iter().rev() {
        final_declarator = match component {
            DeclaratorComponent::Pointer(qualifiers) => {
                Declarator::Pointer(qualifiers, Some(Box::new(final_declarator)))
            }
        };
    }

    Ok(final_declarator)
}

/// Helper to parse type qualifiers
fn parse_type_qualifiers(parser: &mut Parser) -> Result<TypeQualifiers, ParseError> {
    let mut qualifiers = TypeQualifiers::empty();
    while let Some(token) = parser.try_current_token() {
        match token.kind {
            TokenKind::Const => {
                qualifiers.insert(TypeQualifiers::CONST);
                parser.advance();
            }
            TokenKind::Volatile => {
                qualifiers.insert(TypeQualifiers::VOLATILE);
                parser.advance();
            }
            TokenKind::Restrict => {
                qualifiers.insert(TypeQualifiers::RESTRICT);
                parser.advance();
            }
            TokenKind::Atomic => {
                qualifiers.insert(TypeQualifiers::ATOMIC);
                parser.advance();
            }
            _ => break,
        }
    }
    Ok(qualifiers)
}

/// Helper to parse array size
fn parse_array_size(parser: &mut Parser) -> Result<ArraySize, ParseError> {
    let is_static = parser.accept(TokenKind::Static).is_some();
    let qualifiers = parse_type_qualifiers(parser)?;

    if parser.matches(&[TokenKind::Star]) {
        parser.advance();
        Ok(ArraySize::Star { qualifiers })
    } else if parser.matches(&[TokenKind::RightBracket]) {
        // Empty []
        Ok(ArraySize::Incomplete)
    } else {
        // Assume it's an expression for the size
        let expr_result = super::expressions::parse_expression(parser, super::expressions::BindingPower::MIN)?;
        match expr_result {
            super::ParseExprOutput::Expression(expr_node) => {
                if is_static || !qualifiers.is_empty() {
                    Ok(ArraySize::VlaSpecifier { is_static, qualifiers, size: Some(expr_node) })
                } else {
                    Ok(ArraySize::Expression { expr: expr_node, qualifiers })
                }
            }
            _ => Err(ParseError::SyntaxError {
                message: "Expected array size expression".to_string(),
                location: parser.current_token().unwrap().location,
            }),
        }
    }
}

/// Helper to parse function parameters
fn parse_function_parameters(parser: &mut Parser) -> Result<Vec<ParamData>, ParseError> {
    let mut params = Vec::new();

    if !parser.matches(&[TokenKind::RightParen]) {
        if parser.matches(&[TokenKind::Void]) {
            // void parameter list
            parser.advance();
        } else {
            loop {
                if parser.matches(&[TokenKind::Ellipsis]) {
                    // Variadic function
                    parser.advance();
                    break;
                }

                // Parse declaration specifiers for this parameter
                let start_idx = parser.current_idx;
                let saved_diagnostic_count = parser.diag.diagnostics.len();

                let specifiers = match super::declaration_core::parse_declaration_specifiers(parser) {
                    Ok(specifiers) => {
                        debug!(
                            "parse_function_parameters: successfully parsed specifiers, current token: {:?}",
                            parser.current_token_kind()
                        );
                        specifiers
                    }
                    Err(_e) => {
                        // If specifier parsing fails, we might be at a position where we need
                        // to fall back to parsing without a proper declarator
                        debug!(
                            "parse_function_parameters: specifier parsing failed, rolling back"
                        );
                        parser.current_idx = start_idx;
                        parser.diag.diagnostics.truncate(saved_diagnostic_count);

                        // Create a simple default specifier
                        vec![DeclSpecifier {
                            storage_class: None,
                            type_qualifiers: TypeQualifiers::empty(),
                            function_specifiers: FunctionSpecifiers::empty(),
                            alignment_specifier: None,
                            type_specifier: TypeSpecifier::Int,
                        }]
                    }
                };

                // Try to parse declarator, but be more careful about failures
                let declarator = if !parser.matches(&[TokenKind::Comma])
                    && !parser.matches(&[TokenKind::RightParen])
                    && !parser.matches(&[TokenKind::Ellipsis])
                {
                    // Check if we can even attempt declarator parsing
                    let can_parse_declarator = parser
                        .current_token_kind()
                        .map(|k| {
                            matches!(
                                k,
                                TokenKind::Identifier(_)
                                    | TokenKind::Star
                                    | TokenKind::LeftParen
                                    | TokenKind::LeftBracket
                            )
                        })
                        .unwrap_or(false);

                    if can_parse_declarator {
                        match parse_declarator(parser, None) {
                            Ok(declarator) => Some(declarator),
                            Err(e) => {
                                debug!(
                                    "parse_function_parameters: declarator parsing failed: {:?}",
                                    e
                                );
                                // If declarator parsing fails, we still want to continue
                                // with a None declarator
                                None
                            }
                        }
                    } else {
                        None
                    }
                } else {
                    None
                };

                params.push(ParamData {
                    specifiers,
                    declarator,
                });

                if !parser.matches(&[TokenKind::Comma]) {
                    break;
                }
                parser.advance(); // consume comma
            }
        }
    }

    Ok(params)
}

/// Check if current token starts an abstract declarator
pub fn is_abstract_declarator_start(parser: &Parser) -> bool {
    if let Some(token) = parser.try_current_token() {
        match token.kind {
            TokenKind::Star => true,        // pointer
            TokenKind::LeftParen => true,   // parenthesized abstract declarator
            TokenKind::LeftBracket => true, // array
            _ => false,
        }
    } else {
        false
    }
}

/// Extract the declared name from a declarator, if any
pub fn get_declarator_name(declarator: &Declarator) -> Option<Symbol> {
    match declarator {
        Declarator::Identifier(name, _, _) => Some(*name),
        Declarator::Pointer(_, Some(inner)) => get_declarator_name(inner),
        Declarator::Array(inner, _) => get_declarator_name(inner),
        Declarator::Function(inner, _) => get_declarator_name(inner),
        Declarator::AnonymousRecord(_, _) => None,
        Declarator::Abstract => None,
        Declarator::Pointer(_, None) => None,
    }
}

/// Parse abstract declarator (for type names without identifiers)
pub fn parse_abstract_declarator(parser: &mut Parser) -> Result<Declarator, ParseError> {
    let mut declarator_chain: Vec<DeclaratorComponent> = Vec::new();
    let mut _current_qualifiers = TypeQualifiers::empty();

    // Parse leading pointers and their qualifiers
    while parser.matches(&[TokenKind::Star]) {
        parser.advance(); // Consume '*'
        _current_qualifiers = parse_type_qualifiers(parser)?;
        declarator_chain.push(DeclaratorComponent::Pointer(_current_qualifiers));
        _current_qualifiers = TypeQualifiers::empty(); // Reset for next component
    }

    // Parse direct abstract declarator (parenthesized or array/function)
    let base_declarator = if parser.matches(&[TokenKind::LeftParen]) {
        parser.advance(); // Consume '('
        let inner_declarator = parse_abstract_declarator(parser)?;
        parser.expect(TokenKind::RightParen)?; // Consume ')'
        inner_declarator
    } else {
        Declarator::Abstract
    };

    // Parse trailing array and function declarators
    let mut current_base = base_declarator;
    loop {
        if parser.matches(&[TokenKind::LeftBracket]) {
            // Array declarator
            parser.advance(); // Consume '['
            let array_size = parse_array_size(parser)?;
            parser.expect(TokenKind::RightBracket)?; // Consume ']'
            current_base = Declarator::Array(Box::new(current_base), array_size);
        } else if parser.matches(&[TokenKind::LeftParen]) {
            // Function declarator
            parser.advance(); // Consume '('
            let parameters = parse_function_parameters(parser)?;
            parser.expect(TokenKind::RightParen)?; // Consume ')'
            current_base = Declarator::Function(Box::new(current_base), parameters);
        } else {
            break;
        }
    }

    // Reconstruct the declarator chain in reverse order
    let mut final_declarator = current_base;
    for component in declarator_chain.into_iter().rev() {
        final_declarator = match component {
            DeclaratorComponent::Pointer(qualifiers) => {
                Declarator::Pointer(qualifiers, Some(Box::new(final_declarator)))
            }
        };
    }

    Ok(final_declarator)
}