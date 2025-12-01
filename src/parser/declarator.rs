//! Declarator parsing module
//!
//! This module handles the parsing of C declarators, which are the most complex
//! part of C's declaration syntax. Declarators can be nested and include pointers,
//! arrays, and functions.

use crate::ast::*;
use crate::diagnostic::ParseError;
use crate::lexer::TokenKind;
use crate::parser::declaration_core::parse_declaration_specifiers;
use log::debug;
use symbol_table::GlobalSymbol as Symbol;
use thin_vec::{ThinVec, thin_vec};

use super::Parser;
use super::utils::ParserExt;

/// Helper enum for reconstructing complex declarators
#[derive(Debug)]
enum DeclaratorComponent {
    Pointer(TypeQualifiers),
}

/// Parse declarator
pub fn parse_declarator(parser: &mut Parser, initial_declarator: Option<Symbol>) -> Result<Declarator, ParseError> {
    debug!(
        "parse_declarator: starting at position {}, token: {:?}, initial_declarator: {:?}",
        parser.current_idx,
        parser.current_token_kind(),
        initial_declarator
    );

    // Check for __attribute__ before declarator (GCC extension)
    if parser.is_token(TokenKind::Attribute) {
        if let Err(_e) = super::declaration_core::parse_attribute(parser) {
            debug!("parse_declarator: failed to parse __attribute__: {:?}", _e);
        }
    }

    let mut declarator_chain: Vec<DeclaratorComponent> = Vec::new();
    let mut _current_qualifiers = TypeQualifiers::empty();

    // Parse leading pointers and their qualifiers
    while parser.accept(TokenKind::Star).is_some() {
        _current_qualifiers = parse_type_qualifiers(parser)?;
        declarator_chain.push(DeclaratorComponent::Pointer(_current_qualifiers));
        _current_qualifiers = TypeQualifiers::empty(); // Reset for next component
    }

    // Parse direct declarator (identifier or parenthesized declarator)
    let base_declarator = if parser.accept(TokenKind::LeftParen).is_some() {
        debug!("parse_declarator: found LeftParen, parsing parenthesized declarator");
        let inner_declarator = parse_declarator(parser, None)?;
        debug!(
            "parse_declarator: consumed RightParen, current token: {:?}",
            parser.current_token_kind()
        );
        parser.expect(TokenKind::RightParen)?; // Consume ')'
        inner_declarator
    } else if let Some(ident_symbol) = initial_declarator {
        Declarator::Identifier(ident_symbol, TypeQualifiers::empty(), None)
    } else if let Some(token) = parser.try_current_token() {
        if let TokenKind::Identifier(symbol) = token.kind {
            if parser.is_type_name(symbol) {
                // Identifier that is a type name, treat as abstract
                parse_abstract_declarator(parser)?
            } else {
                parser.advance(); // Consume identifier
                Declarator::Identifier(symbol, TypeQualifiers::empty(), None)
            }
        } else if parser.is_abstract_declarator_start() {
            parse_abstract_declarator(parser)?
        } else {
            // For abstract declarator, if nothing matches, it's just abstract
            Declarator::Abstract
        }
    } else {
        // Consume invalid tokens until ) or end
        while let Some(token) = parser.try_current_token() {
            if token.kind == TokenKind::RightParen {
                break;
            }
            debug!("parse_declarator: unexpected token {:?}, consuming", token.kind);
            parser.advance();
        }
        // For abstract declarator, if no token, it's abstract
        Declarator::Abstract
    };

    // Parse trailing array and function declarators
    let mut current_base = base_declarator;
    loop {
        if parser.accept(TokenKind::LeftBracket).is_some() {
            // Array declarator
            let array_size = parse_array_size(parser)?;
            parser.expect(TokenKind::RightBracket)?; // Consume ']'
            current_base = Declarator::Array(Box::new(current_base), array_size);
        } else if parser.accept(TokenKind::LeftParen).is_some() {
            // Function declarator
            let parameters = parse_function_parameters(parser)?;
            debug!(
                "parse_abstract_declarator: parsed function parameters, count: {}",
                parameters.len()
            );
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

    if parser.accept(TokenKind::Star).is_some() {
        Ok(ArraySize::Star { qualifiers })
    } else if parser.is_token(TokenKind::RightBracket) {
        // Empty []
        Ok(ArraySize::Incomplete)
    } else {
        // Assume it's an expression for the size
        let expr_node = parser.parse_expr_min()?;
        if is_static || !qualifiers.is_empty() {
            Ok(ArraySize::VlaSpecifier {
                is_static,
                qualifiers,
                size: Some(expr_node),
            })
        } else {
            Ok(ArraySize::Expression {
                expr: expr_node,
                qualifiers,
            })
        }
    }
}

/// Helper to parse function parameters
fn parse_function_parameters(parser: &mut Parser) -> Result<ThinVec<ParamData>, ParseError> {
    let mut params = ThinVec::new();

    if !parser.is_token(TokenKind::RightParen) {
        if parser.accept(TokenKind::Void).is_some() {
            // void parameter list
        } else {
            loop {
                if parser.accept(TokenKind::Ellipsis).is_some() {
                    // Variadic function
                    break;
                }

                // Check if we have a valid start for parameter declaration
                if !parser.is_declaration_start() {
                    break;
                }

                // Parse declaration specifiers for this parameter
                let start_idx = parser.current_idx;
                let saved_diagnostic_count = parser.diag.diagnostics.len();

                debug!(
                    "parse_function_parameters: attempting to parse specifiers at position {}, token: {:?}, is_type_name: {}",
                    start_idx,
                    parser.current_token_kind(),
                    if let Some(TokenKind::Identifier(sym)) = parser.current_token_kind() {
                        parser.is_type_name(sym)
                    } else {
                        false
                    }
                );

                let specifiers = match parse_declaration_specifiers(parser) {
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
                            "parse_function_parameters: specifier parsing failed at position {}, token: {:?}, error: {:?}, rolling back",
                            parser.current_idx,
                            parser.current_token_kind(),
                            _e
                        );
                        parser.current_idx = start_idx;
                        parser.diag.diagnostics.truncate(saved_diagnostic_count);

                        // Create a simple default specifier
                        thin_vec![DeclSpecifier::TypeSpecifier(TypeSpecifier::Int)]
                    }
                };

                // Try to parse declarator, but be more careful about failures
                let declarator = if !parser.is_token(TokenKind::Comma)
                    && !parser.is_token(TokenKind::RightParen)
                    && !parser.is_token(TokenKind::Ellipsis)
                {
                    // Special handling for abstract declarators in parameter context
                    if parser.is_token(TokenKind::LeftParen) {
                        debug!("parse_function_parameters: found LeftParen, trying abstract declarator parsing");
                        let start_idx = parser.current_idx;
                        match parse_abstract_declarator(parser) {
                            Ok(abstract_decl) => {
                                debug!("parse_function_parameters: abstract declarator parsed successfully");
                                Some(abstract_decl)
                            }
                            Err(e) => {
                                debug!(
                                    "parse_function_parameters: abstract declarator failed: {:?}, rolling back to {}",
                                    e, start_idx
                                );
                                parser.current_idx = start_idx;
                                // Try regular declarator parsing as fallback
                                match parse_declarator(parser, None) {
                                    Ok(decl) => {
                                        debug!("parse_function_parameters: fallback declarator parsing succeeded");
                                        Some(decl)
                                    }
                                    Err(_) => {
                                        debug!(
                                            "parse_function_parameters: both abstract and regular declarator parsing failed"
                                        );
                                        None
                                    }
                                }
                            }
                        }
                    } else {
                        // Regular declarator parsing for other cases
                        match parse_declarator(parser, None) {
                            Ok(declarator) => {
                                debug!(
                                    "parse_function_parameters: declarator parsed successfully, current token: {:?}",
                                    parser.current_token_kind()
                                );
                                Some(declarator)
                            }
                            Err(e) => {
                                debug!(
                                    "parse_function_parameters: declarator parsing failed: {:?}, current token: {:?}, position: {}",
                                    e,
                                    parser.current_token_kind(),
                                    parser.current_idx
                                );
                                None
                            }
                        }
                    }
                } else {
                    debug!(
                        "parse_function_parameters: skipping declarator parsing due to comma/paren/ellipsis, token: {:?}",
                        parser.current_token_kind()
                    );
                    None
                };

                params.push(ParamData { specifiers, declarator });

                debug!(
                    "parse_function_parameters: pushed parameter, current token: {:?}, position: {}",
                    parser.current_token_kind(),
                    parser.current_idx
                );

                if parser.accept(TokenKind::Comma).is_none() {
                    debug!(
                        "parse_function_parameters: no comma found, breaking from parameter loop. Current token: {:?}, position: {}",
                        parser.current_token_kind(),
                        parser.current_idx
                    );
                    break;
                }
                debug!("parse_function_parameters: found comma, continuing to next parameter");

                // After consuming comma, verify we're in a good state to continue
                if parser.is_token(TokenKind::RightParen) {
                    debug!("parse_function_parameters: found unexpected right paren after comma, breaking");
                    break;
                }
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
    debug!(
        "parse_abstract_declarator: starting at position {}, token {:?}",
        parser.current_idx,
        parser.current_token_kind()
    );

    // Check for __attribute__ at the beginning (GCC extension)
    if parser.is_token(TokenKind::Attribute) {
        if let Err(_e) = super::declaration_core::parse_attribute(parser) {
            debug!("parse_abstract_declarator: failed to parse __attribute__: {:?}", _e);
        }
    }

    let mut declarator_chain: Vec<DeclaratorComponent> = Vec::new();
    let mut _current_qualifiers = TypeQualifiers::empty();

    // Parse leading pointers and their qualifiers
    while parser.accept(TokenKind::Star).is_some() {
        _current_qualifiers = parse_type_qualifiers(parser)?;
        declarator_chain.push(DeclaratorComponent::Pointer(_current_qualifiers));
        _current_qualifiers = TypeQualifiers::empty(); // Reset for next component
    }

    // Parse direct abstract declarator (parenthesized or array/function)
    let base_declarator = if let Some(token) = parser.try_current_token() {
        match token.kind {
            TokenKind::Identifier(symbol) => {
                if parser.is_type_name(symbol) {
                    parser.advance(); // consume type name
                    // Check if next is identifier for named abstract declarator
                    if let Some(next_token) = parser.try_current_token() {
                        if let TokenKind::Identifier(name) = next_token.kind {
                            parser.advance(); // consume identifier
                            Declarator::Identifier(name, TypeQualifiers::empty(), None)
                        } else {
                            Declarator::Abstract
                        }
                    } else {
                        Declarator::Abstract
                    }
                } else {
                    parser.advance(); // consume invalid identifier
                    Declarator::Abstract
                }
            }
            TokenKind::Int => {
                parser.advance(); // consume int
                // Check if next is identifier
                if let Some(next_token) = parser.try_current_token() {
                    if let TokenKind::Identifier(name) = next_token.kind {
                        parser.advance(); // consume identifier
                        Declarator::Identifier(name, TypeQualifiers::empty(), None)
                    } else {
                        Declarator::Abstract
                    }
                } else {
                    Declarator::Abstract
                }
            }
            TokenKind::LeftParen => {
                debug!("parse_abstract_declarator: found LeftParen, parsing parenthesized");
                parser.advance(); // Consume '('
                if parser.accept(TokenKind::RightParen).is_some() {
                    // Empty parameter list: ()
                    Declarator::Function(Box::new(Declarator::Abstract), ThinVec::new())
                } else {
                    let start_idx = parser.current_idx;
                    let inner_declarator = parse_abstract_declarator(parser)?;
                    debug!(
                        "parse_abstract_declarator: inner declarator parsed, current token: {:?}",
                        parser.current_token_kind()
                    );
                    if parser.accept(TokenKind::RightParen).is_some() {
                        inner_declarator
                    } else {
                        // Check if we're dealing with a function parameter syntax like "int (int)"
                        // In this case, the closing paren might be part of the parameter list context
                        debug!(
                            "parse_abstract_declarator: expected RightParen but found {:?}, position: {}",
                            parser.current_token_kind(),
                            parser.current_idx
                        );
                        // Try to parse as function declarator if we see another LeftParen
                        if parser.accept(TokenKind::LeftParen).is_some() {
                            debug!(
                                "parse_abstract_declarator: found another LeftParen, treating as function declarator"
                            );
                            let parameters = parse_function_parameters(parser)?;
                            parser.expect(TokenKind::RightParen)?; // Consume ')'
                            Declarator::Function(Box::new(inner_declarator), parameters)
                        } else {
                            // Roll back and try a different approach
                            parser.current_idx = start_idx;
                            Declarator::Abstract
                        }
                    }
                }
            }
            TokenKind::LeftBracket => {
                parser.advance(); // Consume '['
                let array_size = parse_array_size(parser)?;
                parser.expect(TokenKind::RightBracket)?; // Consume ']'
                Declarator::Array(Box::new(Declarator::Abstract), array_size)
            }
            TokenKind::Star => {
                parser.advance(); // Consume '*'
                let qualifiers = parse_type_qualifiers(parser)?;
                Declarator::Pointer(qualifiers, Some(Box::new(Declarator::Abstract)))
            }
            _ => {
                // invalid token, consume if not )
                if token.kind != TokenKind::RightParen {
                    parser.advance();
                }
                Declarator::Abstract
            }
        }
    } else {
        Declarator::Abstract
    };

    debug!(
        "parse_abstract_declarator: base_declarator parsed, current token {:?}",
        parser.current_token_kind()
    );

    // Parse trailing array and function declarators
    let mut current_base = base_declarator;
    loop {
        if parser.accept(TokenKind::LeftBracket).is_some() {
            // Array declarator
            let array_size = parse_array_size(parser)?;
            parser.expect(TokenKind::RightBracket)?; // Consume ']'
            current_base = Declarator::Array(Box::new(current_base), array_size);
        } else if parser.accept(TokenKind::LeftParen).is_some() {
            let parameters = parse_function_parameters(parser)?;
            debug!(
                "parse_abstract_declarator: parsed function parameters, count: {}",
                parameters.len()
            );
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
