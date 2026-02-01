//! Core declaration parsing module
//!
//! This module handles the main declaration parsing logic, including
//! declaration specifiers, initializers, and coordination between
//! different declaration components.

use crate::ast::SourceSpan;
use crate::ast::nodes::FunctionSpecifier;
use crate::ast::nodes::StorageClass;
use crate::ast::nodes::TypeQualifier;
// Import all parsed types to be sure
use crate::ast::parsed::{
    ParsedAlignmentSpecifier, ParsedDeclSpecifier, ParsedDesignatedInitializer, ParsedDesignator, ParsedNodeKind,
    ParsedNodeRef, ParsedTypeSpecifier,
};
use crate::diagnostic::ParseError;
use crate::parser::TokenKind;
use log::debug;
use thin_vec::ThinVec;

use super::Parser;

/// Parse declaration specifiers
pub(crate) fn parse_declaration_specifiers(parser: &mut Parser) -> Result<ThinVec<ParsedDeclSpecifier>, ParseError> {
    let mut specifiers = ThinVec::new();
    let mut has_type_specifier = false;
    let start_idx = parser.current_idx;

    debug!(
        "parse_declaration_specifiers: starting at position {}, token {:?}",
        start_idx,
        parser.current_token_kind()
    );

    while let Some(token) = parser.try_current_token() {
        debug!(
            "parse_declaration_specifiers: loop iteration at position {}, token {:?}",
            parser.current_idx, token.kind
        );
        match token.kind {
            // Storage class specifiers
            TokenKind::Typedef
            | TokenKind::Extern
            | TokenKind::Static
            | TokenKind::Auto
            | TokenKind::Register
            | TokenKind::ThreadLocal => {
                let storage_class = match token.kind {
                    TokenKind::Typedef => {
                        debug!("Found Typedef token, setting storage_class Typedef");
                        StorageClass::Typedef
                    }
                    TokenKind::Extern => StorageClass::Extern,
                    TokenKind::Static => StorageClass::Static,
                    TokenKind::Auto => StorageClass::Auto,
                    TokenKind::Register => StorageClass::Register,
                    TokenKind::ThreadLocal => StorageClass::ThreadLocal,
                    _ => unreachable!(),
                };
                parser.advance();
                specifiers.push(ParsedDeclSpecifier::StorageClass(storage_class));
            }

            // Type qualifiers
            TokenKind::Const | TokenKind::Volatile | TokenKind::Restrict | TokenKind::Atomic => {
                let qualifier = match token.kind {
                    TokenKind::Const => TypeQualifier::Const,
                    TokenKind::Volatile => TypeQualifier::Volatile,
                    TokenKind::Restrict => TypeQualifier::Restrict,
                    TokenKind::Atomic => {
                        if parser.peek_token(0).is_some_and(|t| t.kind == TokenKind::LeftParen) {
                            // This is the `_Atomic(type-name)` form.
                            parser.advance(); // consume `_Atomic`
                            parser.expect(TokenKind::LeftParen)?;

                            let parsed_type = super::parsed_type_builder::parse_parsed_type_name(parser)?;

                            parser.expect(TokenKind::RightParen)?;
                            let type_specifier = ParsedTypeSpecifier::Atomic(parsed_type);
                            specifiers.push(ParsedDeclSpecifier::TypeSpecifier(type_specifier));
                            has_type_specifier = true;
                            continue;
                        }
                        TypeQualifier::Atomic
                    }
                    _ => unreachable!(),
                };
                parser.advance();
                specifiers.push(ParsedDeclSpecifier::TypeQualifier(qualifier));
            }

            // Function specifiers
            TokenKind::Inline | TokenKind::Noreturn => {
                let func_spec = if token.kind == TokenKind::Inline {
                    FunctionSpecifier::Inline
                } else {
                    FunctionSpecifier::Noreturn
                };
                parser.advance();
                specifiers.push(ParsedDeclSpecifier::FunctionSpecifier(func_spec));
            }

            TokenKind::Attribute => {
                debug!("parse_declaration_specifiers: found __attribute__, parsing it");
                if let Err(_e) = parse_attribute(parser) {
                    // For now, ignore attribute parsing errors
                }
                specifiers.push(ParsedDeclSpecifier::Attribute);
            }

            // Type specifiers
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
            | TokenKind::BuiltinVaList => {
                let type_specifier = super::type_specifiers::parse_type_specifier(parser)?;
                specifiers.push(ParsedDeclSpecifier::TypeSpecifier(type_specifier));
                has_type_specifier = true;
            }

            TokenKind::Identifier(symbol) => {
                debug!(
                    "parse_declaration_specifiers: found identifier {:?}, calling is_type_name, current position: {}",
                    symbol, parser.current_idx
                );
                let is_type = parser.is_type_name(symbol);
                debug!(
                    "parse_declaration_specifiers: is_type_name({:?}) = {}, has_type_specifier = {}",
                    symbol, is_type, has_type_specifier
                );
                if is_type && !has_type_specifier {
                    debug!(
                        "parse_declaration_specifiers: {:?} is a type name and no type specifier yet, parsing type specifier",
                        symbol
                    );
                    let type_specifier = super::type_specifiers::parse_type_specifier(parser)?;
                    specifiers.push(ParsedDeclSpecifier::TypeSpecifier(type_specifier));
                    has_type_specifier = true;
                } else {
                    debug!(
                        "parse_declaration_specifiers: {:?} is not a type name or already have type specifier, breaking at position {}",
                        symbol, parser.current_idx
                    );
                    break;
                }
            }

            // Alignment specifier
            TokenKind::Alignas => {
                parser.advance(); // consume _Alignas
                let alignment = if parser.accept(TokenKind::LeftParen).is_some() {
                    let next_token = parser.current_token()?;

                    let is_type_start = if let TokenKind::Identifier(symbol) = next_token.kind {
                        parser.is_type_name(symbol)
                    } else {
                        next_token.kind.is_declaration_specifier_start()
                    };

                    if is_type_start {
                        // _Alignas(type-name)
                        let parsed_type = super::parsed_type_builder::parse_parsed_type_name(parser)?;
                        parser.expect(TokenKind::RightParen)?;
                        ParsedAlignmentSpecifier::Type(parsed_type)
                    } else {
                        // _Alignas(constant-expression)
                        let expr = parser.parse_expr_min()?;
                        parser.expect(TokenKind::RightParen)?;
                        ParsedAlignmentSpecifier::Expr(expr)
                    }
                } else {
                    return Err(ParseError::UnexpectedToken {
                        expected_tokens: "'(' after _Alignas".to_string(),
                        found: token.kind,
                        span: token.span,
                    });
                };

                specifiers.push(ParsedDeclSpecifier::AlignmentSpecifier(alignment));
            }

            _ => {
                debug!(
                    "parse_declaration_specifiers: token {:?} not recognized as declaration specifier, breaking at position {}",
                    token.kind, parser.current_idx
                );
                if let TokenKind::Identifier(symbol) = &token.kind {
                    debug!("parse_declaration_specifiers: unrecognized identifier: {:?}", symbol);
                }
                break;
            }
        }
    }

    debug!(
        "parse_declaration_specifiers: ending at position {}, specifiers len={}, found {} specifiers",
        parser.current_idx,
        specifiers.len(),
        specifiers.len()
    );

    if specifiers.is_empty() {
        let current_token = parser.current_token()?;
        return Err(ParseError::UnexpectedToken {
            expected_tokens: "declaration specifiers".to_string(),
            found: current_token.kind,
            span: current_token.span,
        });
    }

    Ok(specifiers)
}

/// Parse initializer
pub(crate) fn parse_initializer(parser: &mut Parser) -> Result<ParsedNodeRef, ParseError> {
    debug!(
        "parse_initializer: called at position {}, current token: {:?}",
        parser.current_idx,
        parser.current_token_kind()
    );
    let span = parser.current_token_span()?;

    if parser.accept(TokenKind::LeftBrace).is_some() {
        debug!("parse_initializer: found LeftBrace, parsing compound initializer");
        // Compound initializer
        let mut initializers = Vec::new();

        while !parser.is_token(TokenKind::RightBrace) {
            // Check if this is a designated initializer (starts with . or [)
            let is_designated = parser.matches(&[TokenKind::Dot, TokenKind::LeftBracket]);

            let initializer = if is_designated {
                // Parse designated initializer
                parse_designated_initializer(parser)?
            } else {
                // Parse regular initializer (expression or nested compound initializer)
                let expr_or_compound = if parser.is_token(TokenKind::LeftBrace) {
                    // Nested compound initializer
                    parse_initializer(parser)?
                } else {
                    // Expression initializer - parse until comma or closing brace
                    parse_initializer_expression(parser)?
                };

                // Wrap in ParsedDesignatedInitializer with empty designation
                ParsedDesignatedInitializer {
                    designation: Vec::new(),
                    initializer: expr_or_compound,
                }
            };

            initializers.push(initializer);

            if parser.accept(TokenKind::Comma).is_none() {
                break;
            }
        }

        let end_token = parser.expect(TokenKind::RightBrace)?;
        let span = SourceSpan::new(span.start(), end_token.span.end());
        let initializer = parser.push_node(ParsedNodeKind::InitializerList(initializers), span);
        Ok(initializer)
    } else {
        debug!(
            "parse_initializer: no LeftBrace found, current token: {:?}, trying expression initializer",
            parser.current_token_kind()
        );
        // Expression initializer - use simple parsing to avoid comma operators
        let node = parse_initializer_expression(parser)?;
        Ok(node)
    }
}

/// Parse designated initializer
fn parse_designated_initializer(parser: &mut Parser) -> Result<ParsedDesignatedInitializer, ParseError> {
    let designation = if parser.matches(&[TokenKind::Dot, TokenKind::LeftBracket]) {
        parse_designation(parser)?
    } else {
        Vec::new()
    };

    parser.expect(TokenKind::Assign)?;
    let initializer = parse_initializer(parser)?;

    Ok(ParsedDesignatedInitializer {
        designation,
        initializer,
    })
}

/// Parse designation
fn parse_designation(parser: &mut Parser) -> Result<Vec<ParsedDesignator>, ParseError> {
    let mut designators = Vec::new();

    while parser.matches(&[TokenKind::Dot, TokenKind::LeftBracket]) {
        if parser.accept(TokenKind::Dot).is_some() {
            let (field_name, _) = parser.expect_name()?;
            designators.push(ParsedDesignator::FieldName(field_name));
        } else if parser.accept(TokenKind::LeftBracket).is_some() {
            // Check if this is a range designator (contains ellipsis)
            let start_expr = parser.parse_expr_min()?;

            // Check for ellipsis token indicating range syntax
            if parser.accept(TokenKind::Ellipsis).is_some() {
                let end_expr = parser.parse_expr_min()?;
                parser.expect(TokenKind::RightBracket)?;
                designators.push(ParsedDesignator::GnuArrayRange(start_expr, end_expr));
            } else {
                // Single index designator
                parser.expect(TokenKind::RightBracket)?;
                designators.push(ParsedDesignator::ArrayIndex(start_expr));
            }
        }
    }

    Ok(designators)
}

/// Parse expression for initializer (stops at commas that separate declarators)
fn parse_initializer_expression(parser: &mut Parser) -> Result<ParsedNodeRef, ParseError> {
    // Parse expressions in initializers, but stop at comma operators to avoid
    // consuming declarator-separating commas. Use assignment precedence to allow
    // most binary operators but prevent comma operators.
    parser.parse_expr_assignment()
}

/// Parse GCC __attribute__ syntax: __attribute__ (( attribute-list ))
/// For now, we parse and skip the attribute construct
pub(crate) fn parse_attribute(parser: &mut Parser) -> Result<(), ParseError> {
    debug!("parse_attribute: parsing __attribute__ construct");

    // Expect __attribute__
    parser.expect(TokenKind::Attribute)?;

    // Expect opening (
    parser.expect(TokenKind::LeftParen)?;

    // Expect opening (
    parser.expect(TokenKind::LeftParen)?;

    // Skip attribute list until we find ))
    let mut paren_depth = 2;
    while let Some(token) = parser.try_current_token() {
        match token.kind {
            TokenKind::LeftParen => {
                paren_depth += 1;
            }
            TokenKind::RightParen => {
                paren_depth -= 1;
                if paren_depth == 0 {
                    parser.advance();
                    break;
                }
            }
            _ => {}
        }
        parser.advance();
    }

    debug!("parse_attribute: successfully parsed __attribute__ construct");
    Ok(())
}
