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
use thin_vec::ThinVec;

use super::Parser;

/// Parse declaration specifiers
pub(crate) fn parse_declaration_specifiers(parser: &mut Parser) -> Result<ThinVec<ParsedDeclSpecifier>, ParseError> {
    let mut specifiers = ThinVec::new();
    let mut has_type_specifier = false;

    while let Some(token) = parser.try_current_token() {
        match token.kind {
            TokenKind::Typedef
            | TokenKind::Extern
            | TokenKind::Static
            | TokenKind::Auto
            | TokenKind::Register
            | TokenKind::ThreadLocal => {
                let storage_class = match token.kind {
                    TokenKind::Typedef => StorageClass::Typedef,
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

            TokenKind::Const | TokenKind::Volatile | TokenKind::Restrict | TokenKind::Atomic => {
                let qualifier = match token.kind {
                    TokenKind::Const => TypeQualifier::Const,
                    TokenKind::Volatile => TypeQualifier::Volatile,
                    TokenKind::Restrict => TypeQualifier::Restrict,
                    TokenKind::Atomic => {
                        if parser.peek_token(0).is_some_and(|t| t.kind == TokenKind::LeftParen) {
                            parser.advance(); // consume `_Atomic`
                            parser.expect(TokenKind::LeftParen)?;
                            let parsed_type = super::parsed_type_builder::parse_parsed_type_name(parser)?;
                            parser.expect(TokenKind::RightParen)?;
                            specifiers.push(ParsedDeclSpecifier::TypeSpecifier(ParsedTypeSpecifier::Atomic(
                                parsed_type,
                            )));
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

            TokenKind::Inline | TokenKind::Noreturn => {
                let func_spec = match token.kind {
                    TokenKind::Inline => FunctionSpecifier::Inline,
                    _ => FunctionSpecifier::Noreturn,
                };
                parser.advance();
                specifiers.push(ParsedDeclSpecifier::FunctionSpecifier(func_spec));
            }

            TokenKind::Attribute => {
                let _ = parse_attribute(parser);
                specifiers.push(ParsedDeclSpecifier::Attribute);
            }

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
                specifiers.push(ParsedDeclSpecifier::TypeSpecifier(
                    super::type_specifiers::parse_type_specifier(parser)?,
                ));
                has_type_specifier = true;
            }

            TokenKind::Identifier(symbol) => {
                if !has_type_specifier && parser.is_type_name(symbol) {
                    specifiers.push(ParsedDeclSpecifier::TypeSpecifier(
                        super::type_specifiers::parse_type_specifier(parser)?,
                    ));
                    has_type_specifier = true;
                } else {
                    break;
                }
            }

            TokenKind::Alignas => {
                parser.advance();
                parser.expect(TokenKind::LeftParen)?;
                let next_token = parser.current_token()?;

                let is_type_start = if let TokenKind::Identifier(symbol) = next_token.kind {
                    parser.is_type_name(symbol)
                } else {
                    next_token.kind.is_declaration_specifier_start()
                };

                let alignment = if is_type_start {
                    let parsed_type = super::parsed_type_builder::parse_parsed_type_name(parser)?;
                    ParsedAlignmentSpecifier::Type(parsed_type)
                } else {
                    ParsedAlignmentSpecifier::Expr(parser.parse_expr_min()?)
                };
                parser.expect(TokenKind::RightParen)?;
                specifiers.push(ParsedDeclSpecifier::AlignmentSpecifier(alignment));
            }

            _ => break,
        }
    }

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
    let span = parser.current_token_span()?;

    if parser.accept(TokenKind::LeftBrace).is_some() {
        let mut initializers = Vec::new();

        while !parser.at_eof() && !parser.is_token(TokenKind::RightBrace) {
            let initializer = if parser.matches(&[TokenKind::Dot, TokenKind::LeftBracket]) {
                parse_designated_initializer(parser)?
            } else {
                let inner = if parser.is_token(TokenKind::LeftBrace) {
                    parse_initializer(parser)?
                } else {
                    parser.parse_expr_assignment()?
                };

                ParsedDesignatedInitializer {
                    designation: Vec::new(),
                    initializer: inner,
                }
            };

            initializers.push(initializer);
            if parser.accept(TokenKind::Comma).is_none() {
                break;
            }
        }

        let end_token = parser.expect(TokenKind::RightBrace)?;
        let span = SourceSpan::new(span.start(), end_token.span.end());
        Ok(parser.push_node(ParsedNodeKind::InitializerList(initializers), span))
    } else {
        parser.parse_expr_assignment()
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
        } else {
            parser.expect(TokenKind::LeftBracket)?;
            let start_expr = parser.parse_expr_min()?;

            if parser.accept(TokenKind::Ellipsis).is_some() {
                let end_expr = parser.parse_expr_min()?;
                parser.expect(TokenKind::RightBracket)?;
                designators.push(ParsedDesignator::GnuArrayRange(start_expr, end_expr));
            } else {
                parser.expect(TokenKind::RightBracket)?;
                designators.push(ParsedDesignator::ArrayIndex(start_expr));
            }
        }
    }

    Ok(designators)
}

/// Parse GCC __attribute__ syntax: __attribute__ (( attribute-list ))
/// For now, we parse and skip the attribute construct
pub(crate) fn parse_attribute(parser: &mut Parser) -> Result<(), ParseError> {
    parser.expect(TokenKind::Attribute)?;
    parser.expect(TokenKind::LeftParen)?;
    parser.expect(TokenKind::LeftParen)?;

    let mut depth = 2;
    while let Some(token) = parser.try_current_token() {
        match token.kind {
            TokenKind::LeftParen => depth += 1,
            TokenKind::RightParen => {
                depth -= 1;
                if depth == 0 {
                    parser.advance();
                    break;
                }
            }
            _ => {}
        }
        parser.advance();
    }
    Ok(())
}

/// Parse GCC __asm__ syntax: __asm__ ( string-literal )
pub(crate) fn parse_asm(parser: &mut Parser) -> Result<(), ParseError> {
    parser.expect(TokenKind::Asm)?;
    parser.expect(TokenKind::LeftParen)?;

    let mut depth = 1;
    while let Some(token) = parser.try_current_token() {
        match token.kind {
            TokenKind::LeftParen => depth += 1,
            TokenKind::RightParen => {
                depth -= 1;
                if depth == 0 {
                    parser.advance();
                    break;
                }
            }
            _ => {}
        }
        parser.advance();
    }
    Ok(())
}
