//! Declarator parsing module
//!
//! This module handles the parsing of C declarators, which are the most complex
//! part of C's declaration syntax. Declarators can be nested and include pointers,
//! arrays, and functions.

use crate::diagnostic::ParseError;
use crate::parser::declaration_core::parse_declaration_specifiers;
use crate::parser::{Token, TokenKind};
use crate::{ast::*, semantic::TypeQualifiers};
use thin_vec::{ThinVec, thin_vec};

use super::Parser;

/// Helper enum for reconstructing complex declarators
#[derive(Debug)]
enum DeclaratorComponent {
    Pointer(TypeQualifiers),
}

/// Look ahead past a GCC-style `__attribute__((...))` construct without consuming tokens.
/// Returns the token immediately following the attribute if the structure is valid, or None.
///
/// Expects: Attribute (( ... ))
fn peek_past_attribute(parser: &Parser, mut start_offset: u32) -> Option<Token> {
    // Check for multiple attributes
    loop {
        // start_offset points to Attribute
        // Skip Attribute
        start_offset += 1;

        // Expect ((
        // If not ((, then it's not a GCC attribute (or it's ill-formed), stop
        if let Some(t) = parser.peek_token(start_offset) {
            if t.kind != TokenKind::LeftParen {
                return parser.peek_token(start_offset).cloned();
            }
        } else {
            return None;
        }
        start_offset += 1;

        if let Some(t) = parser.peek_token(start_offset) {
            if t.kind != TokenKind::LeftParen {
                return None;
            }
        } else {
            return None;
        }
        start_offset += 1;

        // Skip balanced parens
        let mut depth = 2; // We saw two LeftParens

        while depth > 0 {
            let t = parser.peek_token(start_offset)?;
            match t.kind {
                TokenKind::LeftParen => depth += 1,
                TokenKind::RightParen => depth -= 1,
                _ => {}
            }
            start_offset += 1;
        }

        // Now we are past one attribute.
        // Check if there is another one.
        if let Some(t) = parser.peek_token(start_offset) {
            if t.kind != TokenKind::Attribute {
                // Not an attribute, so we are done
                return Some(*t);
            }
            // It is an attribute, loop again (start_offset points to it)
        } else {
            return None;
        }
    }
}

/// Validate declarator combinations
fn validate_declarator_combination(
    base: &ParsedDeclarator,
    new_kind: &str,
    span: SourceSpan,
) -> Result<(), ParseError> {
    match base {
        ParsedDeclarator::Function { .. } => {
            if new_kind == "array" {
                return Err(ParseError::DeclarationNotAllowed { span });
            }
            if new_kind == "function" {
                return Err(ParseError::DeclarationNotAllowed { span });
            }
        }
        ParsedDeclarator::Array(..) => {
            if new_kind == "function" {
                return Err(ParseError::DeclarationNotAllowed { span });
            }
        }
        _ => {}
    }
    Ok(())
}

pub(crate) fn parse_declarator(parser: &mut Parser) -> Result<ParsedDeclarator, ParseError> {
    while parser.is_token(TokenKind::Attribute) {
        let _ = super::declaration_core::parse_attribute(parser);
    }

    let pointers = parse_leading_pointers(parser)?;

    let base = if parser.accept(TokenKind::LeftParen).is_some() {
        let inner = parse_declarator(parser)?;
        parser.expect(TokenKind::RightParen)?;
        inner
    } else if let Some(token) = parser.try_current_token() {
        match token.kind {
            TokenKind::Identifier(symbol) => {
                parser.advance();
                ParsedDeclarator::Identifier(symbol, TypeQualifiers::empty())
            }
            _ if parser.is_abstract_declarator_start() => parse_abstract_declarator(parser)?,
            _ => ParsedDeclarator::Abstract,
        }
    } else {
        ParsedDeclarator::Abstract
    };

    Ok(reconstruct_declarator_chain(
        pointers,
        parse_trailing_declarators(parser, base)?,
    ))
}

fn parse_type_qualifiers(parser: &mut Parser) -> Result<TypeQualifiers, ParseError> {
    let mut qualifiers = TypeQualifiers::empty();
    while let Some(token) = parser.try_current_token() {
        let q = match token.kind {
            TokenKind::Const => TypeQualifiers::CONST,
            TokenKind::Volatile => TypeQualifiers::VOLATILE,
            TokenKind::Restrict => TypeQualifiers::RESTRICT,
            TokenKind::Atomic => TypeQualifiers::ATOMIC,
            _ => break,
        };
        qualifiers.insert(q);
        parser.advance();
    }
    Ok(qualifiers)
}

fn parse_array_size(parser: &mut Parser) -> Result<ParsedArraySize, ParseError> {
    let is_static = parser.accept(TokenKind::Static).is_some();
    let qualifiers = parse_type_qualifiers(parser)?;

    if parser.accept(TokenKind::Star).is_some() {
        Ok(ParsedArraySize::Star { qualifiers })
    } else if parser.is_token(TokenKind::RightBracket) {
        Ok(ParsedArraySize::Incomplete)
    } else {
        let expr = parser.parse_expr_min()?;
        if is_static || !qualifiers.is_empty() {
            Ok(ParsedArraySize::VlaSpecifier {
                is_static,
                qualifiers,
                size: Some(expr),
            })
        } else {
            Ok(ParsedArraySize::Expression { expr, qualifiers })
        }
    }
}

fn parse_leading_pointers(parser: &mut Parser) -> Result<Vec<DeclaratorComponent>, ParseError> {
    let mut pointers = Vec::new();
    while parser.accept(TokenKind::Star).is_some() {
        pointers.push(DeclaratorComponent::Pointer(parse_type_qualifiers(parser)?));
    }
    Ok(pointers)
}

fn parse_trailing_declarators_for_type_names(
    parser: &mut Parser,
    mut base: ParsedDeclarator,
) -> Result<ParsedDeclarator, ParseError> {
    while let Some(token) = parser.try_current_token() {
        match token.kind {
            TokenKind::LeftBracket => {
                parser.advance();
                validate_declarator_combination(&base, "array", token.span)?;
                let size = parse_array_size(parser)?;
                parser.expect(TokenKind::RightBracket)?;
                base = ParsedDeclarator::Array(Box::new(base), size);
            }
            TokenKind::LeftParen => {
                parser.advance();
                validate_declarator_combination(&base, "function", token.span)?;
                let (params, is_variadic, has_proto) = parse_function_parameters(parser)?;
                parser.expect(TokenKind::RightParen)?;
                base = ParsedDeclarator::Function {
                    inner: Box::new(base),
                    params,
                    is_variadic,
                    has_proto,
                };
            }
            _ => break,
        }
    }
    Ok(base)
}

fn parse_trailing_declarators(parser: &mut Parser, mut base: ParsedDeclarator) -> Result<ParsedDeclarator, ParseError> {
    while let Some(token) = parser.try_current_token() {
        match token.kind {
            TokenKind::LeftBracket => {
                parser.advance();
                validate_declarator_combination(&base, "array", token.span)?;
                let size = parse_array_size(parser)?;
                parser.expect(TokenKind::RightBracket)?;
                base = ParsedDeclarator::Array(Box::new(base), size);
            }
            TokenKind::LeftParen => {
                parser.advance();
                validate_declarator_combination(&base, "function", token.span)?;
                let (params, is_variadic, has_proto) = parse_function_parameters(parser)?;
                parser.expect(TokenKind::RightParen)?;
                base = ParsedDeclarator::Function {
                    inner: Box::new(base),
                    params,
                    is_variadic,
                    has_proto,
                };
            }
            TokenKind::Colon => {
                parser.advance();
                base = ParsedDeclarator::BitField(Box::new(base), parser.parse_expr_min()?);
            }
            _ => break,
        }
    }
    Ok(base)
}

fn reconstruct_declarator_chain(chain: Vec<DeclaratorComponent>, mut base: ParsedDeclarator) -> ParsedDeclarator {
    for component in chain.into_iter().rev() {
        match component {
            DeclaratorComponent::Pointer(q) => base = ParsedDeclarator::Pointer(q, Some(Box::new(base))),
        }
    }
    base
}

// Returns (params, is_variadic, has_proto)
fn parse_function_parameters(
    parser: &mut Parser,
) -> Result<(ThinVec<ParsedParamData>, bool, bool), ParseError> {
    let mut params = ThinVec::new();
    let mut is_variadic = false;

    if parser.is_token(TokenKind::RightParen) {
        // () -> no parameters, no prototype (unspecified arguments in C)
        return Ok((params, is_variadic, false));
    }

    if parser.is_token(TokenKind::Void) && parser.peek_token(0).is_some_and(|t| t.kind == TokenKind::RightParen) {
        // (void) -> no parameters, yes prototype
        parser.advance();
        return Ok((params, is_variadic, true));
    }

    while !parser.at_eof() && !parser.is_token(TokenKind::RightParen) {
        if parser.accept(TokenKind::Ellipsis).is_some() {
            is_variadic = true;
            break;
        }

        if !parser.starts_declaration() {
            break;
        }

        let start_idx = parser.current_idx;
        let spec_idx = parser.current_idx;
        let saved_diags = parser.diag.diagnostics.len();
        let specifiers = match parse_declaration_specifiers(parser) {
            Ok(s) => s,
            Err(_) => {
                parser.current_idx = spec_idx;
                parser.diag.diagnostics.truncate(saved_diags);
                thin_vec![ParsedDeclSpecifier::TypeSpecifier(ParsedTypeSpecifier::Int)]
            }
        };

        let declarator = if !parser.matches(&[TokenKind::Comma, TokenKind::RightParen, TokenKind::Ellipsis]) {
            let decl_idx = parser.current_idx;
            let res = if parser.is_token(TokenKind::LeftParen) {
                parse_abstract_declarator(parser).or_else(|_| {
                    parser.current_idx = decl_idx;
                    parse_declarator(parser)
                })
            } else {
                parse_declarator(parser)
            };
            res.ok()
        } else {
            None
        };

        let span = parser
            .get_token_span(start_idx)
            .unwrap_or_default()
            .merge(parser.last_token_span().unwrap_or_default());
        params.push(ParsedParamData {
            specifiers,
            declarator,
            span,
        });

        if parser.accept(TokenKind::Comma).is_none() {
            break;
        }
    }

    // If we parsed some parameters, it's a prototype
    Ok((params, is_variadic, true))
}

/// Check if current token starts an abstract declarator
pub(crate) fn is_abstract_declarator_start(parser: &Parser) -> bool {
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
pub(crate) fn get_declarator_name(declarator: &ParsedDeclarator) -> Option<NameId> {
    match declarator {
        ParsedDeclarator::Identifier(name, _) => Some(*name),
        ParsedDeclarator::Pointer(_, Some(inner)) => get_declarator_name(inner),
        ParsedDeclarator::Array(inner, _) => get_declarator_name(inner),
        ParsedDeclarator::Function { inner, .. } => get_declarator_name(inner),
        ParsedDeclarator::BitField(inner, _) => get_declarator_name(inner),
        ParsedDeclarator::Abstract => None,
        ParsedDeclarator::Pointer(_, None) => None,
    }
}

pub(crate) fn parse_abstract_declarator(parser: &mut Parser) -> Result<ParsedDeclarator, ParseError> {
    while parser.is_token(TokenKind::Attribute) {
        let _ = super::declaration_core::parse_attribute(parser);
    }

    let pointers = parse_leading_pointers(parser)?;
    let base = if let Some(token) = parser.try_current_token() {
        match token.kind {
            TokenKind::Identifier(symbol) if parser.is_type_name(symbol) => {
                parser.advance();
                if let Some(token) = parser.peek_token(0) {
                    if let TokenKind::Identifier(name) = token.kind {
                        parser.advance();
                        ParsedDeclarator::Identifier(name, TypeQualifiers::empty())
                    } else {
                        ParsedDeclarator::Abstract
                    }
                } else {
                    ParsedDeclarator::Abstract
                }
            }
            TokenKind::Int => {
                parser.advance();
                if let Some(token) = parser.peek_token(0) {
                    if let TokenKind::Identifier(name) = token.kind {
                        parser.advance();
                        ParsedDeclarator::Identifier(name, TypeQualifiers::empty())
                    } else {
                        ParsedDeclarator::Abstract
                    }
                } else {
                    ParsedDeclarator::Abstract
                }
            }
            TokenKind::LeftParen => {
                let is_param = if let Some(next) = parser.peek_token(0) {
                    if next.kind == TokenKind::Attribute {
                        peek_past_attribute(parser, 0).is_some_and(|t| t.kind != TokenKind::Star)
                    } else {
                        parser.is_type_name_start_token(next) || next.kind == TokenKind::RightParen
                    }
                } else {
                    false
                };

                if is_param {
                    ParsedDeclarator::Abstract
                } else {
                    parser.advance(); // consume '('
                    if parser.accept(TokenKind::RightParen).is_some() {
                        ParsedDeclarator::Function {
                            inner: Box::new(ParsedDeclarator::Abstract),
                            params: ThinVec::new(),
                            is_variadic: false,
                            has_proto: false, // ()
                        }
                    } else {
                        let inner = parse_abstract_declarator(parser)?;
                        if parser.accept(TokenKind::RightParen).is_some() {
                            inner
                        } else if parser.accept(TokenKind::LeftParen).is_some() {
                            let (params, is_variadic, has_proto) = parse_function_parameters(parser)?;
                            parser.expect(TokenKind::RightParen)?;
                            ParsedDeclarator::Function {
                                inner: Box::new(inner),
                                params,
                                is_variadic,
                                has_proto,
                            }
                        } else {
                            return Err(ParseError::UnexpectedToken {
                                expected_tokens: "')'".to_string(),
                                found: parser.current_token_kind().unwrap_or(TokenKind::EndOfFile),
                                span: parser.current_token_span_or_empty(),
                            });
                        }
                    }
                }
            }
            TokenKind::LeftBracket => {
                parser.advance();
                let size = parse_array_size(parser)?;
                parser.expect(TokenKind::RightBracket)?;
                ParsedDeclarator::Array(Box::new(ParsedDeclarator::Abstract), size)
            }
            _ => ParsedDeclarator::Abstract,
        }
    } else {
        ParsedDeclarator::Abstract
    };

    Ok(reconstruct_declarator_chain(
        pointers,
        parse_trailing_declarators_for_type_names(parser, base)?,
    ))
}
