//! Declarator parsing module
//!
//! This module handles the parsing of C declarators, which are the most complex
//! part of C's declaration syntax. Declarators can be nested and include pointers,
//! arrays, and functions.

use crate::diagnostic::{ParseError, ParseErrorKind};
use crate::parser::{Token, TokenKind};
use crate::{ast::*, semantic::TypeQualifiers};
use thin_vec::thin_vec;

use super::Parser;

/// Helper enum for reconstructing complex declarators
#[derive(Debug)]
enum DeclaratorComponent {
    Pointer(TypeQualifiers),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DeclaratorKind {
    Array,
    Function,
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
    arena: &ParsedTypeArena,
    base_ref: DeclaratorRef,
    new_kind: DeclaratorKind,
    span: SourceSpan,
) -> Result<(), ParseError> {
    let base = arena.get_decl(base_ref);
    if matches!(
        (&base, new_kind),
        (
            ParsedDeclarator::Function { .. },
            DeclaratorKind::Array | DeclaratorKind::Function
        ) | (ParsedDeclarator::Array { .. }, DeclaratorKind::Function)
    ) {
        return Err(ParseError {
            span,
            kind: ParseErrorKind::DeclarationNotAllowed,
        });
    }
    Ok(())
}

pub(crate) fn parse_declarator(parser: &mut Parser) -> Result<DeclaratorRef, ParseError> {
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
                parser
                    .ast
                    .parsed_types
                    .alloc_decl(ParsedDeclarator::Identifier(Some(symbol)))
            }
            _ if parser.is_abstract_declarator_start() => parse_abstract_declarator(parser)?,
            _ => parser.ast.parsed_types.alloc_decl(ParsedDeclarator::Identifier(None)),
        }
    } else {
        parser.ast.parsed_types.alloc_decl(ParsedDeclarator::Identifier(None))
    };

    let trailing = parse_trailing_declarators(parser, base)?;
    Ok(reconstruct_declarator_chain(parser, pointers, trailing))
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
            Ok(ParsedArraySize::VlaSpec {
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
    mut base: DeclaratorRef,
) -> Result<DeclaratorRef, ParseError> {
    while let Some(token) = parser.try_current_token() {
        match token.kind {
            TokenKind::LeftBracket => {
                parser.advance();
                validate_declarator_combination(&parser.ast.parsed_types, base, DeclaratorKind::Array, token.span)?;
                let size = parse_array_size(parser)?;
                parser.expect(TokenKind::RightBracket)?;
                base = parser
                    .ast
                    .parsed_types
                    .alloc_decl(ParsedDeclarator::Array { inner: base, size });
            }
            TokenKind::LeftParen => {
                parser.advance();
                validate_declarator_combination(&parser.ast.parsed_types, base, DeclaratorKind::Function, token.span)?;
                let (param_range, is_variadic) = parse_function_parameters(parser)?;
                parser.expect(TokenKind::RightParen)?;
                base = parser.ast.parsed_types.alloc_decl(ParsedDeclarator::Function {
                    inner: base,
                    params: param_range,
                    flags: FunctionFlags { is_variadic },
                });
            }
            _ => break,
        }
    }
    Ok(base)
}

fn parse_trailing_declarators(parser: &mut Parser, mut base: DeclaratorRef) -> Result<DeclaratorRef, ParseError> {
    while let Some(token) = parser.try_current_token() {
        match token.kind {
            TokenKind::LeftBracket => {
                parser.advance();
                validate_declarator_combination(&parser.ast.parsed_types, base, DeclaratorKind::Array, token.span)?;
                let size = parse_array_size(parser)?;
                parser.expect(TokenKind::RightBracket)?;
                base = parser
                    .ast
                    .parsed_types
                    .alloc_decl(ParsedDeclarator::Array { inner: base, size });
            }
            TokenKind::LeftParen => {
                parser.advance();
                validate_declarator_combination(&parser.ast.parsed_types, base, DeclaratorKind::Function, token.span)?;
                let (param_range, is_variadic) = parse_function_parameters(parser)?;
                parser.expect(TokenKind::RightParen)?;
                base = parser.ast.parsed_types.alloc_decl(ParsedDeclarator::Function {
                    inner: base,
                    params: param_range,
                    flags: FunctionFlags { is_variadic },
                });
            }
            TokenKind::Colon => {
                parser.advance();
                let width = parser.parse_expr_min()?;
                base = parser
                    .ast
                    .parsed_types
                    .alloc_decl(ParsedDeclarator::BitField { inner: base, width });
            }
            _ => break,
        }
    }
    Ok(base)
}

fn reconstruct_declarator_chain(
    parser: &mut Parser,
    chain: Vec<DeclaratorComponent>,
    mut base: DeclaratorRef,
) -> DeclaratorRef {
    for component in chain.into_iter().rev() {
        match component {
            DeclaratorComponent::Pointer(q) => {
                base = parser.ast.parsed_types.alloc_decl(ParsedDeclarator::Pointer {
                    qualifiers: q,
                    inner: base,
                });
            }
        }
    }
    base
}

fn parse_function_parameters(parser: &mut Parser) -> Result<(ParsedParamRange, bool), ParseError> {
    let mut params = Vec::new();
    let mut is_variadic = false;

    if parser.is_token(TokenKind::RightParen) {
        return Ok((parser.ast.parsed_types.alloc_params(params), is_variadic));
    }

    if parser.is_token(TokenKind::Void) && parser.peek_token(0).is_some_and(|t| t.kind == TokenKind::RightParen) {
        parser.advance();
        return Ok((parser.ast.parsed_types.alloc_params(params), is_variadic));
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
        let specifiers = match super::declaration_core::parse_declaration_specifiers(parser) {
            Ok(s) => s,
            Err(_) => {
                parser.current_idx = spec_idx;
                parser.diag.diagnostics.truncate(saved_diags);
                thin_vec![ParsedDeclSpec::TypeSpec(ParsedTypeSpec::Int)]
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

        let name = declarator
            .map(|d| get_declarator_name(&parser.ast.parsed_types, d))
            .flatten();
        let param_parsed_type =
            super::parsed_type_builder::build_parsed_type_from_specifiers(parser, &specifiers, declarator)?;

        let mut storage = None;
        let mut is_inline = false;
        let mut is_noreturn = false;
        let mut alignment = None;
        for spec in &specifiers {
            match spec {
                ParsedDeclSpec::StorageClass(sc) => storage = Some(*sc),
                ParsedDeclSpec::FunctionSpec(fs) => match fs {
                    FunctionSpec::Inline => is_inline = true,
                    FunctionSpec::Noreturn => is_noreturn = true,
                },
                ParsedDeclSpec::AlignmentSpec(align) => alignment = Some(align.clone()),
                _ => {}
            }
        }

        params.push(ParsedParam {
            name,
            ty: param_parsed_type,
            storage,
            is_inline,
            is_noreturn,
            alignment,
            span,
        });

        if parser.accept(TokenKind::Comma).is_none() {
            break;
        }
    }

    Ok((parser.ast.parsed_types.alloc_params(params), is_variadic))
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
pub(crate) fn get_declarator_name(arena: &ParsedTypeArena, decl_ref: DeclaratorRef) -> Option<NameId> {
    let declarator = arena.get_decl(decl_ref);
    match declarator {
        ParsedDeclarator::Identifier(name) => name,
        ParsedDeclarator::Pointer { inner, .. } => get_declarator_name(arena, inner),
        ParsedDeclarator::Array { inner, .. } => get_declarator_name(arena, inner),
        ParsedDeclarator::Function { inner, .. } => get_declarator_name(arena, inner),
        ParsedDeclarator::BitField { inner, .. } => get_declarator_name(arena, inner),
    }
}

/// Extract the parameters from a function declarator, if any
pub(super) fn get_declarator_params(arena: &ParsedTypeArena, decl_ref: DeclaratorRef) -> Option<ParsedParamRange> {
    let declarator = arena.get_decl(decl_ref);
    match declarator {
        ParsedDeclarator::Function { inner, params, .. } => {
            if let Some(inner_params) = get_declarator_params(arena, inner) {
                Some(inner_params)
            } else {
                Some(params)
            }
        }
        ParsedDeclarator::Pointer { inner, .. } => get_declarator_params(arena, inner),
        ParsedDeclarator::Array { inner, .. } => get_declarator_params(arena, inner),
        _ => None,
    }
}

pub(crate) fn parse_abstract_declarator(parser: &mut Parser) -> Result<DeclaratorRef, ParseError> {
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
                        parser
                            .ast
                            .parsed_types
                            .alloc_decl(ParsedDeclarator::Identifier(Some(name)))
                    } else {
                        parser.ast.parsed_types.alloc_decl(ParsedDeclarator::Identifier(None))
                    }
                } else {
                    parser.ast.parsed_types.alloc_decl(ParsedDeclarator::Identifier(None))
                }
            }
            TokenKind::Int => {
                parser.advance();
                if let Some(token) = parser.peek_token(0) {
                    if let TokenKind::Identifier(name) = token.kind {
                        parser.advance();
                        parser
                            .ast
                            .parsed_types
                            .alloc_decl(ParsedDeclarator::Identifier(Some(name)))
                    } else {
                        parser.ast.parsed_types.alloc_decl(ParsedDeclarator::Identifier(None))
                    }
                } else {
                    parser.ast.parsed_types.alloc_decl(ParsedDeclarator::Identifier(None))
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
                    parser.ast.parsed_types.alloc_decl(ParsedDeclarator::Identifier(None))
                } else {
                    parser.advance(); // consume '('
                    if parser.accept(TokenKind::RightParen).is_some() {
                        let inner = parser.ast.parsed_types.alloc_decl(ParsedDeclarator::Identifier(None));
                        let params = parser.ast.parsed_types.alloc_params(Vec::new());
                        parser.ast.parsed_types.alloc_decl(ParsedDeclarator::Function {
                            inner,
                            params,
                            flags: FunctionFlags { is_variadic: false },
                        })
                    } else {
                        let inner = parse_abstract_declarator(parser)?;
                        if parser.accept(TokenKind::RightParen).is_some() {
                            inner
                        } else if parser.accept(TokenKind::LeftParen).is_some() {
                            let (params, is_variadic) = parse_function_parameters(parser)?;
                            parser.expect(TokenKind::RightParen)?;
                            parser.ast.parsed_types.alloc_decl(ParsedDeclarator::Function {
                                inner,
                                params,
                                flags: FunctionFlags { is_variadic },
                            })
                        } else {
                            return Err(ParseError {
                                span: parser.current_token_span_or_empty(),
                                kind: ParseErrorKind::UnexpectedToken {
                                    expected: "')'",
                                    found: parser.current_token_kind().unwrap_or(TokenKind::EndOfFile),
                                },
                            });
                        }
                    }
                }
            }
            TokenKind::LeftBracket => {
                parser.advance();
                let size = parse_array_size(parser)?;
                parser.expect(TokenKind::RightBracket)?;
                let inner = parser.ast.parsed_types.alloc_decl(ParsedDeclarator::Identifier(None));
                parser
                    .ast
                    .parsed_types
                    .alloc_decl(ParsedDeclarator::Array { inner, size })
            }
            _ => parser.ast.parsed_types.alloc_decl(ParsedDeclarator::Identifier(None)),
        }
    } else {
        parser.ast.parsed_types.alloc_decl(ParsedDeclarator::Identifier(None))
    };

    let trailing = parse_trailing_declarators_for_type_names(parser, base)?;
    Ok(reconstruct_declarator_chain(parser, pointers, trailing))
}
