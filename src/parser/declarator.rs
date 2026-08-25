//! Declarator parsing module
//!
//! This module handles the parsing of C declarators, which are the most complex
//! part of C's declaration syntax. Declarators can be nested and include pointers,
//! arrays, and functions.

use crate::parser::declarations::parse_decl_specs;
use crate::parser::type_builder::build_type;
use crate::parser::{ParseDiag, ParseError, Token, TokenKind};
use crate::{ast::*, semantic::TypeQuals};
use thin_vec::thin_vec;

use super::Parser;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DeclaratorKind {
    Array,
    Function,
}

/// Look ahead past a GCC-style `__attribute__((...))` construct without consuming tokens.
/// Returns the token immediately following the attribute if the structure is valid, or None.
///
/// Expects: Attribute (( ... ))
fn peek_past_attribute(parser: &mut Parser, mut start_offset: u32) -> Option<Token> {
    loop {
        start_offset += 1;
        if parser.peek_token(start_offset)?.kind != TokenKind::LeftParen {
            return None;
        }
        start_offset += 1;
        if parser.peek_token(start_offset)?.kind != TokenKind::LeftParen {
            return None;
        }
        start_offset += 1;

        let mut depth = 2;
        while depth > 0 {
            match parser.peek_token(start_offset)?.kind {
                TokenKind::LeftParen => depth += 1,
                TokenKind::RightParen => depth -= 1,
                _ => {}
            }
            start_offset += 1;
        }

        let t_next = parser.peek_token(start_offset)?;
        if t_next.kind != TokenKind::Attribute {
            return Some(t_next);
        }
    }
}

fn wrap_attributes(
    parser: &mut Parser,
    inner: DeclaratorRef,
    attrs: impl IntoIterator<Item = DeclSpec>,
) -> DeclaratorRef {
    attrs.into_iter().fold(inner, |acc, spec| {
        parser.alloc_decl(PDeclarator::Attribute { inner: acc, spec })
    })
}

/// Validate declarator combinations
fn validate_declarator(
    arena: &PTypeArena,
    base: DeclaratorRef,
    new_kind: DeclaratorKind,
    span: SourceSpan,
) -> Result<(), ParseDiag> {
    let base = arena.get_decl(base);
    if matches!(
        (&base, new_kind),
        (
            PDeclarator::Function { .. },
            DeclaratorKind::Array | DeclaratorKind::Function
        ) | (PDeclarator::Array { .. }, DeclaratorKind::Function)
    ) {
        return Err(ParseDiag {
            span,
            kind: ParseError::DeclarationNotAllowed,
        });
    }
    Ok(())
}

pub(crate) fn parse_declarator(parser: &mut Parser, allow_bitfield: bool) -> Result<DeclaratorRef, ParseDiag> {
    let mut attrs_before = Vec::new();
    while parser.is_token(TokenKind::Attribute) {
        attrs_before.extend(super::declarations::parse_attribute(parser)?);
    }

    let pointers = parse_leading_pointers(parser)?;

    let mut base = if parser.accept(TokenKind::LeftParen).is_some() {
        let inner = parse_declarator(parser, allow_bitfield)?;
        parser.expect(TokenKind::RightParen)?;
        inner
    } else {
        let token = parser.try_current_token();
        match token.map(|t| t.kind) {
            Some(TokenKind::Identifier(symbol)) => {
                parser.advance();
                parser.alloc_decl(PDeclarator::Identifier(Some(symbol)))
            }
            Some(_) if is_abstract_declarator_start(parser) => parse_abstract_declarator(parser, allow_bitfield)?,
            _ => parser.alloc_decl(PDeclarator::Identifier(None)),
        }
    };

    // Parse attributes after identifier or abstract declarator base
    while parser.is_token(TokenKind::Attribute) {
        let attrs = super::declarations::parse_attribute(parser)?;
        base = wrap_attributes(parser, base, attrs);
    }

    let trailing = parse_trailing_declarators(parser, base, allow_bitfield)?;
    let trailing = wrap_attributes(parser, trailing, attrs_before);

    Ok(reconstruct_declarator_chain(parser, pointers, trailing))
}

fn parse_type_quals(parser: &mut Parser) -> Result<TypeQuals, ParseDiag> {
    let mut quals = TypeQuals::empty();
    while let Some(token) = parser.try_current_token() {
        if let Some(q) = token.kind.as_type_qualifier() {
            quals.insert(TypeQuals::from_type_qualifier(q));
            parser.advance();
        } else {
            break;
        }
    }
    Ok(quals)
}

fn parse_array_size(parser: &mut Parser) -> Result<PArraySize, ParseDiag> {
    let is_static = parser.accept(TokenKind::Static).is_some();
    let quals = parse_type_quals(parser)?;

    if parser.accept(TokenKind::Star).is_some() {
        Ok(PArraySize::Star { quals })
    } else if parser.is_token(TokenKind::RightBracket) {
        Ok(PArraySize::Incomplete)
    } else {
        let expr = parser.parse_expr_min()?;
        if is_static || !quals.is_empty() {
            Ok(PArraySize::VlaSpec {
                is_static,
                quals,
                size: Some(expr),
            })
        } else {
            Ok(PArraySize::Expression { expr, quals })
        }
    }
}

fn parse_leading_pointers(parser: &mut Parser) -> Result<Vec<(TypeQuals, Vec<DeclSpec>)>, ParseDiag> {
    let mut pointers = Vec::new();
    while parser.accept(TokenKind::Star).is_some() {
        let quals = parse_type_quals(parser)?;
        let mut attrs = Vec::new();
        while parser.is_token(TokenKind::Attribute) {
            attrs.extend(super::declarations::parse_attribute(parser)?);
        }
        pointers.push((quals, attrs));
    }
    Ok(pointers)
}

/// Parses trailing declarators
fn parse_trailing_declarators(
    parser: &mut Parser,
    mut base: DeclaratorRef,
    allow_bitfield: bool,
) -> Result<DeclaratorRef, ParseDiag> {
    while let Some(token) = parser.try_current_token() {
        match token.kind {
            TokenKind::LeftBracket => {
                parser.advance();
                validate_declarator(&parser.ast.arena, base, DeclaratorKind::Array, token.span)?;
                let size = parse_array_size(parser)?;
                parser.expect(TokenKind::RightBracket)?;
                base = parser.alloc_decl(PDeclarator::Array { inner: base, size });
            }
            TokenKind::LeftParen => {
                parser.advance();
                validate_declarator(&parser.ast.arena, base, DeclaratorKind::Function, token.span)?;
                let (param_range, flags, scope_id) = parse_function_parameters(parser)?;
                parser.expect(TokenKind::RightParen)?;
                base = parser.alloc_decl(PDeclarator::Function {
                    inner: base,
                    params: param_range,
                    flags,
                    scope_id,
                });
            }
            TokenKind::Colon if allow_bitfield => {
                parser.advance();
                let width = parser.parse_expr_assignment()?;
                base = parser.alloc_decl(PDeclarator::BitField { inner: base, width });
            }
            TokenKind::Attribute => {
                let attrs = super::declarations::parse_attribute(parser)?;
                base = wrap_attributes(parser, base, attrs);
            }
            TokenKind::Asm => {
                if let Some(lit) = super::declarations::parse_asm(parser)? {
                    base = parser.alloc_decl(PDeclarator::Attribute {
                        inner: base,
                        spec: DeclSpec::AttributeAsm(lit),
                    });
                }
            }
            _ => break,
        }
    }
    Ok(base)
}

fn reconstruct_declarator_chain(
    parser: &mut Parser,
    chain: Vec<(TypeQuals, Vec<DeclSpec>)>,
    mut base: DeclaratorRef,
) -> DeclaratorRef {
    for (quals, attrs) in chain.into_iter().rev() {
        base = parser.alloc_decl(PDeclarator::Pointer { quals, inner: base });
        base = wrap_attributes(parser, base, attrs);
    }
    base
}

fn parse_function_parameters(parser: &mut Parser) -> Result<(PParamRange, FunctionFlags, ScopeId), ParseDiag> {
    let scope_id = parser.symbol_table.push_scope();
    let mut params = Vec::new();
    let mut is_variadic = false;

    if parser.is_token(TokenKind::RightParen) {
        parser.symbol_table.pop_scope();
        return Ok((parser.alloc_params(params), FunctionFlags::empty(), scope_id));
    }

    if parser.is_token(TokenKind::Void) && parser.peek_token(0).is_some_and(|t| t.kind == TokenKind::RightParen) {
        parser.advance();
        parser.symbol_table.pop_scope();
        return Ok((parser.alloc_params(params), FunctionFlags::HAS_PROTOTYPE, scope_id));
    }

    while !parser.at_eof() && !parser.is_token(TokenKind::RightParen) {
        if parser.accept(TokenKind::Ellipsis).is_some() {
            is_variadic = true;
            break;
        }

        if !parser.starts_declaration() {
            break;
        }

        let start_span = parser.current_token_span_or_empty();

        let specifiers = parser
            .transaction(parse_decl_specs)
            .unwrap_or_else(|_| thin_vec![DeclSpec::TypeSpec(TypeSpec::Int)]);

        let declarator = parse_param_declarator(parser);

        let span = start_span.merge(parser.last_token_span().unwrap_or(start_span));

        let name = declarator.and_then(|d| get_declarator_name(&parser.ast.arena, d));
        let param_ptype = build_type(parser, &specifiers, declarator)?;

        let (storage, is_thread_local, is_inline, is_noreturn, alignment) = extract_param_flags(&specifiers);

        if let Some(name_id) = name {
            parser.symbol_table.define_parser_non_typedef(name_id, span);
        }

        params.push(PParam {
            name,
            ty: param_ptype,
            storage,
            is_thread_local,
            is_inline,
            is_noreturn,
            alignment,
            span,
        });

        if parser.accept(TokenKind::Comma).is_none() {
            break;
        }
    }

    parser.symbol_table.pop_scope();
    Ok((
        parser.alloc_params(params),
        if is_variadic {
            FunctionFlags::HAS_PROTOTYPE | FunctionFlags::IS_VARIADIC
        } else {
            FunctionFlags::HAS_PROTOTYPE
        },
        scope_id,
    ))
}

/// Check if current token starts an abstract declarator
pub(crate) fn is_abstract_declarator_start(parser: &mut Parser) -> bool {
    parser.try_current_token().is_some_and(|token| {
        matches!(
            token.kind,
            TokenKind::Star | TokenKind::LeftParen | TokenKind::LeftBracket
        )
    })
}

/// Extract the declared name from a declarator, if any
pub(crate) fn get_declarator_name(arena: &PTypeArena, declarator: DeclaratorRef) -> Option<NameId> {
    let declarator = arena.get_decl(declarator);
    match declarator {
        PDeclarator::Identifier(name) => *name,
        PDeclarator::Pointer { inner, .. }
        | PDeclarator::Array { inner, .. }
        | PDeclarator::Function { inner, .. }
        | PDeclarator::BitField { inner, .. }
        | PDeclarator::Attribute { inner, .. } => get_declarator_name(arena, *inner),
    }
}

pub(crate) fn parse_abstract_declarator(parser: &mut Parser, allow_bitfield: bool) -> Result<DeclaratorRef, ParseDiag> {
    while parser.is_token(TokenKind::Attribute) {
        let _ = super::declarations::parse_attribute(parser);
    }

    let pointers = parse_leading_pointers(parser)?;
    let token = parser.try_current_token();
    let base = match token.map(|t| t.kind) {
        Some(TokenKind::LeftParen) => {
            let is_param = parser.peek_token(0).is_some_and(|next| {
                if next.kind == TokenKind::Attribute {
                    peek_past_attribute(parser, 0).is_some_and(|t| t.kind != TokenKind::Star)
                } else {
                    parser.is_type_name_start_token(&next.kind) || next.kind == TokenKind::RightParen
                }
            });

            if is_param {
                parser.alloc_decl(PDeclarator::Identifier(None))
            } else {
                parser.advance(); // consume '('
                let inner = parse_abstract_declarator(parser, allow_bitfield)?;
                parser.expect(TokenKind::RightParen)?;
                inner
            }
        }
        Some(TokenKind::LeftBracket) => {
            parser.advance();
            let size = parse_array_size(parser)?;
            parser.expect(TokenKind::RightBracket)?;
            let inner = parser.alloc_decl(PDeclarator::Identifier(None));
            parser.alloc_decl(PDeclarator::Array { inner, size })
        }
        _ => parser.alloc_decl(PDeclarator::Identifier(None)),
    };

    let trailing = parse_trailing_declarators(parser, base, allow_bitfield)?;
    Ok(reconstruct_declarator_chain(parser, pointers, trailing))
}

fn parse_param_declarator(parser: &mut Parser) -> Option<DeclaratorRef> {
    if parser.matches(&[TokenKind::Comma, TokenKind::RightParen, TokenKind::Ellipsis]) {
        return None;
    }
    if parser.is_token(TokenKind::LeftParen) {
        parser
            .transaction(|p| parse_abstract_declarator(p, false))
            .or_else(|_| parse_declarator(parser, false))
            .ok()
    } else {
        parse_declarator(parser, false).ok()
    }
}

fn extract_param_flags(specifiers: &[DeclSpec]) -> (StorageClass, bool, bool, bool, Option<PAlignmentSpec>) {
    let mut storage = StorageClass::None;
    let mut is_thread_local = false;
    let mut is_inline = false;
    let mut is_noreturn = false;
    let mut alignment = None;
    for spec in specifiers {
        match spec {
            DeclSpec::StorageClass(sc) => storage = *sc,
            DeclSpec::ThreadLocal => is_thread_local = true,
            DeclSpec::FunctionSpec(fs) => match fs {
                FunctionSpec::Inline => is_inline = true,
                FunctionSpec::Noreturn => is_noreturn = true,
            },
            DeclSpec::AlignmentSpec(align, _) => alignment = Some(align.clone()),
            _ => {}
        }
    }
    (storage, is_thread_local, is_inline, is_noreturn, alignment)
}
