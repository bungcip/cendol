//! Struct and union parsing module
//!
//! This module handles parsing of struct and union declarations,
//! including member declarations and anonymous structs/unions.

use thin_vec::ThinVec;

use crate::ast::parsed::*;
use crate::ast::*;
use crate::parser::declarations::parse_decl_specs;
use crate::parser::{ParseDiag, TokenKind};

use super::Parser;

/// Parse struct or union specifier with context
pub(super) fn parse_record_spec(parser: &mut Parser, is_union: bool) -> Result<TypeSpec, ParseDiag> {
    let mut attributes = parser.parse_attributes_lenient();

    let tag = parser.accept_name();

    let definition = if parser.accept(TokenKind::LeftBrace).is_some() {
        let members = parse_struct_decl_list(parser)?;
        parser.expect(TokenKind::RightBrace)?;

        // Check for attributes after struct definition
        attributes.extend(parser.parse_attributes_lenient());

        Some(members)
    } else {
        None
    };

    Ok(TypeSpec::Record(is_union, tag, definition, attributes))
}

/// Parse struct declaration list
fn parse_struct_decl_list(parser: &mut Parser) -> Result<Vec<ParsedNodeRef>, ParseDiag> {
    let mut declarations = Vec::new();

    while !parser.at_eof() && !parser.is_token(TokenKind::RightBrace) {
        if let Some(token) = parser.try_current_token()
            && let TokenKind::PragmaPack(kind) = token.kind
        {
            let node = parser.push_node(ParsedNodeKind::PragmaPack(kind), token.span);
            declarations.push(node);
            parser.advance();
            continue;
        }

        if let Some(token) = parser.try_current_token()
            && let TokenKind::PragmaVisibility(kind) = token.kind
        {
            let node = parser.push_node(ParsedNodeKind::PragmaVisibility(kind), token.span);
            declarations.push(node);
            parser.advance();
            continue;
        }

        let declaration = parse_struct_decl(parser)?;
        declarations.push(declaration);
    }

    Ok(declarations)
}

/// Parse struct declaration
fn parse_struct_decl(parser: &mut Parser) -> Result<ParsedNodeRef, ParseDiag> {
    // Check for _Static_assert (C11)
    if let Some(token) = parser.accept(TokenKind::StaticAssert) {
        return super::declarations::parse_static_assert(parser, token);
    }

    let start_loc = parser.current_token_span()?.start();

    let mut specifiers = parse_decl_specs(parser)?;

    let has_record_enum_type = specifiers
        .iter()
        .any(|s| matches!(s, DeclSpec::TypeSpec(TypeSpec::Record(..) | TypeSpec::Enum(..))));

    let init_declarators = if has_record_enum_type && parser.accept(TokenKind::Semicolon).is_some() {
        ThinVec::new()
    } else {
        let decls = parse_init_declarators(parser)?;
        super::declarations::parse_trailing_attributes_and_asm(parser, &mut specifiers)?;
        parser.expect(TokenKind::Semicolon)?;
        decls
    };

    let decl = ParsedDecl {
        specifiers,
        init_declarators,
    };

    let span = SourceSpan::new(start_loc, parser.previous_token_span().end());
    Ok(parser.push_node(ParsedNodeKind::Declaration(decl), span))
}

fn parse_init_declarators(parser: &mut Parser) -> Result<ThinVec<ParsedInitDeclarator>, ParseDiag> {
    let mut decls = ThinVec::new();
    loop {
        let start = parser.current_token_span_or_empty();
        let declarator = super::declarator::parse_declarator(parser, true)?;
        let span = start.merge(parser.last_token_span().unwrap_or(start));
        decls.push(ParsedInitDeclarator {
            declarator,
            initializer: None,
            span,
        });
        if parser.accept(TokenKind::Comma).is_none() {
            break;
        }
    }
    Ok(decls)
}
