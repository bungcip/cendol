//! Struct and union parsing module
//!
//! This module handles parsing of struct and union declarations,
//! including member declarations and anonymous structs/unions.

use thin_vec::{ThinVec, thin_vec};

use crate::ast::parsed::*;
use crate::ast::*;
use crate::diagnostic::ParseError;
use crate::parser::TokenKind;
use crate::parser::declaration_core::parse_declaration_specifiers;

use super::Parser;

/// Parse struct or union specifier with context
pub(super) fn parse_record_specifier_with_context(
    parser: &mut Parser,
    is_union: bool,
) -> Result<ParsedTypeSpec, ParseError> {
    // Check for __attribute__ after struct/union keyword (GCC extension)
    if parser.is_token(TokenKind::Attribute)
        && let Err(_e) = super::declaration_core::parse_attribute(parser)
    {
        // For now, ignore attribute parsing errors
    }

    let tag = parser.accept_name();

    let definition = if parser.accept(TokenKind::LeftBrace).is_some() {
        let members = parse_struct_declaration_list(parser)?;
        parser.expect(TokenKind::RightBrace)?;

        // Check for __attribute__ after struct definition (GCC extension)
        if parser.is_token(TokenKind::Attribute)
            && let Err(_e) = super::declaration_core::parse_attribute(parser)
        {
            // For now, ignore attribute parsing errors
        }

        Some(ParsedRecordDef {
            tag,
            members: Some(members),
            is_union,
        })
    } else {
        None
    };

    Ok(ParsedTypeSpec::Record(is_union, tag, definition))
}

/// Parse struct declaration list
fn parse_struct_declaration_list(parser: &mut Parser) -> Result<Vec<ParsedNodeRef>, ParseError> {
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

        let declaration = parse_struct_declaration(parser)?;
        declarations.push(declaration);
    }

    Ok(declarations)
}

/// Parse struct declaration
fn parse_struct_declaration(parser: &mut Parser) -> Result<ParsedNodeRef, ParseError> {
    // Check for _Static_assert (C11)
    if let Some(token) = parser.accept(TokenKind::StaticAssert) {
        return super::declarations::parse_static_assert(parser, token);
    }

    let start_loc = parser.current_token_span()?.start();

    // Check if we have an anonymous struct/union
    let is_struct = parser.accept(TokenKind::Struct).is_some();
    let is_union = if !is_struct {
        parser.accept(TokenKind::Union).is_some()
    } else {
        false
    };
    let declaration_data = if is_struct || is_union {
        let tag = parser.accept_name();
        if parser.accept(TokenKind::LeftBrace).is_some() {
            let members = parse_struct_declaration_list(parser)?;
            parser.expect(TokenKind::RightBrace)?;

            let init_declarators = if parser.accept(TokenKind::Semicolon).is_some() {
                ThinVec::new()
            } else {
                let decls = parse_init_declarators_no_init(parser)?;
                parser.expect(TokenKind::Semicolon)?;
                decls
            };

            ParsedDeclaration {
                specifiers: thin_vec![ParsedDeclSpec::TypeSpec(ParsedTypeSpec::Record(
                    is_union,
                    tag,
                    Some(ParsedRecordDef {
                        tag,
                        members: Some(members),
                        is_union,
                    }),
                ))],
                init_declarators,
            }
        } else {
            let specifiers = thin_vec![ParsedDeclSpec::TypeSpec(ParsedTypeSpec::Record(is_union, tag, None,))];
            let init_declarators = if parser.accept(TokenKind::Semicolon).is_some() {
                ThinVec::new()
            } else {
                let decls = parse_init_declarators_no_init(parser)?;
                parser.expect(TokenKind::Semicolon)?;
                decls
            };
            ParsedDeclaration {
                specifiers,
                init_declarators,
            }
        }
    } else {
        let specifiers = parse_declaration_specifiers(parser)?;
        let init_declarators = parse_init_declarators_no_init(parser)?;
        parser.expect(TokenKind::Semicolon)?;
        ParsedDeclaration {
            specifiers,
            init_declarators,
        }
    };

    let span = SourceSpan::new(start_loc, parser.previous_token_span().end());
    Ok(parser.push_node(ParsedNodeKind::Declaration(declaration_data), span))
}

fn parse_init_declarators_no_init(parser: &mut Parser) -> Result<ThinVec<ParsedInitDeclarator>, ParseError> {
    let mut decls = ThinVec::new();
    loop {
        let start = parser.current_token_span_or_empty();
        let declarator = super::declarator::parse_declarator(parser)?;
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
