//! Struct and union parsing module
//!
//! This module handles parsing of struct and union declarations,
//! including member declarations and anonymous structs/unions.

use thin_vec::{ThinVec, thin_vec};

use crate::ast::*;
use crate::diagnostic::ParseError;
use crate::lexer::TokenKind;

use super::Parser;

/// Parse struct or union specifier with context
pub fn parse_record_specifier_with_context(
    parser: &mut Parser,
    is_union: bool,
    in_struct_member: bool,
) -> Result<TypeSpecifier, ParseError> {
    // Check for __attribute__ after struct/union keyword (GCC extension)
    if parser.is_token(TokenKind::Attribute)
        && let Err(_e) = super::declaration_core::parse_attribute(parser)
    {
        // For now, ignore attribute parsing errors
    }

    let tag = parser.accept_name();

    // In struct member context, only parse members if we have a specific tag
    // to avoid confusion with anonymous nested structs
    let definition = if parser.accept(TokenKind::LeftBrace).is_some() && (!in_struct_member || tag.is_some()) {
        let members = parse_struct_declaration_list(parser)?;
        parser.expect(TokenKind::RightBrace)?;

        // Check for __attribute__ after struct definition (GCC extension)
        if parser.is_token(TokenKind::Attribute)
            && let Err(_e) = super::declaration_core::parse_attribute(parser)
        {
            // For now, ignore attribute parsing errors
        }

        Some(RecordDefData {
            tag,
            members: Some(members),
            is_union,
        })
    } else {
        None
    };

    Ok(TypeSpecifier::Record(is_union, tag, definition))
}

/// Parse struct declaration list
pub fn parse_struct_declaration_list(parser: &mut Parser) -> Result<Vec<DeclarationData>, ParseError> {
    let mut declarations = Vec::new();

    while !parser.is_token(TokenKind::RightBrace) {
        let declaration = parse_struct_declaration(parser)?;
        declarations.push(declaration);
    }

    Ok(declarations)
}

/// Parse struct declaration
pub fn parse_struct_declaration(parser: &mut Parser) -> Result<DeclarationData, ParseError> {
    // Check if we have an anonymous struct/union
    let is_struct = parser.accept(TokenKind::Struct).is_some();
    let is_union = if !is_struct {
        parser.accept(TokenKind::Union).is_some()
    } else {
        false
    };
    if is_struct || is_union {
        // Check if this is an anonymous struct
        if parser.is_token(TokenKind::LeftBrace) {
            // Anonymous struct definition
            parser.expect(TokenKind::LeftBrace)?;
            let members = parse_struct_declaration_list(parser)?;
            parser.expect(TokenKind::RightBrace)?;

            // After parsing { members }, check the next token
            // If the next token is ';', treat it as an anonymous struct member (no declarator needed)
            // If the next token is an identifier or declarator start, continue with variable declaration parsing
            let init_declarators = if parser.is_token(TokenKind::Semicolon) {
                // Anonymous struct member: struct { members };
                parser.expect(TokenKind::Semicolon)?;
                ThinVec::new()
            } else {
                // Variable declaration with anonymous struct type: struct { members } variable;
                thin_vec![InitDeclarator {
                    declarator: super::declarator::parse_declarator(parser, None)?,
                    initializer: None,
                }]
            };

            let type_specifier = TypeSpecifier::Record(
                is_union,
                None,
                Some(RecordDefData {
                    tag: None,
                    members: Some(members),
                    is_union,
                }),
            );

            let specifiers = thin_vec![DeclSpecifier::TypeSpecifier(type_specifier)];

            // Only expect semicolon if we haven't already consumed it in the anonymous case
            if !init_declarators.is_empty() {
                parser.expect(TokenKind::Semicolon)?;
            }

            Ok(DeclarationData {
                specifiers,
                init_declarators,
            })
        } else {
            // Named struct - read the tag first
            let tag = parser.accept_name();

            // Check if it's defined inline
            if parser.is_token(TokenKind::LeftBrace) {
                // Named struct with definition
                parser.expect(TokenKind::LeftBrace)?;
                let members = parse_struct_declaration_list(parser)?;
                parser.expect(TokenKind::RightBrace)?;

                // After parsing { members }, check the next token
                let init_declarators = if parser.is_token(TokenKind::Semicolon) {
                    // Named struct definition: struct tag { members };
                    parser.expect(TokenKind::Semicolon)?;
                    ThinVec::new()
                } else {
                    // Variable declaration with named struct type: struct tag { members } variable;
                    thin_vec![InitDeclarator {
                        declarator: super::declarator::parse_declarator(parser, None)?,
                        initializer: None,
                    }]
                };

                let type_specifier = TypeSpecifier::Record(
                    is_union,
                    tag,
                    Some(RecordDefData {
                        tag,
                        members: Some(members),
                        is_union,
                    }),
                );

                let specifiers = thin_vec![DeclSpecifier::TypeSpecifier(type_specifier)];

                // Only expect semicolon if we haven't already consumed it
                if !init_declarators.is_empty() {
                    parser.expect(TokenKind::Semicolon)?;
                }

                Ok(DeclarationData {
                    specifiers,
                    init_declarators,
                })
            } else {
                // Just a forward declaration or reference to named struct
                let type_specifier = TypeSpecifier::Record(is_union, tag, None);
                let declarator = super::declarator::parse_declarator(parser, None)?;

                let specifiers = thin_vec![DeclSpecifier::TypeSpecifier(type_specifier)];

                parser.expect(TokenKind::Semicolon)?;

                Ok(DeclarationData {
                    specifiers,
                    init_declarators: thin_vec![InitDeclarator {
                        declarator,
                        initializer: None,
                    }],
                })
            }
        }
    } else {
        // Regular member: type specifier + multiple declarators
        let type_specifier = super::type_specifiers::parse_type_specifier_with_context(parser, true)?;

        let mut init_declarators = ThinVec::new();
        loop {
            let declarator = super::declarator::parse_declarator(parser, None)?;
            init_declarators.push(InitDeclarator {
                declarator,
                initializer: None,
            });

            if parser.accept(TokenKind::Comma).is_none() {
                break;
            }
        }

        let specifiers = thin_vec![DeclSpecifier::TypeSpecifier(type_specifier)];

        parser.expect(TokenKind::Semicolon)?;

        Ok(DeclarationData {
            specifiers,
            init_declarators,
        })
    }
}
