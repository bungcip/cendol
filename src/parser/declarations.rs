//! Declaration parsing module
//!
//! This module handles all declaration parsing logic, including type specifiers,
//! declarators, initializers, and top-level constructs like function definitions
//! and translation units.

use crate::ast::literal::Literal;
use crate::ast::{parsed::*, *};
use crate::diagnostic::{ParseError, ParseErrorKind};
use crate::parser::declaration_core::parse_declaration_specifiers;
use crate::parser::{Token, TokenKind};
use crate::source_manager::{SourceLoc, SourceSpan};
use thin_vec::ThinVec;

use super::Parser;

pub(crate) fn parse_declaration(parser: &mut Parser) -> Result<ParsedNodeRef, ParseError> {
    let trx = parser.start_transaction();
    let start_loc = trx.parser.current_token_span()?.start();
    let dummy = trx.parser.push_dummy();

    if let Some(token) = trx.parser.accept(TokenKind::StaticAssert) {
        let result = parse_static_assert(trx.parser, token);
        if result.is_ok() {
            trx.commit();
        }
        return result;
    }

    let mut specifiers = parse_declaration_specifiers(trx.parser)?;

    let has_record_enum_type = specifiers.iter().any(|s| {
        matches!(
            s,
            ParsedDeclSpecifier::TypeSpecifier(ParsedTypeSpecifier::Record(_, _, _) | ParsedTypeSpecifier::Enum(_, _))
        )
    });
    let has_storage_class = specifiers
        .iter()
        .any(|s| matches!(s, ParsedDeclSpecifier::StorageClass(_)));

    if has_record_enum_type
        && !has_storage_class
        && let Some(semi) = trx.parser.accept(TokenKind::Semicolon)
    {
        let declaration_data = ParsedDeclarationData {
            specifiers,
            init_declarators: ThinVec::new(),
        };
        let span = SourceSpan::new(start_loc, semi.span.end());
        let node = trx
            .parser
            .push_node(ParsedNodeKind::Declaration(declaration_data), span);
        trx.commit();
        return Ok(node);
    }

    if !trx.parser.is_token(TokenKind::Semicolon)
        && !matches!(
            trx.parser.current_token_kind(),
            Some(TokenKind::Identifier(_)) | Some(TokenKind::Star) | Some(TokenKind::LeftParen)
        )
    {
        let message = if let Some(ParsedDeclSpecifier::TypeSpecifier(ts)) = specifiers.last() {
            match ts {
                ParsedTypeSpecifier::Record(_, _, _) => "Expected ';' after struct/union definition",
                ParsedTypeSpecifier::Enum(_, _) => "Expected ';' after enum definition",
                _ => "Expected declarator or identifier after type specifier",
            }
        } else {
            "Expected type specifiers"
        };

        let current_token = trx.parser.current_token()?;
        return Err(ParseError {
            span: current_token.span,
            kind: ParseErrorKind::UnexpectedToken {
                expected_tokens: message.to_string(),
                found: current_token.kind,
            },
        });
    }

    let mut init_declarators = ThinVec::new();
    loop {
        let start_span = trx.parser.current_token_span_or_empty();
        let declarator = super::declarator::parse_declarator(trx.parser)?;

        let initializer = if trx.parser.accept(TokenKind::Assign).is_some() {
            Some(super::declaration_core::parse_initializer(trx.parser)?)
        } else {
            None
        };

        let span = start_span.merge(trx.parser.last_token_span().unwrap_or(start_span));

        if let Some(name) = trx.parser.get_declarator_name(&declarator) {
            if specifiers
                .iter()
                .any(|s| matches!(s, ParsedDeclSpecifier::StorageClass(StorageClass::Typedef)))
            {
                trx.parser.add_typedef(name);
            } else {
                trx.parser.type_context.add_non_typedef(name);
            }
        }

        init_declarators.push(ParsedInitDeclarator {
            declarator,
            initializer,
            span,
        });

        if !trx.parser.is_token(TokenKind::Comma) {
            break;
        }
        trx.parser.advance();
    }

    loop {
        if trx.parser.is_token(TokenKind::Attribute) {
            let attrs = super::declaration_core::parse_attribute(trx.parser)?;
            specifiers.extend(attrs);
        } else if trx.parser.is_token(TokenKind::Asm) {
            let _ = super::declaration_core::parse_asm(trx.parser);
        } else {
            break;
        }
    }

    let semi = if let Some(token) = trx.parser.accept(TokenKind::Semicolon) {
        token
    } else {
        let current_token = trx.parser.current_token()?;
        return Err(ParseError {
            span: current_token.span,
            kind: ParseErrorKind::UnexpectedToken {
                expected_tokens: "';' after declaration".to_string(),
                found: current_token.kind,
            },
        });
    };

    let declaration_data = ParsedDeclarationData {
        specifiers,
        init_declarators,
    };
    let node = trx.parser.replace_node(
        dummy,
        ParsedNodeKind::Declaration(declaration_data),
        SourceSpan::new(start_loc, semi.span.end()),
    );
    trx.commit();
    Ok(node)
}

fn parse_function_definition(parser: &mut Parser) -> Result<ParsedNodeRef, ParseError> {
    let start_loc = parser.current_token()?.span.start();
    let dummy = parser.push_dummy();

    let specifiers = parse_declaration_specifiers(parser)?;
    let declarator = super::declarator::parse_declarator(parser)?;

    parser.type_context.push_scope();

    if let Some(params) = super::declarator::get_declarator_params(&declarator) {
        for param in params {
            if let Some(ref decl) = param.declarator
                && let Some(name) = super::declarator::get_declarator_name(decl)
            {
                parser.type_context.add_non_typedef(name);
            }
        }
    }

    let res = super::statements::parse_compound_statement(parser);

    parser.type_context.pop_scope();

    let (body, body_end_loc) = res?;

    let function_def = ParsedFunctionDefData {
        specifiers,
        declarator: Box::new(declarator),
        body,
    };

    Ok(parser.replace_node(
        dummy,
        ParsedNodeKind::FunctionDef(function_def),
        SourceSpan::new(start_loc, body_end_loc),
    ))
}

pub(crate) fn parse_translation_unit(parser: &mut Parser) -> Result<ParsedNodeRef, ParseError> {
    let start_loc = parser.current_token()?.span.start();
    let mut end_loc = SourceLoc::builtin();
    let mut top_level_declarations = Vec::new();

    let dummy = parser.push_dummy();

    while let Some(token) = parser.try_current_token() {
        if token.kind == TokenKind::EndOfFile {
            end_loc = token.span.end();
            break;
        }

        if let TokenKind::PragmaPack(kind) = token.kind {
            let node = parser.push_node(ParsedNodeKind::PragmaPack(kind), token.span);
            top_level_declarations.push(node);
            parser.advance();
            continue;
        }

        let initial_idx = parser.current_idx;
        match parse_declaration(parser) {
            Ok(declaration) => top_level_declarations.push(declaration),
            Err(_) => {
                parser.current_idx = initial_idx;
                match parse_function_definition(parser) {
                    Ok(func_def) => top_level_declarations.push(func_def),
                    Err(e) => {
                        parser.diag.report(e);
                        parser.synchronize();
                    }
                }
            }
        }
    }

    Ok(parser.replace_node(
        dummy,
        ParsedNodeKind::TranslationUnit(top_level_declarations),
        SourceSpan::new(start_loc, end_loc),
    ))
}

pub(super) fn parse_static_assert(parser: &mut Parser, start_token: Token) -> Result<ParsedNodeRef, ParseError> {
    let start_loc = start_token.span.start();
    parser.expect(TokenKind::LeftParen)?;
    let condition = parser.parse_expr_assignment()?;
    parser.expect(TokenKind::Comma)?;

    let token = parser.current_token()?;
    let message_node = match token.kind {
        TokenKind::StringLiteral(symbol) => {
            parser.advance();
            parser.push_node(ParsedNodeKind::Literal(Literal::String(symbol)), token.span)
        }
        _ => {
            return Err(ParseError {
                span: token.span,
                kind: ParseErrorKind::UnexpectedToken {
                    expected_tokens: "string literal".to_string(),
                    found: token.kind,
                },
            });
        }
    };

    parser.expect(TokenKind::RightParen)?;
    let semi = parser.expect(TokenKind::Semicolon)?;
    Ok(parser.push_node(
        ParsedNodeKind::StaticAssert(condition, message_node),
        SourceSpan::new(start_loc, semi.span.end()),
    ))
}
