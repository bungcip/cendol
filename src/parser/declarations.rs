//! Declaration parsing module
//!
//! This module handles all declaration parsing logic, including type specifiers,
//! declarators, initializers, and top-level constructs like function definitions
//! and translation units.

use crate::ast::*;
use crate::parser::{ParseError, ParseErrorKind, Token, TokenKind};
use crate::source_manager::{SourceLoc, SourceSpan};
use thin_vec::ThinVec;

use super::Parser;
use crate::ast::parsed::{
    DeclSpec, ParsedAlignmentSpec, ParsedDesignatedInitializer, ParsedDesignator, ParsedNodeKind, ParsedNodeRef,
    TypeSpec,
};
use crate::parser::type_builder::parse_type_name;
use crate::parser::type_specifiers::parse_type_spec;

/// parse declaration or function definition
pub(crate) fn parse_decl(parser: &mut Parser, allow_function_def: bool) -> Result<ParsedNodeRef, ParseError> {
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

    let mut specifiers = parse_decl_specs(trx.parser)?;

    let has_record_enum_type = specifiers
        .iter()
        .any(|s| matches!(s, DeclSpec::TypeSpec(TypeSpec::Record(..) | TypeSpec::Enum(..))));
    let has_storage_class = specifiers.iter().any(|s| matches!(s, DeclSpec::StorageClass(_)));

    if has_record_enum_type
        && !has_storage_class
        && let Some(semi) = trx.parser.accept(TokenKind::Semicolon)
    {
        let decl = ParsedDecl {
            specifiers,
            init_declarators: ThinVec::new(),
        };
        let span = SourceSpan::new(start_loc, semi.span.end());
        let node = trx.parser.push_node(ParsedNodeKind::Declaration(decl), span);
        trx.commit();
        return Ok(node);
    }

    if !trx.parser.is_token(TokenKind::Semicolon)
        && !matches!(
            trx.parser.current_token_kind(),
            Some(TokenKind::Identifier(_)) | Some(TokenKind::Star) | Some(TokenKind::LeftParen)
        )
    {
        let message = if let Some(DeclSpec::TypeSpec(ts)) = specifiers.last() {
            match ts {
                TypeSpec::Record(..) => "Expected ';' after struct/union definition",
                TypeSpec::Enum(..) => "Expected ';' after enum definition",
                _ => "Expected declarator or identifier after type specifier",
            }
        } else {
            "Expected type specifiers"
        };

        let current_token = trx.parser.current_token()?;
        return Err(ParseError {
            span: current_token.span,
            kind: ParseErrorKind::UnexpectedToken {
                expected: message,
                found: current_token.kind,
            },
        });
    }

    let declarator = super::declarator::parse_declarator(trx.parser, false)?;

    if allow_function_def && trx.parser.is_token(TokenKind::LeftBrace) {
        let result = parse_function_definition_tail(trx.parser, specifiers, declarator, start_loc, dummy);
        if result.is_ok() {
            trx.commit();
        }
        return result;
    }

    let mut init_declarators = ThinVec::new();
    let mut current_declarator = Some(declarator);

    loop {
        let start_span = trx.parser.current_token_span_or_empty();
        let declarator = if let Some(d) = current_declarator.take() {
            d
        } else {
            super::declarator::parse_declarator(trx.parser, false)?
        };

        let initializer = if trx.parser.accept(TokenKind::Assign).is_some() {
            Some(super::declarations::parse_initializer(trx.parser)?)
        } else {
            None
        };

        let span = start_span.merge(trx.parser.last_token_span().unwrap_or(start_span));

        if let Some(name) = super::declarator::get_declarator_name(&trx.parser.ast.parsed_types, declarator) {
            if specifiers
                .iter()
                .any(|s| matches!(s, DeclSpec::StorageClass(StorageClass::Typedef)))
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
            let attrs = super::declarations::parse_attribute(trx.parser)?;
            specifiers.extend(attrs);
        } else if trx.parser.is_token(TokenKind::Asm) {
            let _ = super::declarations::parse_asm(trx.parser);
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
                expected: "';' after declaration",
                found: current_token.kind,
            },
        });
    };

    let decl = ParsedDecl {
        specifiers,
        init_declarators,
    };
    let node = trx.parser.replace_node(
        dummy,
        ParsedNodeKind::Declaration(decl),
        SourceSpan::new(start_loc, semi.span.end()),
    );
    trx.commit();
    Ok(node)
}

fn parse_function_definition_tail(
    parser: &mut Parser,
    specifiers: ThinVec<DeclSpec>,
    declarator: DeclaratorRef,
    start_loc: SourceLoc,
    dummy: ParsedNodeRef,
) -> Result<ParsedNodeRef, ParseError> {
    parser.type_context.push_scope();

    if let Some(range) = super::declarator::get_declarator_params(&parser.ast.parsed_types, declarator) {
        for param in parser.ast.parsed_types.get_params(range) {
            if let Some(name) = param.name {
                parser.type_context.add_non_typedef(name);
            }
        }
    }

    let res = super::statements::parse_compound_statement(parser);

    parser.type_context.pop_scope();

    let (body, body_end_loc) = res?;

    let function_def = ParsedFunctionDef {
        specifiers,
        declarator,
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

        if parser.accept(TokenKind::Semicolon).is_some() {
            continue;
        }

        match parse_decl(parser, true) {
            Ok(declaration) => top_level_declarations.push(declaration),
            Err(e) => {
                parser.report_error(e);
                parser.synchronize();
            }
        }
    }

    Ok(parser.replace_node(
        dummy,
        ParsedNodeKind::TranslationUnit(top_level_declarations.into_boxed_slice()),
        SourceSpan::new(start_loc, end_loc),
    ))
}

pub(super) fn parse_static_assert(parser: &mut Parser, start_token: Token) -> Result<ParsedNodeRef, ParseError> {
    let start_loc = start_token.span.start();
    parser.expect(TokenKind::LeftParen)?;
    let condition = parser.parse_expr_assignment()?;

    let message_node = if parser.accept(TokenKind::Comma).is_some() {
        let (lit, span) = parser.expect_string_literal()?;
        Some(parser.push_node(ParsedNodeKind::Literal(lit), span))
    } else {
        if parser.lang_opts.c_standard < crate::lang_options::CStandard::C23 {
            let token = parser.current_token()?;
            return Err(ParseError {
                span: token.span,
                kind: ParseErrorKind::UnexpectedToken {
                    expected: "',' followed by a string literal",
                    found: token.kind,
                },
            });
        }
        None
    };

    parser.expect(TokenKind::RightParen)?;
    let semi = parser.expect(TokenKind::Semicolon)?;
    Ok(parser.push_node(
        ParsedNodeKind::StaticAssert(condition, message_node),
        SourceSpan::new(start_loc, semi.span.end()),
    ))
}

/// Parse declaration specifiers
pub(crate) fn parse_decl_specs(parser: &mut Parser) -> Result<ThinVec<DeclSpec>, ParseError> {
    let mut specifiers = ThinVec::new();
    let mut has_type_specifier = false;

    while let Some(token) = parser.try_current_token() {
        match token.kind {
            TokenKind::Typedef
            | TokenKind::Extern
            | TokenKind::Static
            | TokenKind::Auto
            | TokenKind::Register
            | TokenKind::ThreadLocal
            | TokenKind::Constexpr => {
                let storage_class = token.kind.as_storage_class().unwrap();
                parser.advance();
                specifiers.push(DeclSpec::StorageClass(storage_class));
            }

            TokenKind::Const | TokenKind::Volatile | TokenKind::Restrict | TokenKind::Atomic => {
                if token.kind == TokenKind::Atomic
                    && parser.peek_token(0).is_some_and(|t| t.kind == TokenKind::LeftParen)
                {
                    parser.advance(); // consume `_Atomic`
                    parser.expect(TokenKind::LeftParen)?;
                    let parsed_type = parse_type_name(parser)?;
                    parser.expect(TokenKind::RightParen)?;
                    specifiers.push(DeclSpec::TypeSpec(TypeSpec::Atomic(parsed_type)));
                    has_type_specifier = true;
                    continue;
                }
                let qualifier = token.kind.as_type_qualifier().unwrap();
                parser.advance();
                specifiers.push(DeclSpec::TypeQualifier(qualifier));
            }

            TokenKind::Inline | TokenKind::Noreturn => {
                let func_spec = token.kind.as_function_spec().unwrap();
                parser.advance();
                specifiers.push(DeclSpec::FunctionSpec(func_spec));
            }

            TokenKind::Attribute => {
                let attrs = parse_attribute(parser)?;
                specifiers.extend(attrs);
                specifiers.push(DeclSpec::Attribute);
            }

            TokenKind::LeftBracket if parser.at_c23_attribute_start() => {
                let attrs = parse_c23_attribute(parser)?;
                specifiers.extend(attrs);
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
            | TokenKind::BuiltinVaList
            | TokenKind::Typeof
            | TokenKind::TypeofUnqual
            | TokenKind::AutoType => {
                specifiers.push(DeclSpec::TypeSpec(parse_type_spec(parser)?));
                has_type_specifier = true;
            }

            TokenKind::Identifier(symbol) => {
                if !has_type_specifier && parser.is_type_name(symbol) {
                    specifiers.push(DeclSpec::TypeSpec(parse_type_spec(parser)?));
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
                    let parsed_type = parse_type_name(parser)?;
                    ParsedAlignmentSpec::Type(parsed_type)
                } else {
                    ParsedAlignmentSpec::Expr(parser.parse_expr_min()?)
                };
                parser.expect(TokenKind::RightParen)?;
                specifiers.push(DeclSpec::AlignmentSpec(alignment));
            }

            _ => break,
        }
    }

    if specifiers.is_empty() {
        let current_token = parser.current_token()?;
        return Err(ParseError {
            span: current_token.span,
            kind: ParseErrorKind::UnexpectedToken {
                expected: "declaration specifiers",
                found: current_token.kind,
            },
        });
    }

    Ok(specifiers)
}

/// Parse initializer
pub(super) fn parse_initializer(parser: &mut Parser) -> Result<ParsedNodeRef, ParseError> {
    let span = parser.current_token_span()?;

    if parser.accept(TokenKind::LeftBrace).is_some() {
        let mut initializers = Vec::new();

        while !parser.at_eof() && !parser.is_token(TokenKind::RightBrace) {
            let initializer = if parser.matches(&[TokenKind::Dot, TokenKind::LeftBracket]) {
                parse_designated_initializer(parser)?
            } else {
                let initializer = if parser.is_token(TokenKind::LeftBrace) {
                    parse_initializer(parser)?
                } else {
                    parser.parse_expr_assignment()?
                };

                ParsedDesignatedInitializer {
                    designation: Vec::new().into_boxed_slice(),
                    initializer,
                }
            };

            initializers.push(initializer);
            if parser.accept(TokenKind::Comma).is_none() {
                break;
            }
        }

        let end_token = parser.expect(TokenKind::RightBrace)?;
        let span = SourceSpan::new(span.start(), end_token.span.end());
        Ok(parser.push_node(ParsedNodeKind::InitializerList(initializers.into_boxed_slice()), span))
    } else {
        parser.parse_expr_assignment()
    }
}

/// Parse designated initializer
fn parse_designated_initializer(parser: &mut Parser) -> Result<ParsedDesignatedInitializer, ParseError> {
    let designation = parse_designation(parser)?;

    parser.expect(TokenKind::Assign)?;
    let initializer = parse_initializer(parser)?;

    Ok(ParsedDesignatedInitializer {
        designation,
        initializer,
    })
}

/// Parse designation
fn parse_designation(parser: &mut Parser) -> Result<Box<[ParsedDesignator]>, ParseError> {
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
                designators.push(ParsedDesignator::ArrayRange(start_expr, end_expr));
            } else {
                parser.expect(TokenKind::RightBracket)?;
                designators.push(ParsedDesignator::ArrayIndex(start_expr));
            }
        }
    }

    Ok(designators.into_boxed_slice())
}

/// Parse GCC __attribute__ syntax: __attribute__ (( attribute-list ))
pub(crate) fn parse_attribute(parser: &mut Parser) -> Result<Vec<DeclSpec>, ParseError> {
    parser.expect(TokenKind::Attribute)?;
    parser.expect(TokenKind::LeftParen)?;
    parser.expect(TokenKind::LeftParen)?;

    let mut specs = Vec::new();
    let mut depth = 2;

    while depth > 1 && !parser.at_eof() {
        if parser.accept(TokenKind::Comma).is_some() {
            continue;
        }

        let token = parser.current_token()?;
        match token.kind {
            TokenKind::Identifier(name) => {
                if name == parser.keywords.attr_noreturn || name == parser.keywords.attr_noreturn_underscore {
                    specs.push(DeclSpec::FunctionSpec(crate::ast::FunctionSpec::Noreturn));
                    parser.advance();
                } else if name == parser.keywords.attr_aligned || name == parser.keywords.attr_aligned_underscore {
                    parser.advance();
                    if parser.accept(TokenKind::LeftParen).is_some() {
                        let alignment = if parser.is_type_name_start() {
                            let parsed_type = parse_type_name(parser)?;
                            ParsedAlignmentSpec::Type(parsed_type)
                        } else {
                            ParsedAlignmentSpec::Expr(parser.parse_expr_min()?)
                        };
                        parser.expect(TokenKind::RightParen)?;
                        specs.push(DeclSpec::AlignmentSpec(alignment));
                    }
                } else if name == parser.keywords.attr_packed || name == parser.keywords.attr_packed_underscore {
                    specs.push(DeclSpec::AttributePacked);
                    parser.advance();
                } else {
                    // Skip unknown attribute name and potential arguments
                    parser.advance();
                    if parser.accept(TokenKind::LeftParen).is_some() {
                        let mut inner_depth = 1;
                        while inner_depth > 0 && !parser.at_eof() {
                            if parser.accept(TokenKind::LeftParen).is_some() {
                                inner_depth += 1;
                            } else if parser.accept(TokenKind::RightParen).is_some() {
                                inner_depth -= 1;
                            } else {
                                parser.advance();
                            }
                        }
                    }
                }
            }
            TokenKind::LeftParen => {
                depth += 1;
                parser.advance();
            }
            TokenKind::RightParen => {
                depth -= 1;
                parser.advance();
            }
            _ => {
                parser.advance();
            }
        }
    }

    if depth == 1 {
        parser.expect(TokenKind::RightParen)?;
    }

    Ok(specs)
}

/// Parse C23 attribute syntax: [[ attribute-list ]]
pub(crate) fn parse_c23_attribute(parser: &mut Parser) -> Result<Vec<DeclSpec>, ParseError> {
    parser.expect(TokenKind::LeftBracket)?;
    parser.expect(TokenKind::LeftBracket)?;

    let mut specs = Vec::new();
    while !parser.at_eof() && !parser.is_token(TokenKind::RightBracket) {
        if parser.accept(TokenKind::Comma).is_some() {
            continue;
        }

        if let Some(TokenKind::Identifier(_)) = parser.current_token_kind() {
            parser.advance();

            // Check for scoped attribute prefix ::
            if parser.is_token(TokenKind::Colon) && parser.peek_token(0).is_some_and(|t| t.kind == TokenKind::Colon) {
                parser.advance(); // :
                parser.advance(); // :
                parser.expect_name()?;
            }

            // Check for arguments ( ... )
            if parser.accept(TokenKind::LeftParen).is_some() {
                let mut depth = 1;
                while depth > 0 && !parser.at_eof() {
                    let token = parser.advance().unwrap();
                    if token.kind == TokenKind::LeftParen {
                        depth += 1;
                    } else if token.kind == TokenKind::RightParen {
                        depth -= 1;
                    }
                }
            }
            specs.push(DeclSpec::Attribute);
        } else {
            parser.advance();
        }
    }

    parser.expect(TokenKind::RightBracket)?;
    parser.expect(TokenKind::RightBracket)?;

    Ok(specs)
}

/// Parse GCC __asm__ syntax: __asm__ ( string-literal )
pub(crate) fn parse_asm(parser: &mut Parser) -> Result<(), ParseError> {
    parser.expect(TokenKind::Asm)?;
    parser.expect(TokenKind::LeftParen)?;
    let mut depth = 1;

    while depth > 0 && !parser.at_eof() {
        let token = parser.advance().unwrap();
        if token.kind == TokenKind::LeftParen {
            depth += 1;
        } else if token.kind == TokenKind::RightParen {
            depth -= 1;
        }
    }
    Ok(())
}
