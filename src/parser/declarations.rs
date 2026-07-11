//! Declaration parsing module
//!
//! This module handles all declaration parsing logic, including type specifiers,
//! declarators, initializers, and top-level constructs like function definitions
//! and translation units.

use crate::ast::*;
use crate::parser::{ParseDiag, ParseError, Token, TokenKind};
use crate::semantic::ScopeId;
use crate::source_manager::{SourceLoc, SourceSpan};
use thin_vec::ThinVec;

use super::Parser;
use crate::ast::parsed::{
    DeclSpec, ParsedAlignmentSpec, ParsedDesignatedInitializer, ParsedDesignator, ParsedNodeKind, ParsedNodeRef,
    TypeSpec,
};
use crate::parser::type_builder::parse_type_name;
use crate::parser::type_specifiers::parse_type_spec;
use crate::parser::utils::parse_comma_separated_list;

/// parse declaration or function definition
pub(crate) fn parse_decl(parser: &mut Parser, allow_function_def: bool) -> Result<ParsedNodeRef, ParseDiag> {
    parser.transaction(|p| {
        let start_loc = p.current_token_span()?.start();
        let dummy = p.push_dummy();

        if let Some(token) = p.accept(TokenKind::StaticAssert) {
            return parse_static_assert(p, token);
        }

        let mut specifiers = parse_decl_specs(p)?;

        let has_record_enum_type = specifiers
            .iter()
            .any(|s| matches!(s, DeclSpec::TypeSpec(TypeSpec::Record(..) | TypeSpec::Enum(..))));
        let has_storage_class = specifiers.iter().any(|s| matches!(s, DeclSpec::StorageClass(_)));

        if has_record_enum_type
            && !has_storage_class
            && let Some(semi) = p.accept(TokenKind::Semicolon)
        {
            let decl = ParsedDecl {
                specifiers,
                init_declarators: ThinVec::new(),
            };
            let span = SourceSpan::new(start_loc, semi.span.end());
            return Ok(p.push_node(ParsedNodeKind::Declaration(decl), span));
        }

        if !p.is_token(TokenKind::Semicolon)
            && !matches!(
                p.current_token_kind(),
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

            let current_token = p.current_token()?;
            return Err(ParseDiag {
                span: current_token.span,
                kind: ParseError::UnexpectedToken {
                    expected: message,
                    found: current_token.kind,
                },
            });
        }

        let declarator = super::declarator::parse_declarator(p, false)?;

        if allow_function_def && p.is_token(TokenKind::LeftBrace) {
            return parse_function_definition_tail(p, specifiers, declarator, start_loc, dummy);
        }

        let mut init_declarators = ThinVec::new();
        let mut current_declarator = Some(declarator);

        loop {
            let start_span = p.current_token_span_or_empty();
            let declarator = if let Some(d) = current_declarator.take() {
                d
            } else {
                super::declarator::parse_declarator(p, false)?
            };

            let initializer = if p.accept(TokenKind::Assign).is_some() {
                Some(super::declarations::parse_initializer(p)?)
            } else {
                None
            };

            let span = start_span.merge(p.last_token_span().unwrap_or(start_span));

            if let Some(name) = super::declarator::get_declarator_name(&p.ast.parsed_types, declarator) {
                if specifiers
                    .iter()
                    .any(|s| matches!(s, DeclSpec::StorageClass(StorageClass::Typedef)))
                {
                    p.add_typedef(name);
                } else {
                    p.symbol_table.define_parser_non_typedef(name, span);
                }
            }

            init_declarators.push(ParsedInitDeclarator {
                declarator,
                initializer,
                span,
            });

            if !p.is_token(TokenKind::Comma) {
                break;
            }
            p.advance();
        }

        parse_trailing_attributes_and_asm(p, &mut specifiers)?;

        let semi = if let Some(token) = p.accept(TokenKind::Semicolon) {
            token
        } else {
            let current_token = p.current_token()?;
            return Err(ParseDiag {
                span: current_token.span,
                kind: ParseError::UnexpectedToken {
                    expected: "';' after declaration",
                    found: current_token.kind,
                },
            });
        };

        let decl = ParsedDecl {
            specifiers,
            init_declarators,
        };
        Ok(p.replace_node(
            dummy,
            ParsedNodeKind::Declaration(decl),
            SourceSpan::new(start_loc, semi.span.end()),
        ))
    })
}

fn parse_function_definition_tail(
    parser: &mut Parser,
    specifiers: ThinVec<DeclSpec>,
    declarator: DeclaratorRef,
    start_loc: SourceLoc,
    dummy: ParsedNodeRef,
) -> Result<ParsedNodeRef, ParseDiag> {
    let scope_id = parser
        .ast
        .parsed_types
        .get_declarator_scope(declarator)
        .unwrap_or(ScopeId::GLOBAL);
    let old_scope = parser.symbol_table.current_scope();
    parser.symbol_table.set_current_scope(scope_id);
    parser.next_compound_uses_scope = Some(scope_id);

    let res = super::statements::parse_compound_statement(parser);

    parser.symbol_table.set_current_scope(old_scope);

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

pub(crate) fn parse_translation_unit(parser: &mut Parser) -> Result<ParsedNodeRef, ParseDiag> {
    let mut span = parser.current_token()?.span;
    let mut top_level_declarations = Vec::new();

    let dummy = parser.push_dummy();

    while let Some(token) = parser.try_current_token() {
        if token.kind == TokenKind::EndOfFile {
            span = span.merge(token.span);
            break;
        }

        if let TokenKind::PragmaPack(kind) = token.kind {
            let node = parser.push_node(ParsedNodeKind::PragmaPack(kind), token.span);
            top_level_declarations.push(node);
            parser.advance();
            continue;
        }

        if let TokenKind::PragmaVisibility(kind) = token.kind {
            let node = parser.push_node(ParsedNodeKind::PragmaVisibility(kind), token.span);
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
        span,
    ))
}

pub(super) fn parse_static_assert(parser: &mut Parser, start_token: Token) -> Result<ParsedNodeRef, ParseDiag> {
    let start = start_token.span;
    parser.expect(TokenKind::LeftParen)?;
    let condition = parser.parse_expr_assignment()?;

    let message_node = if parser.accept(TokenKind::Comma).is_some() {
        let (lit, span) = parser.expect_string_literal()?;
        Some(parser.push_node(ParsedNodeKind::Literal(lit), span))
    } else {
        // We allow single-argument _Static_assert as an extension in < C23
        None
    };

    parser.expect(TokenKind::RightParen)?;
    let semi = parser.expect(TokenKind::Semicolon)?;
    Ok(parser.push_node(
        ParsedNodeKind::StaticAssert(condition, message_node),
        start.merge(semi.span),
    ))
}

/// Parse declaration specifiers
pub(crate) fn parse_decl_specs(parser: &mut Parser) -> Result<ThinVec<DeclSpec>, ParseDiag> {
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
                specifiers.push(DeclSpec::AlignmentSpec(alignment, false));
            }

            _ => break,
        }
    }

    if specifiers.is_empty() {
        let current_token = parser.current_token()?;
        return Err(ParseDiag {
            span: current_token.span,
            kind: ParseError::UnexpectedToken {
                expected: "declaration specifiers",
                found: current_token.kind,
            },
        });
    }

    Ok(specifiers)
}

/// Parse initializer
pub(super) fn parse_initializer(parser: &mut Parser) -> Result<ParsedNodeRef, ParseDiag> {
    if let Some(token) = parser.accept(TokenKind::LeftBrace) {
        let initializers = parse_comma_separated_list(parser, TokenKind::RightBrace, |parser| {
            if parser.matches(&[TokenKind::Dot, TokenKind::LeftBracket]) {
                parse_designated_initializer(parser)
            } else {
                let initializer = if parser.is_token(TokenKind::LeftBrace) {
                    parse_initializer(parser)?
                } else {
                    parser.parse_expr_assignment()?
                };

                Ok(ParsedDesignatedInitializer {
                    designation: Vec::new().into_boxed_slice(),
                    initializer,
                })
            }
        })?;

        let end_token = parser.expect(TokenKind::RightBrace)?;
        let span = token.span.merge(end_token.span);
        Ok(parser.push_node(ParsedNodeKind::InitializerList(initializers.into_boxed_slice()), span))
    } else {
        parser.parse_expr_assignment()
    }
}

/// Parse designated initializer
fn parse_designated_initializer(parser: &mut Parser) -> Result<ParsedDesignatedInitializer, ParseDiag> {
    let designation = parse_designation(parser)?;

    parser.expect(TokenKind::Assign)?;
    let initializer = parse_initializer(parser)?;

    Ok(ParsedDesignatedInitializer {
        designation,
        initializer,
    })
}

/// Parse designation
fn parse_designation(parser: &mut Parser) -> Result<Box<[ParsedDesignator]>, ParseDiag> {
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
pub(crate) fn parse_attribute(parser: &mut Parser) -> Result<Vec<DeclSpec>, ParseDiag> {
    parser.expect(TokenKind::Attribute)?;

    parser.expect(TokenKind::LeftParen)?;
    parser.expect(TokenKind::LeftParen)?;
    let mut depth = 2;

    let mut specs = Vec::new();
    while depth > 1 && !parser.at_eof() {
        if parser.accept(TokenKind::Comma).is_some() {
            continue;
        }

        let token = parser.current_token()?;
        match token.kind {
            TokenKind::Identifier(name) => {
                // Inside __attribute__((...)), noreturn is just an attribute name (not a function specifier).
                // GCC uses __attribute__((noreturn)) on function types, but on other types it's ignored.
                if name == parser.keywords.attr_noreturn || name == parser.keywords.attr_noreturn_underscore {
                    // Skip noreturn as an attribute - it's only valid on function types
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
                        specs.push(DeclSpec::AlignmentSpec(alignment, true));
                    }
                } else if name == parser.keywords.attr_packed || name == parser.keywords.attr_packed_underscore {
                    specs.push(DeclSpec::AttributePacked);
                    parser.advance();
                } else if name == parser.keywords.attr_transparent_union
                    || name == parser.keywords.attr_transparent_union_underscore
                {
                    specs.push(DeclSpec::AttributeTransparentUnion);
                    parser.advance();
                } else if name == parser.keywords.attr_cleanup || name == parser.keywords.attr_cleanup_underscore {
                    parser.advance();
                    parser.expect(TokenKind::LeftParen)?;
                    let arg = parser.parse_expr_assignment()?;
                    parser.expect(TokenKind::RightParen)?;
                    specs.push(DeclSpec::AttributeCleanup(arg));
                } else if name == parser.keywords.attr_visibility || name == parser.keywords.attr_visibility_underscore
                {
                    parser.advance();
                    parser.expect(TokenKind::LeftParen)?;
                    let (lit, _span) = parser.expect_string_literal()?;
                    let val = match lit.get_val() {
                        crate::ast::literal::LitVal::String { value, .. } => value,
                        _ => String::new(),
                    };
                    parser.expect(TokenKind::RightParen)?;
                    let vis = match val.as_str() {
                        "default" => crate::lang_options::Visibility::Default,
                        "hidden" => crate::lang_options::Visibility::Hidden,
                        "protected" => crate::lang_options::Visibility::Protected,
                        "internal" => crate::lang_options::Visibility::Internal,
                        _ => crate::lang_options::Visibility::Default,
                    };
                    specs.push(DeclSpec::AttributeVisibility(vis));
                } else if name == parser.keywords.attr_alias || name == parser.keywords.attr_alias_underscore {
                    parser.advance();
                    parser.expect(TokenKind::LeftParen)?;
                    let (lit, _span) = parser.expect_string_literal()?;
                    parser.expect(TokenKind::RightParen)?;
                    specs.push(DeclSpec::AttributeAlias(lit));
                } else if name == parser.keywords.attr_mode || name == parser.keywords.attr_mode_underscore {
                    parser.advance();
                    parser.expect(TokenKind::LeftParen)?;
                    let token = parser.current_token()?;
                    if let TokenKind::Identifier(mode_name) = token.kind {
                        parser.advance();
                        specs.push(DeclSpec::AttributeMode(mode_name));
                    } else {
                        // Skip if it's not an identifier (e.g., error case)
                        parser.advance();
                    }
                    parser.expect(TokenKind::RightParen)?;
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
            TokenKind::Noreturn => {
                // Inside __attribute__((...)), __noreturn__ is an attribute name,
                // not a function specifier. Just skip it.
                parser.advance();
            }
            TokenKind::Attribute => {
                // Handle nested __attribute__ in attribute list
                // These get collected and skipped
                let nested = parse_attribute(parser)?;
                specs.extend(nested);
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
pub(crate) fn parse_c23_attribute(parser: &mut Parser) -> Result<Vec<DeclSpec>, ParseDiag> {
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
pub(crate) fn parse_asm(parser: &mut Parser) -> Result<Option<crate::ast::literal::LitRef>, ParseDiag> {
    parser.expect(TokenKind::Asm)?;
    parser.expect(TokenKind::LeftParen)?;
    let mut lit_out = None;
    if let Ok(token) = parser.current_token()
        && let TokenKind::Literal(lit) = token.kind
        && lit.kind() == crate::ast::literal::LitKind::String
    {
        let (lit_val, _) = parser.expect_string_literal()?;
        lit_out = Some(lit_val);
    }
    let mut depth = 1;

    while depth > 0 && !parser.at_eof() {
        let token = parser.advance().unwrap();
        if token.kind == TokenKind::LeftParen {
            depth += 1;
        } else if token.kind == TokenKind::RightParen {
            depth -= 1;
        }
    }
    Ok(lit_out)
}

pub(crate) fn parse_trailing_attributes_and_asm(
    parser: &mut Parser,
    specifiers: &mut ThinVec<DeclSpec>,
) -> Result<(), ParseDiag> {
    loop {
        if parser.is_token(TokenKind::Attribute) {
            specifiers.extend(parse_attribute(parser)?);
        } else if parser.at_c23_attribute_start() {
            specifiers.extend(parse_c23_attribute(parser)?);
        } else if parser.is_token(TokenKind::Asm) {
            if let Some(lit) = parse_asm(parser)? {
                specifiers.push(DeclSpec::AttributeAsm(lit));
            }
        } else {
            break;
        }
    }
    Ok(())
}
