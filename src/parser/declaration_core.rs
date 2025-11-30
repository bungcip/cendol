//! Core declaration parsing module
//!
//! This module handles the main declaration parsing logic, including
//! declaration specifiers, initializers, and coordination between
//! different declaration components.

use crate::ast::*;
use crate::diagnostic::ParseError;
use crate::lexer::TokenKind;
use crate::source_manager::SourceSpan;
use log::debug;
use thin_vec::ThinVec;

use super::Parser;
use super::{BindingPower, parse_expression, unwrap_expr_result};

/// Parse declaration specifiers
pub(crate) fn parse_declaration_specifiers(parser: &mut Parser) -> Result<ThinVec<DeclSpecifier>, ParseError> {
    let mut specifiers = ThinVec::new();
    let mut has_type_specifier = false;
    let start_idx = parser.current_idx;

    debug!(
        "parse_declaration_specifiers: starting at position {}, token {:?}",
        start_idx,
        parser.current_token_kind()
    );

    while let Some(token) = parser.try_current_token() {
        debug!(
            "parse_declaration_specifiers: loop iteration at position {}, token {:?}",
            parser.current_idx, token.kind
        );
        match token.kind {
            // Storage class specifiers
            TokenKind::Typedef
            | TokenKind::Extern
            | TokenKind::Static
            | TokenKind::Auto
            | TokenKind::Register
            | TokenKind::ThreadLocal => {
                let storage_class = match token.kind {
                    TokenKind::Typedef => {
                        debug!("Found Typedef token, setting storage_class Typedef");
                        StorageClass::Typedef
                    }
                    TokenKind::Extern => StorageClass::Extern,
                    TokenKind::Static => StorageClass::Static,
                    TokenKind::Auto => StorageClass::Auto,
                    TokenKind::Register => StorageClass::Register,
                    TokenKind::ThreadLocal => StorageClass::ThreadLocal,
                    _ => unreachable!(),
                };
                parser.advance();
                specifiers.push(DeclSpecifier::StorageClass(storage_class));
            }

            // Type qualifiers
            TokenKind::Const | TokenKind::Volatile | TokenKind::Restrict | TokenKind::Atomic => {
                let mut qualifiers = TypeQualifiers::empty();
                while let Some(token) = parser.try_current_token() {
                    match token.kind {
                        TokenKind::Const => qualifiers.insert(TypeQualifiers::CONST),
                        TokenKind::Volatile => qualifiers.insert(TypeQualifiers::VOLATILE),
                        TokenKind::Restrict => qualifiers.insert(TypeQualifiers::RESTRICT),
                        TokenKind::Atomic => qualifiers.insert(TypeQualifiers::ATOMIC),
                        _ => break,
                    }
                    parser.advance();
                }
                specifiers.push(DeclSpecifier::TypeQualifiers(qualifiers));
            }

            // Function specifiers
            TokenKind::Inline | TokenKind::Noreturn => {
                let mut func_specs = FunctionSpecifiers::empty();
                while let Some(token) = parser.try_current_token() {
                    match token.kind {
                        TokenKind::Inline => func_specs.insert(FunctionSpecifiers::INLINE),
                        TokenKind::Noreturn => func_specs.insert(FunctionSpecifiers::NORETURN),
                        _ => break,
                    }
                    parser.advance();
                }
                specifiers.push(DeclSpecifier::FunctionSpecifiers(func_specs));
            }

            // Type specifiers
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
            | TokenKind::Enum => {
                let type_specifier = super::type_specifiers::parse_type_specifier(parser)?;
                specifiers.push(DeclSpecifier::TypeSpecifier(type_specifier));
                has_type_specifier = true;
            }

            TokenKind::Identifier(symbol) => {
                debug!(
                    "parse_declaration_specifiers: found identifier {:?}, calling is_type_name, current position: {}",
                    symbol, parser.current_idx
                );
                let is_type = parser.is_type_name(symbol);
                debug!(
                    "parse_declaration_specifiers: is_type_name({:?}) = {}, has_type_specifier = {}",
                    symbol, is_type, has_type_specifier
                );
                if is_type && !has_type_specifier {
                    debug!(
                        "parse_declaration_specifiers: {:?} is a type name and no type specifier yet, parsing type specifier",
                        symbol
                    );
                    let type_specifier = super::type_specifiers::parse_type_specifier(parser)?;
                    specifiers.push(DeclSpecifier::TypeSpecifier(type_specifier));
                    has_type_specifier = true;
                } else {
                    debug!(
                        "parse_declaration_specifiers: {:?} is not a type name or already have type specifier, breaking at position {}",
                        symbol, parser.current_idx
                    );
                    break;
                }
            }

            // Alignment specifier
            TokenKind::Alignas => {
                parser.advance(); // consume _Alignas
                let alignment = if parser.accept(TokenKind::LeftParen).is_some() {
                    if parser.matches(&[TokenKind::Identifier(symbol_table::GlobalSymbol::new(""))]) {
                        // _Alignas(type-name)
                        let type_ref = parse_type_name(parser)?;
                        parser.expect(TokenKind::RightParen)?;
                        AlignmentSpecifier::Type(type_ref)
                    } else {
                        // _Alignas(constant-expression)
                        let expr_result = parse_expression(parser, BindingPower::MIN);
                        let expr = unwrap_expr_result(parser, expr_result, "expression in _Alignas")?;
                        parser.expect(TokenKind::RightParen)?;
                        AlignmentSpecifier::Expr(expr)
                    }
                } else {
                    return Err(ParseError::SyntaxError {
                        message: "Expected '(' after _Alignas".to_string(),
                        location: token.location,
                    });
                };

                specifiers.push(DeclSpecifier::AlignmentSpecifier(alignment));
            }

            _ => {
                debug!(
                    "parse_declaration_specifiers: token {:?} not recognized as declaration specifier, breaking",
                    token.kind
                );
                break;
            }
        }
    }

    debug!(
        "parse_declaration_specifiers: ending at position {}, specifiers len={}, found {} specifiers",
        parser.current_idx,
        specifiers.len(),
        specifiers.len()
    );

    if specifiers.is_empty() {
        return Err(ParseError::SyntaxError {
            message: "Expected declaration specifiers".to_string(),
            location: parser.current_token().unwrap().location,
        });
    }

    Ok(specifiers)
}

/// Parse initializer
pub(crate) fn parse_initializer(parser: &mut Parser) -> Result<Initializer, ParseError> {
    debug!(
        "parse_initializer: called at position {}, current token: {:?}",
        parser.current_idx,
        parser.current_token_kind()
    );
    if parser.accept(TokenKind::LeftBrace).is_some() {
        debug!("parse_initializer: found LeftBrace, parsing compound initializer");
        // Compound initializer
        let mut initializers = Vec::new();

        while !parser.matches(&[TokenKind::RightBrace]) {
            // Check if this is a designated initializer (starts with . or [)
            let is_designated = parser.matches(&[TokenKind::Dot]) || parser.matches(&[TokenKind::LeftBracket]);

            let initializer = if is_designated {
                // Parse designated initializer
                parse_designated_initializer(parser)?
            } else {
                // Parse regular initializer (expression or nested compound initializer)
                let expr_or_compound = if parser.matches(&[TokenKind::LeftBrace]) {
                    // Nested compound initializer
                    parse_initializer(parser)?
                } else {
                    // Expression initializer - parse until comma or closing brace
                    let expr_result = parse_initializer_expression(parser)?;
                    Initializer::Expression(expr_result)
                };

                // Wrap in DesignatedInitializer with empty designation
                DesignatedInitializer {
                    designation: Vec::new(),
                    initializer: expr_or_compound,
                }
            };

            initializers.push(initializer);

            if !parser.matches(&[TokenKind::Comma]) {
                break;
            }
            parser.advance(); // consume comma
        }

        parser.expect(TokenKind::RightBrace)?;
        Ok(Initializer::List(initializers))
    } else {
        debug!(
            "parse_initializer: no LeftBrace found, current token: {:?}, trying expression initializer",
            parser.current_token_kind()
        );
        // Expression initializer - use simple parsing to avoid comma operators
        let node = parse_initializer_expression(parser)?;
        Ok(Initializer::Expression(node))
    }
}

/// Parse designated initializer
fn parse_designated_initializer(parser: &mut Parser) -> Result<DesignatedInitializer, ParseError> {
    let designation = if parser.matches(&[TokenKind::Dot]) || parser.matches(&[TokenKind::LeftBracket]) {
        parse_designation(parser)?
    } else {
        Vec::new()
    };

    parser.expect(TokenKind::Assign)?;
    let initializer = parse_initializer(parser)?;

    Ok(DesignatedInitializer {
        designation,
        initializer,
    })
}

/// Parse designation
fn parse_designation(parser: &mut Parser) -> Result<Vec<Designator>, ParseError> {
    let mut designators = Vec::new();

    while parser.matches(&[TokenKind::Dot]) || parser.matches(&[TokenKind::LeftBracket]) {
        if parser.accept(TokenKind::Dot).is_some() {
            let token = parser.try_current_token().ok_or_else(|| ParseError::SyntaxError {
                message: "Expected field name".to_string(),
                location: SourceSpan::empty(),
            })?;

            let field_name = match token.kind {
                TokenKind::Identifier(symbol) => symbol,
                _ => {
                    return Err(ParseError::UnexpectedToken {
                        expected: vec![TokenKind::Identifier(symbol_table::GlobalSymbol::new(""))],
                        found: token.kind,
                        location: token.location,
                    });
                }
            };

            parser.advance().ok_or_else(|| ParseError::SyntaxError {
                message: "Unexpected end of input".to_string(),
                location: SourceSpan::empty(),
            })?;
            designators.push(Designator::FieldName(field_name));
        } else if parser.accept(TokenKind::LeftBracket).is_some() {
            let expr_result = parse_expression(parser, BindingPower::MIN)?;
            let index_expr = match expr_result {
                super::ParseExprOutput::Expression(node) => node,
                _ => {
                    return Err(ParseError::SyntaxError {
                        message: "Expected expression in array designator".to_string(),
                        location: parser.current_token().unwrap().location,
                    });
                }
            };
            parser.expect(TokenKind::RightBracket)?;
            designators.push(Designator::ArrayIndex(index_expr));
        }
    }

    Ok(designators)
}

/// Parse expression for initializer (stops at commas that separate declarators)
fn parse_initializer_expression(parser: &mut Parser) -> Result<NodeRef, ParseError> {
    // Parse expressions in initializers, but stop at comma operators to avoid
    // consuming declarator-separating commas. Use assignment precedence to allow
    // most binary operators but prevent comma operators.
    let expr_result = parse_expression(parser, BindingPower::ASSIGNMENT)?;
    match expr_result {
        super::ParseExprOutput::Expression(node) => Ok(node),
        _ => Err(ParseError::SyntaxError {
            message: "Expected expression in initializer".to_string(),
            location: parser.current_token().unwrap().location,
        }),
    }
}

/// Parse type name (for casts, sizeof, etc.)
pub(crate) fn parse_type_name(parser: &mut Parser) -> Result<TypeRef, ParseError> {
    // Parse declaration specifiers
    let _specifiers = parse_declaration_specifiers(parser)?;

    // Parse abstract declarator (optional)
    let _declarator = if parser.is_abstract_declarator_start() {
        Some(super::declarator::parse_abstract_declarator(parser)?)
    } else {
        None
    };

    // Build the type from specifiers and declarator
    // TODO: Implement proper type construction from specifiers and declarator
    Ok(parser.ast.push_type(Type {
        kind: TypeKind::Void,
        qualifiers: TypeQualifiers::empty(),
        size: None,
        alignment: None,
    }))
}
