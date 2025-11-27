//! Declaration parsing module
//!
//! This module handles all declaration parsing logic, including type specifiers,
//! declarators, initializers, and top-level constructs like function definitions
//! and translation units.

use crate::ast::*;
use crate::diagnostic::ParseError;
use crate::lexer::{Token, TokenKind};
use crate::source_manager::{SourceLoc, SourceSpan};
use log::debug;
use std::cell::Cell;
use symbol_table::GlobalSymbol as Symbol;

use super::Parser;

/// Parse a declaration
pub fn parse_declaration(parser: &mut Parser) -> Result<NodeRef, ParseError> {
    let start_span = parser.current_token()?.location.start;
    let initial_idx = parser.current_idx; // Save initial position for potential rollback
    let saved_diagnostic_count = parser.diag.diagnostics.len();

    debug!(
        "parse_declaration: starting at position {}, token {:?}",
        initial_idx,
        parser.current_token_kind()
    );

    // Check for _Static_assert (C11)
    if let Some(token) = parser.accept(TokenKind::StaticAssert) {
        return parse_static_assert(parser, token);
    }

    // Try to parse declaration specifiers
    let specifiers = match parse_declaration_specifiers(parser) {
        Ok(specifiers) => {
            debug!(
                "parse_declaration: parsed {} specifiers, current token {:?}",
                specifiers.len(),
                parser.current_token_kind()
            );
            debug!(
                "parse_declaration: current token after specifiers: {:?}",
                parser.current_token_kind()
            );
            if let Some(last_specifier) = specifiers.last() {
                debug!(
                    "parse_declaration: last specifier type: {:?}",
                    std::mem::discriminant(&last_specifier.type_specifier)
                );
            }
            specifiers
        }
        Err(e) => {
            // If declaration specifiers parsing fails, roll back completely
            parser.current_idx = initial_idx;
            parser.diag.diagnostics.truncate(saved_diagnostic_count);
            debug!(
                "parse_declaration: specifier parsing failed, rolled back to {}",
                initial_idx
            );
            return Err(e);
        }
    };

    // Special handling for struct/union/enum declarations
    // Check if any specifier is a struct/union/enum specifier (definition or forward declaration)
    let is_record_enum_specifier = specifiers.iter().any(|s| matches!(&s.type_specifier, TypeSpecifier::Record(_, _, _) | TypeSpecifier::Enum(_, _)) && s.storage_class.is_none());

    // If we have a struct/union/enum specifier, we need to check if there are declarators following
    // The logic should be:
    // - If next token is semicolon: treat as record/enum declaration (definition or forward)
    // - If next token is declarator-starting token: continue with normal declaration parsing
    if is_record_enum_specifier {
        if parser.matches(&[TokenKind::Semicolon]) {
            // This is either:
            // 1. A pure struct/union/enum definition like "struct foo { ... };" or "enum E { ... };"
            // 2. A forward struct/union/enum declaration like "struct foo;" or "enum E;"
            // In both cases, consume the semicolon and create declaration with no declarators
            parser.expect(TokenKind::Semicolon)?;

            let declaration_data = DeclarationData {
                specifiers,
                init_declarators: Vec::new(),
            };

            let end_span = parser.current_token()?.location.end;
            let span = SourceSpan::new(start_span, end_span);

            let node = parser
                .ast
                .push_node(Node::new(NodeKind::Declaration(declaration_data), span));
            debug!(
                "parse_declaration: successfully parsed record/enum declaration, node_id={}",
                node.get()
            );
            return Ok(node);
        } else {
            // This is a record/enum specifier with declarators
            // Continue with normal declaration parsing (e.g., "struct foo { ... } var;")
            debug!(
                "parse_declaration: record/enum specifier with declarators, continuing with normal parsing"
            );
        }
    }

    // For all other cases, check if we have declarators
    let has_declarators = if parser.matches(&[TokenKind::Semicolon]) {
        // Definitely no declarators
        false
    } else {
        // Check if we have a declarator-starting token
        // This includes: identifier, star, or left paren
        matches!(
            parser.current_token_kind(),
            Some(TokenKind::Identifier(_)) | Some(TokenKind::Star) | Some(TokenKind::LeftParen)
        )
    };
    debug!("parse_declaration: has_declarators = {}", has_declarators);

    // If no declarators and this is not a record/enum definition, it's an error
    if !has_declarators {
        // Check if this looks like a record/enum definition
        // by looking at the last parsed specifier
        if let Some(last_specifier) = specifiers.last() {
            match &last_specifier.type_specifier {
                TypeSpecifier::Record(_, _tag, _definition) => {
                    // This should not happen due to the check above, but just in case
                    parser.current_idx = initial_idx;
                    parser.diag.diagnostics.truncate(saved_diagnostic_count);
                    debug!(
                        "parse_declaration: record definition with no declarators and no semicolon, rolled back to {}",
                        initial_idx
                    );
                    return Err(ParseError::SyntaxError {
                        message: "Expected ';' after struct/union definition".to_string(),
                        location: parser.current_token()?.location,
                    });
                }
                TypeSpecifier::Enum(_tag, _definition) => {
                    // This should not happen due to the check above, but just in case
                    parser.current_idx = initial_idx;
                    parser.diag.diagnostics.truncate(saved_diagnostic_count);
                    debug!(
                        "parse_declaration: enum definition with no declarators and no semicolon, rolled back to {}",
                        initial_idx
                    );
                    return Err(ParseError::SyntaxError {
                        message: "Expected ';' after enum definition".to_string(),
                        location: parser.current_token()?.location,
                    });
                }
                _ => {
                    // Not a record/enum definition, this is likely an error
                    // But let's rollback and let the statement parser handle it
                    parser.current_idx = initial_idx;
                    parser.diag.diagnostics.truncate(saved_diagnostic_count);
                    debug!(
                        "parse_declaration: no declarators found, rolled back to {}",
                        initial_idx
                    );
                    return Err(ParseError::SyntaxError {
                        message: "Expected declarator or identifier after type specifier"
                            .to_string(),
                        location: parser.current_token()?.location,
                    });
                }
            }
        } else {
            // No specifiers at all - this shouldn't happen
            parser.current_idx = initial_idx;
            parser.diag.diagnostics.truncate(saved_diagnostic_count);
            debug!(
                "parse_declaration: no specifiers, rolled back to {}",
                initial_idx
            );
            return Err(ParseError::SyntaxError {
                message: "Expected type specifiers".to_string(),
                location: parser.current_token()?.location,
            });
        }
    }

    // Parse init declarators
    let mut init_declarators = Vec::new();

    loop {
        let declarator_start_idx = parser.current_idx;
        debug!(
            "parse_declaration: parsing declarator at position {}, token {:?}",
            declarator_start_idx,
            parser.current_token_kind()
        );

        let declarator = match super::declarator::parse_declarator(parser, None) {
            Ok(declarator) => {
                debug!(
                    "parse_declaration: parsed declarator, current token {:?}",
                    parser.current_token_kind()
                );
                declarator
            }
            Err(e) => {
                // If declarator parsing fails, roll back completely
                parser.current_idx = initial_idx;
                parser.diag.diagnostics.truncate(saved_diagnostic_count);
                debug!(
                    "parse_declaration: declarator parsing failed, rolled back to {}",
                    initial_idx
                );
                return Err(e);
            }
        };

        let _initializer_start_idx = parser.current_idx;
        let initializer = if parser.matches(&[TokenKind::Assign]) {
            parser.advance(); // consume '='
            debug!(
                "parse_declaration: found '=', parsing initializer at position {}",
                parser.current_idx
            );
            match parse_initializer(parser) {
                Ok(initializer) => {
                    debug!(
                        "parse_declaration: parsed initializer, now at position {} with token {:?}",
                        parser.current_idx,
                        parser.current_token_kind()
                    );
                    Some(initializer)
                }
                Err(e) => {
                    // If initializer parsing fails, roll back completely
                    parser.current_idx = initial_idx;
                    parser.diag.diagnostics.truncate(saved_diagnostic_count);
                    debug!(
                        "parse_declaration: initializer parsing failed, rolled back to {}",
                        initial_idx
                    );
                    return Err(e);
                }
            }
        } else {
            None
        };

        init_declarators.push(InitDeclarator {
            declarator,
            initializer,
        });

        if !parser.matches(&[TokenKind::Comma]) {
            break;
        }
        parser.advance(); // consume comma
    }

    // Check for semicolon at current position
    debug!(
        "parse_declaration: expecting semicolon, current token {:?}",
        parser.current_token_kind()
    );
    let semicolon_token = if parser.matches(&[TokenKind::Semicolon]) {
        parser.advance().ok_or_else(|| ParseError::SyntaxError {
            message: "Unexpected end of input".to_string(),
            location: SourceSpan::empty(),
        })?
    } else {
        // If semicolon is missing, roll back completely
        parser.current_idx = initial_idx;
        parser.diag.diagnostics.truncate(saved_diagnostic_count);
        debug!(
            "parse_declaration: missing semicolon, rolled back to {}",
            initial_idx
        );
        return Err(ParseError::SyntaxError {
            message: "Expected ';' after declaration".to_string(),
            location: parser.current_token()?.location,
        });
    };

    let end_span = semicolon_token.location.end;

    let span = SourceSpan::new(start_span, end_span);

    // Track typedef names for disambiguation
    for specifier in &specifiers {
        if specifier.storage_class == Some(StorageClass::Typedef) {
            for init_declarator in &init_declarators {
                if let Some(name) = parser.get_declarator_name(&init_declarator.declarator) {
                    parser.add_typedef(name);
                }
            }
        }
    }

    let declaration_data = DeclarationData {
        specifiers,
        init_declarators,
    };

    let node = parser
        .ast
        .push_node(Node::new(NodeKind::Declaration(declaration_data), span));
    debug!(
        "parse_declaration: successfully parsed declaration, node_id={}",
        node.get()
    );
    Ok(node)
}

/// Parse declaration specifiers
pub fn parse_declaration_specifiers(parser: &mut Parser) -> Result<Vec<DeclSpecifier>, ParseError> {
    let mut specifiers = Vec::new();
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
                    TokenKind::Typedef => StorageClass::Typedef,
                    TokenKind::Extern => StorageClass::Extern,
                    TokenKind::Static => StorageClass::Static,
                    TokenKind::Auto => StorageClass::Auto,
                    TokenKind::Register => StorageClass::Register,
                    TokenKind::ThreadLocal => StorageClass::ThreadLocal,
                    _ => unreachable!(),
                };
                parser.advance();
                specifiers.push(DeclSpecifier {
                    storage_class: Some(storage_class),
                    type_qualifiers: TypeQualifiers::empty(),
                    function_specifiers: FunctionSpecifiers::empty(),
                    alignment_specifier: None,
                    type_specifier: TypeSpecifier::Void, // Placeholder
                });
            }

            // Type qualifiers
            TokenKind::Const
            | TokenKind::Volatile
            | TokenKind::Restrict
            | TokenKind::Atomic => {
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
                specifiers.push(DeclSpecifier {
                    storage_class: None,
                    type_qualifiers: qualifiers,
                    function_specifiers: FunctionSpecifiers::empty(),
                    alignment_specifier: None,
                    type_specifier: TypeSpecifier::Void, // Placeholder
                });
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
                specifiers.push(DeclSpecifier {
                    storage_class: None,
                    type_qualifiers: TypeQualifiers::empty(),
                    function_specifiers: func_specs,
                    alignment_specifier: None,
                    type_specifier: TypeSpecifier::Void, // Placeholder
                });
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
                let type_specifier = parse_type_specifier(parser)?;
                specifiers.push(DeclSpecifier {
                    storage_class: None,
                    type_qualifiers: TypeQualifiers::empty(),
                    function_specifiers: FunctionSpecifiers::empty(),
                    alignment_specifier: None,
                    type_specifier,
                });
                has_type_specifier = true;
            }

            TokenKind::Identifier(symbol) => {
                debug!(
                    "parse_declaration_specifiers: found identifier {:?}, calling is_type_name, current position: {}",
                    symbol, parser.current_idx
                );
                if parser.is_type_name(symbol) && !has_type_specifier {
                    debug!(
                        "parse_declaration_specifiers: {:?} is a type name and no type specifier yet, parsing type specifier",
                        symbol
                    );
                    let type_specifier = parse_type_specifier(parser)?;
                    specifiers.push(DeclSpecifier {
                        storage_class: None,
                        type_qualifiers: TypeQualifiers::empty(),
                        function_specifiers: FunctionSpecifiers::empty(),
                        alignment_specifier: None,
                        type_specifier,
                    });
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
                let alignment = if parser.matches(&[TokenKind::LeftParen]) {
                    parser.advance(); // consume '('
                    if parser.matches(&[TokenKind::Identifier(Symbol::new(""))]) {
                        // _Alignas(type-name)
                        let type_ref = parse_type_name(parser)?;
                        parser.expect(TokenKind::RightParen)?;
                        AlignmentSpecifier::Type(type_ref)
                    } else {
                        // _Alignas(constant-expression)
                        let expr_result = super::expressions::parse_expression(parser, super::expressions::BindingPower::MIN)?;
                        let expr = match expr_result {
                            super::ParseExprOutput::Expression(node) => node,
                            _ => {
                                return Err(ParseError::SyntaxError {
                                    message: "Expected expression in _Alignas".to_string(),
                                    location: parser.current_token().unwrap().location,
                                });
                            }
                        };
                        parser.expect(TokenKind::RightParen)?;
                        AlignmentSpecifier::Expr(expr)
                    }
                } else {
                    return Err(ParseError::SyntaxError {
                        message: "Expected '(' after _Alignas".to_string(),
                        location: token.location,
                    });
                };

                specifiers.push(DeclSpecifier {
                    storage_class: None,
                    type_qualifiers: TypeQualifiers::empty(),
                    function_specifiers: FunctionSpecifiers::empty(),
                    alignment_specifier: Some(alignment),
                    type_specifier: TypeSpecifier::Void, // Placeholder
                });
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

/// Parse type specifier
fn parse_type_specifier(parser: &mut Parser) -> Result<TypeSpecifier, ParseError> {
    parse_type_specifier_with_context(parser, false)
}

/// Parse type specifier with context
fn parse_type_specifier_with_context(
    parser: &mut Parser,
    in_struct_member: bool,
) -> Result<TypeSpecifier, ParseError> {
    let token = parser
        .try_current_token()
        .ok_or_else(|| ParseError::SyntaxError {
            message: "Expected type specifier".to_string(),
            location: SourceSpan::empty(),
        })?;

    match token.kind {
        TokenKind::Void => {
            parser.advance();
            Ok(TypeSpecifier::Void)
        }
        TokenKind::Char => {
            parser.advance();
            Ok(TypeSpecifier::Char)
        }
        TokenKind::Short => {
            parser.advance();
            Ok(TypeSpecifier::Short)
        }
        TokenKind::Int => {
            parser.advance();
            Ok(TypeSpecifier::Int)
        }
        TokenKind::Long => {
            parser.advance();
            // Check for long long or long double
            if let Some(next_token) = parser.try_current_token() {
                match next_token.kind {
                    TokenKind::Long => {
                        parser.advance();
                        Ok(TypeSpecifier::LongLong)
                    }
                    TokenKind::Double => {
                        parser.advance();
                        Ok(TypeSpecifier::LongDouble)
                    }
                    _ => Ok(TypeSpecifier::Long),
                }
            } else {
                Ok(TypeSpecifier::Long)
            }
        }
        TokenKind::Float => {
            parser.advance();
            Ok(TypeSpecifier::Float)
        }
        TokenKind::Double => {
            parser.advance();
            Ok(TypeSpecifier::Double)
        }
        TokenKind::Signed => {
            parser.advance();
            Ok(TypeSpecifier::Signed)
        }
        TokenKind::Unsigned => {
            parser.advance();
            Ok(TypeSpecifier::Unsigned)
        }
        TokenKind::Bool => {
            parser.advance();
            Ok(TypeSpecifier::Bool)
        }
        TokenKind::Complex => {
            parser.advance();
            // Parse optional base type for _Complex (C11 allows _Complex float, _Complex double, etc.)
            // For now, just consume the base type - full implementation would create proper type
            if parser.matches(&[TokenKind::Float, TokenKind::Double, TokenKind::Long]) {
                // For now, just consume the base type - full implementation would create proper type
                parser.advance();
                if parser.matches(&[TokenKind::Double]) {
                    parser.advance(); // consume double for long double
                }
            }
            Ok(TypeSpecifier::Complex)
        }
        TokenKind::Atomic => {
            parser.advance();
            parser.expect(TokenKind::LeftParen)?;
            let type_ref = parse_type_name(parser)?;
            parser.expect(TokenKind::RightParen)?;
            Ok(TypeSpecifier::Atomic(type_ref))
        }
        TokenKind::Struct => {
            parser.advance();
            parse_record_specifier_with_context(parser, false, in_struct_member)
        }
        TokenKind::Union => {
            parser.advance();
            parse_record_specifier_with_context(parser, true, in_struct_member)
        }
        TokenKind::Enum => {
            parser.advance();
            parse_enum_specifier(parser)
        }
        TokenKind::Identifier(symbol) => {
            parser.advance();
            Ok(TypeSpecifier::TypedefName(symbol))
        }
        _ => Err(ParseError::UnexpectedToken {
            expected: vec![
                TokenKind::Void,
                TokenKind::Char,
                TokenKind::Short,
                TokenKind::Int,
                TokenKind::Long,
                TokenKind::Float,
                TokenKind::Double,
                TokenKind::Signed,
                TokenKind::Unsigned,
                TokenKind::Bool,
                TokenKind::Complex,
                TokenKind::Atomic,
                TokenKind::Struct,
                TokenKind::Union,
                TokenKind::Enum,
                TokenKind::Identifier(Symbol::new("")),
            ],
            found: token.kind,
            location: token.location,
        }),
    }
}

/// Parse struct or union specifier with context
fn parse_record_specifier_with_context(
    parser: &mut Parser,
    is_union: bool,
    in_struct_member: bool,
) -> Result<TypeSpecifier, ParseError> {
    let tag = if let Some(token) = parser.try_current_token() {
        if let TokenKind::Identifier(symbol) = token.kind {
            parser.advance();
            Some(symbol)
        } else {
            None
        }
    } else {
        None
    };

    // In struct member context, only parse members if we have a specific tag
    // to avoid confusion with anonymous nested structs
    let definition =
        if parser.matches(&[TokenKind::LeftBrace]) && (!in_struct_member || tag.is_some()) {
            parser.advance(); // consume '{'
            let members = parse_struct_declaration_list(parser)?;
            parser.expect(TokenKind::RightBrace)?;
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

/// Parse enum specifier
fn parse_enum_specifier(parser: &mut Parser) -> Result<TypeSpecifier, ParseError> {
    let tag = if let Some(token) = parser.try_current_token() {
        if let TokenKind::Identifier(symbol) = token.kind {
            parser.advance().ok_or_else(|| ParseError::SyntaxError {
                message: "Unexpected end of input".to_string(),
                location: SourceSpan::empty(),
            })?;
            Some(symbol)
        } else {
            None
        }
    } else {
        None
    };

    let enumerators = if parser.matches(&[TokenKind::LeftBrace]) {
        parser.advance(); // consume '{'
        let enums = parse_enumerator_list(parser)?;
        parser.expect(TokenKind::RightBrace)?;
        Some(enums)
    } else {
        None
    };

    Ok(TypeSpecifier::Enum(tag, enumerators))
}

/// Parse struct declaration list
fn parse_struct_declaration_list(parser: &mut Parser) -> Result<Vec<DeclarationData>, ParseError> {
    let mut declarations = Vec::new();

    while !parser.matches(&[TokenKind::RightBrace]) {
        let declaration = parse_struct_declaration(parser)?;
        declarations.push(declaration);
    }

    Ok(declarations)
}

/// Parse struct declaration
fn parse_struct_declaration(parser: &mut Parser) -> Result<DeclarationData, ParseError> {
    // Check if we have an anonymous struct/union
    if parser.matches(&[TokenKind::Struct, TokenKind::Union]) {
        let is_union = parser.matches(&[TokenKind::Union]);
        parser.advance(); // consume struct/union

        // Check if this is an anonymous struct
        if parser.matches(&[TokenKind::LeftBrace]) {
            // Anonymous struct definition
            parser.expect(TokenKind::LeftBrace)?;
            let members = parse_struct_declaration_list(parser)?;
            parser.expect(TokenKind::RightBrace)?;

            // After parsing { members }, check the next token
            // If the next token is ';', treat it as an anonymous struct member (no declarator needed)
            // If the next token is an identifier or declarator start, continue with variable declaration parsing
            let init_declarators = if parser.matches(&[TokenKind::Semicolon]) {
                // Anonymous struct member: struct { members };
                parser.expect(TokenKind::Semicolon)?;
                Vec::new()
            } else {
                // Variable declaration with anonymous struct type: struct { members } variable;
                vec![InitDeclarator {
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

            let specifiers = vec![DeclSpecifier {
                storage_class: None,
                type_qualifiers: TypeQualifiers::empty(),
                function_specifiers: FunctionSpecifiers::empty(),
                alignment_specifier: None,
                type_specifier,
            }];

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
            let tag = if let Some(token) = parser.try_current_token() {
                if let TokenKind::Identifier(symbol) = token.kind {
                    parser.advance();
                    Some(symbol)
                } else {
                    None
                }
            } else {
                None
            };

            // Check if it's defined inline
            if parser.matches(&[TokenKind::LeftBrace]) {
                // Named struct with definition
                parser.expect(TokenKind::LeftBrace)?;
                let members = parse_struct_declaration_list(parser)?;
                parser.expect(TokenKind::RightBrace)?;

                // After parsing { members }, check the next token
                let init_declarators = if parser.matches(&[TokenKind::Semicolon]) {
                    // Named struct definition: struct tag { members };
                    parser.expect(TokenKind::Semicolon)?;
                    Vec::new()
                } else {
                    // Variable declaration with named struct type: struct tag { members } variable;
                    vec![InitDeclarator {
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

                let specifiers = vec![DeclSpecifier {
                    storage_class: None,
                    type_qualifiers: TypeQualifiers::empty(),
                    function_specifiers: FunctionSpecifiers::empty(),
                    alignment_specifier: None,
                    type_specifier,
                }];

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

                let specifiers = vec![DeclSpecifier {
                    storage_class: None,
                    type_qualifiers: TypeQualifiers::empty(),
                    function_specifiers: FunctionSpecifiers::empty(),
                    alignment_specifier: None,
                    type_specifier,
                }];

                parser.expect(TokenKind::Semicolon)?;

                Ok(DeclarationData {
                    specifiers,
                    init_declarators: vec![InitDeclarator {
                        declarator,
                        initializer: None,
                    }],
                })
            }
        }
    } else {
        // Regular member: type specifier + multiple declarators
        let type_specifier = parse_type_specifier_with_context(parser, true)?;

        let mut init_declarators = Vec::new();
        loop {
            let declarator = super::declarator::parse_declarator(parser, None)?;
            init_declarators.push(InitDeclarator {
                declarator,
                initializer: None,
            });

            if !parser.matches(&[TokenKind::Comma]) {
                break;
            }
            parser.advance(); // consume comma
        }

        let specifiers = vec![DeclSpecifier {
            storage_class: None,
            type_qualifiers: TypeQualifiers::empty(),
            function_specifiers: FunctionSpecifiers::empty(),
            alignment_specifier: None,
            type_specifier,
        }];

        parser.expect(TokenKind::Semicolon)?;

        Ok(DeclarationData {
            specifiers,
            init_declarators,
        })
    }
}

/// Parse enumerator list
fn parse_enumerator_list(parser: &mut Parser) -> Result<Vec<NodeRef>, ParseError> {
    let mut enumerators = Vec::new();

    loop {
        let enumerator = parse_enumerator(parser)?;
        enumerators.push(enumerator);

        if !parser.matches(&[TokenKind::Comma]) {
            break;
        }
        parser.advance(); // consume comma

        // Allow trailing comma
        if parser.matches(&[TokenKind::RightBrace]) {
            break;
        }
    }

    Ok(enumerators)
}

/// Parse enumerator
fn parse_enumerator(parser: &mut Parser) -> Result<NodeRef, ParseError> {
    let token = parser
        .try_current_token()
        .ok_or_else(|| ParseError::SyntaxError {
            message: "Expected enumerator name".to_string(),
            location: SourceSpan::empty(),
        })?;

    let name = match token.kind {
        TokenKind::Identifier(symbol) => symbol,
        _ => {
            return Err(ParseError::UnexpectedToken {
                expected: vec![TokenKind::Identifier(Symbol::new(""))],
                found: token.kind,
                location: token.location,
            });
        }
    };

    parser.advance().ok_or_else(|| ParseError::SyntaxError {
        message: "Unexpected end of input".to_string(),
        location: SourceSpan::empty(),
    })?;

    let value = if parser.matches(&[TokenKind::Assign]) {
        parser.advance(); // consume '='
        let expr_result = super::expressions::parse_expression(parser, super::expressions::BindingPower::MIN)?;
        match expr_result {
            super::ParseExprOutput::Expression(node) => Some(node),
            _ => {
                return Err(ParseError::SyntaxError {
                    message: "Expected expression for enumerator value".to_string(),
                    location: parser.current_token().unwrap().location,
                });
            }
        }
    } else {
        None
    };

    let span = SourceSpan::new(token.location.start, token.location.end);

    let node = parser.ast.push_node(Node {
        kind: NodeKind::EnumConstant(name, value),
        span,
        resolved_type: Cell::new(None),
        resolved_symbol: Cell::new(None),
    });
    Ok(node)
}

/// Parse type name (for casts, sizeof, etc.)
pub fn parse_type_name(parser: &mut Parser) -> Result<TypeRef, ParseError> {
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

/// Parse initializer
pub fn parse_initializer(parser: &mut Parser) -> Result<Initializer, ParseError> {
    debug!(
        "parse_initializer: called at position {}, current token: {:?}",
        parser.current_idx,
        parser.current_token_kind()
    );
    if parser.matches(&[TokenKind::LeftBrace]) {
        debug!("parse_initializer: found LeftBrace, parsing compound initializer");
        // Compound initializer
        parser.advance(); // consume '{'
        let mut initializers = Vec::new();

        while !parser.matches(&[TokenKind::RightBrace]) {
            // Check if this is a designated initializer (starts with . or [)
            let is_designated =
                parser.matches(&[TokenKind::Dot]) || parser.matches(&[TokenKind::LeftBracket]);

            let initializer = if is_designated {
                // Parse designated initializer
                parse_designated_initializer(parser)?
            } else {
                // Parse regular initializer (expression or nested compound initializer)
                let expr_or_compound = if parser.matches(&[TokenKind::LeftBrace]) {
                    // Nested compound initializer
                    parse_initializer(parser)?
                } else {
                    // Expression initializer
                    let expr_result = super::expressions::parse_expression(parser, super::expressions::BindingPower::MIN)?;
                    match expr_result {
                        super::ParseExprOutput::Expression(node) => Initializer::Expression(node),
                        _ => {
                            return Err(ParseError::SyntaxError {
                                message: "Expected expression in initializer".to_string(),
                                location: parser.current_token().unwrap().location,
                            });
                        }
                    }
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
        // Expression initializer
        let expr_result = super::expressions::parse_expression(parser, super::expressions::BindingPower::MIN)?;
        match expr_result {
            super::ParseExprOutput::Expression(node) => Ok(Initializer::Expression(node)),
            _ => Err(ParseError::SyntaxError {
                message: "Expected expression in initializer".to_string(),
                location: parser.current_token().unwrap().location,
            }),
        }
    }
}

/// Parse designated initializer
fn parse_designated_initializer(parser: &mut Parser) -> Result<DesignatedInitializer, ParseError> {
    let designation =
        if parser.matches(&[TokenKind::Dot]) || parser.matches(&[TokenKind::LeftBracket]) {
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
        if parser.matches(&[TokenKind::Dot]) {
            parser.advance(); // consume '.'
            let token = parser
                .try_current_token()
                .ok_or_else(|| ParseError::SyntaxError {
                    message: "Expected field name".to_string(),
                    location: SourceSpan::empty(),
                })?;

            let field_name = match token.kind {
                TokenKind::Identifier(symbol) => symbol,
                _ => {
                    return Err(ParseError::UnexpectedToken {
                        expected: vec![TokenKind::Identifier(Symbol::new(""))],
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
        } else if parser.matches(&[TokenKind::LeftBracket]) {
            parser.advance(); // consume '['
            let expr_result = super::expressions::parse_expression(parser, super::expressions::BindingPower::MIN)?;
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

/// Parse function definition
pub fn parse_function_definition(parser: &mut Parser) -> Result<NodeRef, ParseError> {
    let start_span = parser.current_token()?.location.start;

    // Parse declaration specifiers
    let specifiers = parse_declaration_specifiers(parser)?;

    // Parse declarator (should be a function declarator)
    let declarator = super::declarator::parse_declarator(parser, None)?;

    // Parse function body
    let (body, body_end_span) = super::statements::parse_compound_statement(parser)?;

    let span = SourceSpan::new(start_span, body_end_span);

    let function_def = FunctionDefData {
        specifiers,
        declarator,
        body,
    };

    let node = parser
        .ast
        .push_node(Node::new(NodeKind::FunctionDef(function_def), span));
    Ok(node)
}

/// Parse translation unit (top level)
pub fn parse_translation_unit(parser: &mut Parser) -> Result<NodeRef, ParseError> {
    let start_span = parser.current_token()?.location.start;
    let mut end_span = SourceLoc::empty();

    let mut top_level_declarations = Vec::new();
    let mut iteration_count = 0;
    const MAX_ITERATIONS: usize = 1000; // Prevent infinite loops

    while let Some(token) = parser.try_current_token() {
        if token.kind == TokenKind::EndOfFile {
            end_span = token.location.end;
            break;
        }

        // Prevent infinite loops by limiting iterations
        iteration_count += 1;
        if iteration_count > MAX_ITERATIONS {
            debug!(
                "Parser exceeded maximum iteration limit at token {:?}, position {}",
                token.kind, parser.current_idx
            );
            return Err(ParseError::SyntaxError {
                message: format!(
                    "Parser exceeded maximum iteration limit - possible infinite loop at token {:?}",
                    token.kind
                ),
                location: token.location,
            });
        }

        let initial_idx = parser.current_idx;

        // Try parsing as declaration first
        match parse_declaration(parser) {
            Ok(declaration) => {
                top_level_declarations.push(declaration);
            }
            Err(_) => {
                // If declaration parsing failed, try function definition
                // Reset to initial position for backtracking
                parser.current_idx = initial_idx;
                match parse_function_definition(parser) {
                    Ok(func_def) => {
                        top_level_declarations.push(func_def);
                    }
                    Err(e) => {
                        parser.diag.report_parse_error(e);
                        parser.synchronize();
                    }
                }
            }
        }
    }

    let span = SourceSpan::new(start_span, end_span);
    let node = parser.ast.push_node(Node::new(
        NodeKind::TranslationUnit(top_level_declarations),
        span,
    ));

    parser.ast.set_root_node(node);

    Ok(node)
}

/// Check if current tokens indicate start of a declaration
pub fn is_declaration_start(parser: &Parser) -> bool {
    debug!(
        "is_declaration_start: checking token {:?}",
        parser.current_token_kind()
    );
    if let Some(token) = parser.try_current_token() {
        match token.kind {
            TokenKind::Typedef
            | TokenKind::Extern
            | TokenKind::Static
            | TokenKind::Auto
            | TokenKind::Register
            | TokenKind::ThreadLocal
            | TokenKind::Const
            | TokenKind::Volatile
            | TokenKind::Restrict
            | TokenKind::Atomic
            | TokenKind::Inline
            | TokenKind::Noreturn
            | TokenKind::Void
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
            | TokenKind::Alignas => true,
            TokenKind::Identifier(symbol) => {
                // Check if it's a typedef name
                let is_type = parser.is_type_name(symbol);
                debug!(
                    "is_declaration_start: identifier {:?}, is_type_name={}",
                    symbol, is_type
                );
                is_type
            }
            // Exclude sizeof and other expression-only keywords that might be mistaken for type names
            TokenKind::Sizeof | TokenKind::Alignof | TokenKind::Generic => false,
            _ => false,
        }
    } else {
        false
    }
}

/// Check if current token starts a type name
pub fn is_type_name_start(parser: &Parser) -> bool {
    debug!(
        "is_type_name_start: checking token {:?} at position {}",
        parser.current_token_kind(),
        parser.current_idx
    );

    if let Some(token) = parser.try_current_token() {
        let result = matches!(
            token.kind,
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
                | TokenKind::Const
                | TokenKind::Volatile
                | TokenKind::Restrict
                | TokenKind::Atomic
        );

        // For identifiers, only consider them type name starts if they are actually typedef names
        let is_identifier_type = if let TokenKind::Identifier(symbol) = token.kind {
            parser.is_type_name(symbol)
        } else {
            false
        };

        let final_result = result || is_identifier_type;

        debug!(
            "is_type_name_start: token {:?} is type name start: {} (direct: {}, identifier: {})",
            token.kind, final_result, result, is_identifier_type
        );
        final_result
    } else {
        debug!("is_type_name_start: no token available");
        false
    }
}

/// Parse static assert (C11)
pub fn parse_static_assert(parser: &mut Parser, start_token: Token) -> Result<NodeRef, ParseError> {
    // already consumed `_Static_assert`
    let start_span = start_token.location.start;
    parser.expect(TokenKind::LeftParen)?;

    let condition_result = super::expressions::parse_expression(parser, super::expressions::BindingPower::MIN)?;
    let condition = match condition_result {
        super::ParseExprOutput::Expression(node) => node,
        _ => {
            return Err(ParseError::SyntaxError {
                message: "Expected expression in _Static_assert condition".to_string(),
                location: parser.current_token().unwrap().location,
            });
        }
    };

    parser.expect(TokenKind::Comma)?;

    let token = parser
        .try_current_token()
        .ok_or_else(|| ParseError::SyntaxError {
            message: "Expected string literal in _Static_assert".to_string(),
            location: SourceSpan::empty(),
        })?;

    let message = match token.kind {
        TokenKind::StringLiteral(symbol) => symbol,
        _ => {
            return Err(ParseError::UnexpectedToken {
                expected: vec![TokenKind::StringLiteral(Symbol::new(""))],
                found: token.kind,
                location: token.location,
            });
        }
    };

    parser.advance();
    parser.expect(TokenKind::RightParen)?;
    let semicolon_token = parser.expect(TokenKind::Semicolon)?;
    let end_span = semicolon_token.location.end;

    let span = SourceSpan::new(start_span, end_span);

    let node = parser.ast.push_node(Node {
        kind: NodeKind::StaticAssert(condition, message),
        span,
        resolved_type: Cell::new(None),
        resolved_symbol: Cell::new(None),
    });
    Ok(node)
}