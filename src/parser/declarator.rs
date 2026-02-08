//! Declarator parsing module
//!
//! This module handles the parsing of C declarators, which are the most complex
//! part of C's declaration syntax. Declarators can be nested and include pointers,
//! arrays, and functions.

use crate::diagnostic::ParseError;
use crate::parser::declaration_core::parse_declaration_specifiers;
use crate::parser::{Token, TokenKind};
use crate::{ast::*, semantic::TypeQualifiers};
use log::debug;
use thin_vec::{ThinVec, thin_vec};

use super::Parser;

/// Helper enum for reconstructing complex declarators
#[derive(Debug)]
enum DeclaratorComponent {
    Pointer(TypeQualifiers),
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
    base: &ParsedDeclarator,
    new_kind: &str,
    span: SourceSpan,
) -> Result<(), ParseError> {
    match base {
        ParsedDeclarator::Function { .. } => {
            if new_kind == "array" {
                return Err(ParseError::DeclarationNotAllowed { span });
            }
            if new_kind == "function" {
                return Err(ParseError::DeclarationNotAllowed { span });
            }
        }
        ParsedDeclarator::Array(..) => {
            if new_kind == "function" {
                return Err(ParseError::DeclarationNotAllowed { span });
            }
        }
        _ => {}
    }
    Ok(())
}

/// Parse declarator
pub(crate) fn parse_declarator(
    parser: &mut Parser,
    initial_declarator: Option<NameId>,
) -> Result<ParsedDeclarator, ParseError> {
    debug!(
        "parse_declarator: starting at position {}, token: {:?}, initial_declarator: {:?}",
        parser.current_idx,
        parser.current_token_kind(),
        initial_declarator
    );

    // Check for __attribute__ before declarator (GCC extension)
    while parser.is_token(TokenKind::Attribute) {
        if let Err(_e) = super::declaration_core::parse_attribute(parser) {
            debug!("parse_declarator: failed to parse __attribute__: {:?}", _e);
        }
    }

    // Parse leading pointers and their qualifiers
    let declarator_chain = parse_leading_pointers(parser)?;

    // Parse direct declarator (identifier or parenthesized declarator)
    let base_declarator = if parser.accept(TokenKind::LeftParen).is_some() {
        debug!("parse_declarator: found LeftParen, parsing parenthesized declarator");
        let inner_declarator = parse_declarator(parser, None)?;
        debug!(
            "parse_declarator: consumed RightParen, current token: {:?}",
            parser.current_token_kind()
        );
        parser.expect(TokenKind::RightParen)?; // Consume ')'
        inner_declarator
    } else if let Some(ident_symbol) = initial_declarator {
        ParsedDeclarator::Identifier(ident_symbol, TypeQualifiers::empty())
    } else if let Some(token) = parser.try_current_token() {
        if let TokenKind::Identifier(symbol) = token.kind {
            parser.advance(); // Consume identifier
            ParsedDeclarator::Identifier(symbol, TypeQualifiers::empty())
        } else if parser.is_abstract_declarator_start() {
            parse_abstract_declarator(parser)?
        } else {
            // For abstract declarator, if nothing matches, it's just abstract
            ParsedDeclarator::Abstract
        }
    } else {
        // Consume invalid tokens until ) or end
        while let Some(token) = parser.try_current_token() {
            if token.kind == TokenKind::RightParen {
                break;
            }
            debug!("parse_declarator: unexpected token {:?}, consuming", token.kind);
            parser.advance();
        }
        // For abstract declarator, if no token, it's abstract
        ParsedDeclarator::Abstract
    };

    // Parse trailing array and function declarators
    let current_base = parse_trailing_declarators(parser, base_declarator)?;

    // Reconstruct the declarator chain in reverse order
    let final_declarator = reconstruct_declarator_chain(declarator_chain, current_base);

    Ok(final_declarator)
}

/// Helper to parse type qualifiers
fn parse_type_qualifiers(parser: &mut Parser) -> Result<TypeQualifiers, ParseError> {
    let mut qualifiers = TypeQualifiers::empty();
    while let Some(token) = parser.try_current_token() {
        match token.kind {
            TokenKind::Const => {
                qualifiers.insert(TypeQualifiers::CONST);
                parser.advance();
            }
            TokenKind::Volatile => {
                qualifiers.insert(TypeQualifiers::VOLATILE);
                parser.advance();
            }
            TokenKind::Restrict => {
                qualifiers.insert(TypeQualifiers::RESTRICT);
                parser.advance();
            }
            TokenKind::Atomic => {
                qualifiers.insert(TypeQualifiers::ATOMIC);
                parser.advance();
            }
            _ => break,
        }
    }
    Ok(qualifiers)
}

/// Helper to parse array size
fn parse_array_size(parser: &mut Parser) -> Result<ParsedArraySize, ParseError> {
    let is_static = parser.accept(TokenKind::Static).is_some();
    let qualifiers = parse_type_qualifiers(parser)?;

    if parser.accept(TokenKind::Star).is_some() {
        Ok(ParsedArraySize::Star { qualifiers })
    } else if parser.is_token(TokenKind::RightBracket) {
        // Empty []
        Ok(ParsedArraySize::Incomplete)
    } else {
        // Assume it's an expression for the size
        let expr_node = parser.parse_expr_min()?;
        if is_static || !qualifiers.is_empty() {
            Ok(ParsedArraySize::VlaSpecifier {
                is_static,
                qualifiers,
                size: Some(expr_node),
            })
        } else {
            Ok(ParsedArraySize::Expression {
                expr: expr_node,
                qualifiers,
            })
        }
    }
}

/// Parse leading pointers and their qualifiers, building a declarator component chain
fn parse_leading_pointers(parser: &mut Parser) -> Result<Vec<DeclaratorComponent>, ParseError> {
    let mut declarator_chain: Vec<DeclaratorComponent> = Vec::new();

    while parser.accept(TokenKind::Star).is_some() {
        let current_qualifiers = parse_type_qualifiers(parser)?;
        declarator_chain.push(DeclaratorComponent::Pointer(current_qualifiers));
    }

    Ok(declarator_chain)
}

/// Parse trailing declarators (arrays, functions) that follow the base declarator
/// This is used for abstract declarators in type names where bit-fields are not allowed
fn parse_trailing_declarators_for_type_names(
    parser: &mut Parser,
    mut current_base: ParsedDeclarator,
) -> Result<ParsedDeclarator, ParseError> {
    loop {
        let current_token_span = parser.try_current_token().map_or(SourceSpan::empty(), |t| t.span);
        if parser.accept(TokenKind::LeftBracket).is_some() {
            // Array declarator
            validate_declarator_combination(&current_base, "array", current_token_span)?;
            let array_size = parse_array_size(parser)?;
            parser.expect(TokenKind::RightBracket)?; // Consume ']'
            current_base = ParsedDeclarator::Array(Box::new(current_base), array_size);
        } else if parser.accept(TokenKind::LeftParen).is_some() {
            // Function declarator
            validate_declarator_combination(&current_base, "function", current_token_span)?;
            let (parameters, is_variadic) = parse_function_parameters(parser)?;
            parser.expect(TokenKind::RightParen)?; // Consume ')'
            current_base = ParsedDeclarator::Function {
                inner: Box::new(current_base),
                params: parameters,
                is_variadic,
            };
        } else {
            break;
        }
    }

    Ok(current_base)
}

/// Parse trailing declarators (arrays, functions, bit-fields) that follow the base declarator
fn parse_trailing_declarators(
    parser: &mut Parser,
    mut current_base: ParsedDeclarator,
) -> Result<ParsedDeclarator, ParseError> {
    loop {
        let current_token_span = parser.try_current_token().map_or(SourceSpan::empty(), |t| t.span);
        if parser.accept(TokenKind::LeftBracket).is_some() {
            // Array declarator
            validate_declarator_combination(&current_base, "array", current_token_span)?;
            let array_size = parse_array_size(parser)?;
            parser.expect(TokenKind::RightBracket)?; // Consume ']'
            current_base = ParsedDeclarator::Array(Box::new(current_base), array_size);
        } else if parser.accept(TokenKind::LeftParen).is_some() {
            // Function declarator
            validate_declarator_combination(&current_base, "function", current_token_span)?;
            let (parameters, is_variadic) = parse_function_parameters(parser)?;
            parser.expect(TokenKind::RightParen)?; // Consume ')'
            current_base = ParsedDeclarator::Function {
                inner: Box::new(current_base),
                params: parameters,
                is_variadic,
            };
        } else if parser.accept(TokenKind::Colon).is_some() {
            // Bit-field declarator: name : width
            let bit_width_expr = parser.parse_expr_min()?;
            current_base = ParsedDeclarator::BitField(Box::new(current_base), bit_width_expr);
        } else {
            break;
        }
    }

    Ok(current_base)
}

/// Reconstruct the declarator chain by applying pointer qualifiers in reverse order
fn reconstruct_declarator_chain(
    declarator_chain: Vec<DeclaratorComponent>,
    base_declarator: ParsedDeclarator,
) -> ParsedDeclarator {
    let mut final_declarator = base_declarator;
    for component in declarator_chain.into_iter().rev() {
        final_declarator = match component {
            DeclaratorComponent::Pointer(qualifiers) => {
                ParsedDeclarator::Pointer(qualifiers, Some(Box::new(final_declarator)))
            }
        };
    }
    final_declarator
}

/// Helper to parse function parameters
fn parse_function_parameters(parser: &mut Parser) -> Result<(ThinVec<ParsedParamData>, bool), ParseError> {
    let mut params = ThinVec::new();
    let mut is_variadic = false;

    if !parser.is_token(TokenKind::RightParen) {
        if parser.is_token(TokenKind::Void) && parser.peek_token(0).is_some_and(|t| t.kind == TokenKind::RightParen) {
            // void parameter list (only if followed effectively by ')')
            parser.expect(TokenKind::Void)?;
        } else {
            loop {
                if parser.accept(TokenKind::Ellipsis).is_some() {
                    is_variadic = true;
                    break;
                }

                // Check if we have a valid start for parameter declaration
                if !parser.starts_declaration() {
                    break;
                }

                let start_idx = parser.current_idx;

                // Parse declaration specifiers for this parameter
                let specifiers_start_idx = parser.current_idx;
                let saved_diagnostic_count = parser.diag.diagnostics.len();

                debug!(
                    "parse_function_parameters: attempting to parse specifiers at position {}, token: {:?}, is_type_name: {}",
                    start_idx,
                    parser.current_token_kind(),
                    if let Some(TokenKind::Identifier(sym)) = parser.current_token_kind() {
                        parser.is_type_name(sym)
                    } else {
                        false
                    }
                );

                let specifiers = match parse_declaration_specifiers(parser) {
                    Ok(specifiers) => {
                        debug!(
                            "parse_function_parameters: successfully parsed specifiers, current token: {:?}",
                            parser.current_token_kind()
                        );
                        specifiers
                    }
                    Err(_e) => {
                        // If specifier parsing fails, we might be at a position where we need
                        // to fall back to parsing without a proper declarator
                        debug!(
                            "parse_function_parameters: specifier parsing failed at position {}, token: {:?}, error: {:?}, rolling back",
                            parser.current_idx,
                            parser.current_token_kind(),
                            _e
                        );
                        parser.current_idx = specifiers_start_idx;
                        parser.diag.diagnostics.truncate(saved_diagnostic_count);

                        // Create a simple default specifier
                        thin_vec![ParsedDeclSpecifier::TypeSpecifier(ParsedTypeSpecifier::Int)]
                    }
                };

                // Try to parse declarator, but be more careful about failures
                let declarator = if !parser.is_token(TokenKind::Comma)
                    && !parser.is_token(TokenKind::RightParen)
                    && !parser.is_token(TokenKind::Ellipsis)
                {
                    // Special handling for abstract declarators in parameter context
                    if parser.is_token(TokenKind::LeftParen) {
                        debug!("parse_function_parameters: found LeftParen, trying abstract declarator parsing");
                        let start_idx = parser.current_idx;
                        match parse_abstract_declarator(parser) {
                            Ok(abstract_decl) => {
                                debug!("parse_function_parameters: abstract declarator parsed successfully");
                                Some(abstract_decl)
                            }
                            Err(e) => {
                                debug!(
                                    "parse_function_parameters: abstract declarator failed: {:?}, rolling back to {}",
                                    e, start_idx
                                );
                                parser.current_idx = start_idx;
                                // Try regular declarator parsing as fallback
                                match parse_declarator(parser, None) {
                                    Ok(decl) => {
                                        debug!("parse_function_parameters: fallback declarator parsing succeeded");
                                        Some(decl)
                                    }
                                    Err(_) => {
                                        debug!(
                                            "parse_function_parameters: both abstract and regular declarator parsing failed"
                                        );
                                        None
                                    }
                                }
                            }
                        }
                    } else {
                        // Regular declarator parsing for other cases
                        match parse_declarator(parser, None) {
                            Ok(declarator) => {
                                debug!(
                                    "parse_function_parameters: declarator parsed successfully, current token: {:?}",
                                    parser.current_token_kind()
                                );
                                Some(declarator)
                            }
                            Err(e) => {
                                debug!(
                                    "parse_function_parameters: declarator parsing failed: {:?}, current token: {:?}, position: {}",
                                    e,
                                    parser.current_token_kind(),
                                    parser.current_idx
                                );
                                None
                            }
                        }
                    }
                } else {
                    debug!(
                        "parse_function_parameters: skipping declarator parsing due to comma/paren/ellipsis, token: {:?}",
                        parser.current_token_kind()
                    );
                    None
                };

                // Calculate span for the parameter
                let end_span = parser
                    .last_token_span()
                    .unwrap_or_else(|| parser.current_token_span_or_empty());
                let start_token_span = parser.get_token_span(start_idx).unwrap_or_default();
                let span = start_token_span.merge(end_span);

                params.push(ParsedParamData {
                    specifiers,
                    declarator,
                    span,
                });

                debug!(
                    "parse_function_parameters: pushed parameter, current token: {:?}, position: {}",
                    parser.current_token_kind(),
                    parser.current_idx
                );

                if parser.accept(TokenKind::Comma).is_none() {
                    debug!(
                        "parse_function_parameters: no comma found, breaking from parameter loop. Current token: {:?}, position: {}",
                        parser.current_token_kind(),
                        parser.current_idx
                    );
                    break;
                }
                debug!("parse_function_parameters: found comma, continuing to next parameter");

                // After consuming comma, verify we're in a good state to continue
                if parser.is_token(TokenKind::RightParen) {
                    debug!("parse_function_parameters: found unexpected right paren after comma, breaking");
                    break;
                }
            }
        }
    }

    Ok((params, is_variadic))
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
pub(crate) fn get_declarator_name(declarator: &ParsedDeclarator) -> Option<NameId> {
    match declarator {
        ParsedDeclarator::Identifier(name, _) => Some(*name),
        ParsedDeclarator::Pointer(_, Some(inner)) => get_declarator_name(inner),
        ParsedDeclarator::Array(inner, _) => get_declarator_name(inner),
        ParsedDeclarator::Function { inner, .. } => get_declarator_name(inner),
        ParsedDeclarator::BitField(inner, _) => get_declarator_name(inner),
        ParsedDeclarator::AnonymousRecord(_, _) => None,
        ParsedDeclarator::Abstract => None,
        ParsedDeclarator::Pointer(_, None) => None,
    }
}

/// Parse abstract declarator (for type names without identifiers)
pub(crate) fn parse_abstract_declarator(parser: &mut Parser) -> Result<ParsedDeclarator, ParseError> {
    debug!(
        "parse_abstract_declarator: starting at position {}, token {:?}",
        parser.current_idx,
        parser.current_token_kind()
    );

    // Check for __attribute__ at the beginning (GCC extension)
    while parser.is_token(TokenKind::Attribute) {
        if let Err(_e) = super::declaration_core::parse_attribute(parser) {
            debug!("parse_abstract_declarator: failed to parse __attribute__: {:?}", _e);
        }
    }

    // Parse leading pointers and their qualifiers
    let declarator_chain = parse_leading_pointers(parser)?;

    // Parse direct abstract declarator (parenthesized or array/function)
    let base_declarator = if let Some(token) = parser.try_current_token() {
        match token.kind {
            TokenKind::Identifier(symbol) => {
                if parser.is_type_name(symbol) {
                    parser.advance(); // consume type name
                    // Check if next is identifier for named abstract declarator
                    if let Some(next_token) = parser.try_current_token() {
                        if let TokenKind::Identifier(name) = next_token.kind {
                            parser.advance(); // consume identifier
                            ParsedDeclarator::Identifier(name, TypeQualifiers::empty())
                        } else {
                            ParsedDeclarator::Abstract
                        }
                    } else {
                        ParsedDeclarator::Abstract
                    }
                } else {
                    parser.advance(); // consume invalid identifier
                    ParsedDeclarator::Abstract
                }
            }
            TokenKind::Int => {
                parser.advance(); // consume int
                // Check if next is identifier
                if let Some(next_token) = parser.try_current_token() {
                    if let TokenKind::Identifier(name) = next_token.kind {
                        parser.advance(); // consume identifier
                        ParsedDeclarator::Identifier(name, TypeQualifiers::empty())
                    } else {
                        ParsedDeclarator::Abstract
                    }
                } else {
                    ParsedDeclarator::Abstract
                }
            }
            TokenKind::LeftParen => {
                debug!("parse_abstract_declarator: found LeftParen");

                // Check if this is likely a function parameter list start, e.g. `(int...)` or `(char...)`
                // If so, we treat it as a function declarator applied to an empty abstract declarator,
                // instead of consuming the paren as a parenthesized declarator.
                // We also check for `()` which is an empty parameter list.
                let is_param_list_start = if let Some(next_token) = parser.peek_token(0) {
                    if next_token.kind == TokenKind::Attribute {
                        // Disambiguate between `(ATTR *)` (parenthesized declarator) and `(ATTR int)` (param list).
                        // If Attribute is followed by *, it's likely a parenthesized declarator.
                        if let Some(after_attr) = peek_past_attribute(parser, 0) {
                            after_attr.kind != TokenKind::Star
                        } else {
                            // Fallback if attribute syntax is weird
                            true
                        }
                    } else {
                        parser.is_type_name_start_token(next_token) || next_token.kind == TokenKind::RightParen
                    }
                } else {
                    false
                };

                if is_param_list_start {
                    // It's a suffix, e.g. `(int)` in `int (int)`.
                    // We return Abstract so the trailing declarator parser picks it up as a function declarator.
                    ParsedDeclarator::Abstract
                } else {
                    parser.advance(); // Consume '('
                    if parser.accept(TokenKind::RightParen).is_some() {
                        // This case is actually covered by is_param_list_start above,
                        // but if we somehow got here (maybe peek failed?), handle it.
                        // Although if peek failed, we probably hit EOF soon.
                        ParsedDeclarator::Function {
                            inner: Box::new(ParsedDeclarator::Abstract),
                            params: ThinVec::new(),
                            is_variadic: false,
                        }
                    } else {
                        let start_idx = parser.current_idx;
                        let inner_declarator = parse_abstract_declarator(parser)?;
                        debug!(
                            "parse_abstract_declarator: inner declarator parsed, current token: {:?}",
                            parser.current_token_kind()
                        );
                        if parser.accept(TokenKind::RightParen).is_some() {
                            inner_declarator
                        } else {
                            // Check if we're dealing with a function parameter syntax like "int (int)"
                            // In this case, the closing paren might be part of the parameter list context
                            debug!(
                                "parse_abstract_declarator: expected RightParen but found {:?}, position: {}",
                                parser.current_token_kind(),
                                parser.current_idx
                            );
                            // Try to parse as function declarator if we see another LeftParen
                            if parser.accept(TokenKind::LeftParen).is_some() {
                                debug!(
                                    "parse_abstract_declarator: found another LeftParen, treating as function declarator"
                                );
                                let (parameters, is_variadic) = parse_function_parameters(parser)?;
                                parser.expect(TokenKind::RightParen)?; // Consume ')'
                                ParsedDeclarator::Function {
                                    inner: Box::new(inner_declarator),
                                    params: parameters,
                                    is_variadic,
                                }
                            } else {
                                // Roll back and try a different approach
                                parser.current_idx = start_idx;
                                ParsedDeclarator::Abstract
                            }
                        }
                    }
                }
            }
            TokenKind::LeftBracket => {
                parser.advance(); // Consume '['
                let array_size = parse_array_size(parser)?;
                parser.expect(TokenKind::RightBracket)?; // Consume ']'
                ParsedDeclarator::Array(Box::new(ParsedDeclarator::Abstract), array_size)
            }
            TokenKind::Star => {
                parser.advance(); // Consume '*'
                let qualifiers = parse_type_qualifiers(parser)?;
                ParsedDeclarator::Pointer(qualifiers, Some(Box::new(ParsedDeclarator::Abstract)))
            }
            _ => {
                // invalid token, don't consume
                ParsedDeclarator::Abstract
            }
        }
    } else {
        ParsedDeclarator::Abstract
    };

    debug!(
        "parse_abstract_declarator: base_declarator parsed, current token {:?}",
        parser.current_token_kind()
    );

    // Parse trailing array and function declarators
    let current_base = parse_trailing_declarators_for_type_names(parser, base_declarator)?;

    // Reconstruct the declarator chain in reverse order
    let final_declarator = reconstruct_declarator_chain(declarator_chain, current_base);

    Ok(final_declarator)
}
