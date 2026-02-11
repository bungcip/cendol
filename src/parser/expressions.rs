//! Expression parsing module
//!
//! This module handles all expression parsing logic, including the Pratt parser
//! implementation for operator precedence and associativity.

use crate::ast::{parsed::*, *};
use crate::diagnostic::ParseError;
use crate::parser::{Token, TokenKind};
use crate::source_manager::{SourceLoc, SourceSpan};
use log::{debug, trace};

use super::Parser;

/// Binding power for Pratt parser operator precedence
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct BindingPower(u8);

impl BindingPower {
    pub(crate) const MIN: Self = Self(0);
    pub const COMMA: Self = Self(2);
    pub const ASSIGNMENT: Self = Self(4);
    pub const CONDITIONAL: Self = Self(6);
    pub const LOGICAL_OR: Self = Self(8);
    pub const LOGICAL_AND: Self = Self(10);
    pub const BITWISE_OR: Self = Self(12);
    pub const BITWISE_XOR: Self = Self(14);
    pub const BITWISE_AND: Self = Self(16);
    pub const EQUALITY: Self = Self(18);
    pub const RELATIONAL: Self = Self(20);
    pub const SHIFT: Self = Self(22);
    pub const ADDITIVE: Self = Self(24);
    pub const MULTIPLICATIVE: Self = Self(26);
    pub const CAST: Self = Self(28);
    pub const UNARY: Self = Self(30);
    pub const POSTFIX: Self = Self(32);
    // pub const PRIMARY: Self = Self(34);
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Associativity {
    Left,
    Right,
}

/// Pratt parser implementation
pub(crate) struct PrattParser;

impl PrattParser {
    fn get_binding_power(token_kind: TokenKind) -> Option<(BindingPower, Associativity)> {
        match token_kind {
            // Assignment operators (right-associative)
            TokenKind::Assign
            | TokenKind::PlusAssign
            | TokenKind::MinusAssign
            | TokenKind::StarAssign
            | TokenKind::DivAssign
            | TokenKind::ModAssign
            | TokenKind::AndAssign
            | TokenKind::OrAssign
            | TokenKind::XorAssign
            | TokenKind::LeftShiftAssign
            | TokenKind::RightShiftAssign => Some((BindingPower::ASSIGNMENT, Associativity::Right)),

            // Comma operator (left-associative, lowest precedence)
            TokenKind::Comma => Some((BindingPower::COMMA, Associativity::Left)),

            // Conditional operator (right-associative)
            TokenKind::Question => Some((BindingPower::CONDITIONAL, Associativity::Right)),

            // Logical operators (left-associative)
            TokenKind::LogicOr => Some((BindingPower::LOGICAL_OR, Associativity::Left)),
            TokenKind::LogicAnd => Some((BindingPower::LOGICAL_AND, Associativity::Left)),

            // Bitwise operators (left-associative)
            TokenKind::Or => Some((BindingPower::BITWISE_OR, Associativity::Left)),
            TokenKind::Xor => Some((BindingPower::BITWISE_XOR, Associativity::Left)),
            TokenKind::And => Some((BindingPower::BITWISE_AND, Associativity::Left)),

            // Comparison operators (left-associative)
            TokenKind::Equal | TokenKind::NotEqual => Some((BindingPower::EQUALITY, Associativity::Left)),
            TokenKind::Less | TokenKind::Greater | TokenKind::LessEqual | TokenKind::GreaterEqual => {
                Some((BindingPower::RELATIONAL, Associativity::Left))
            }

            // Shift operators (left-associative)
            TokenKind::LeftShift | TokenKind::RightShift => Some((BindingPower::SHIFT, Associativity::Left)),

            // Additive operators (left-associative)
            TokenKind::Plus | TokenKind::Minus => Some((BindingPower::ADDITIVE, Associativity::Left)),

            // Multiplicative operators (left-associative)
            TokenKind::Star | TokenKind::Slash | TokenKind::Percent => {
                Some((BindingPower::MULTIPLICATIVE, Associativity::Left))
            }

            // Postfix operators
            TokenKind::Increment
            | TokenKind::Decrement
            | TokenKind::LeftParen
            | TokenKind::LeftBracket
            | TokenKind::Dot
            | TokenKind::Arrow => Some((BindingPower::POSTFIX, Associativity::Left)),

            _ => None,
        }
    }
}

/// Main expression parsing using Pratt algorithm
pub(crate) fn parse_expression(
    parser: &mut Parser,
    min_binding_power: BindingPower,
) -> Result<ParsedNodeRef, ParseError> {
    trace!("parse_expression: min_binding_power={}", min_binding_power.0);
    let mut left = parse_prefix(parser)?;

    while let Some(current_token) = parser.try_current_token() {
        debug!(
            "parse_expression: loop iteration, current token {:?}, min_binding_power={}",
            current_token.kind, min_binding_power.0
        );

        let Some((binding_power, associativity)) = PrattParser::get_binding_power(current_token.kind) else {
            debug!(
                "parse_expression: no binding power for {:?}, breaking",
                current_token.kind
            );
            break;
        };

        let should_break = match associativity {
            Associativity::Left => binding_power <= min_binding_power,
            Associativity::Right => binding_power < min_binding_power,
        };

        if should_break {
            debug!(
                "parse_expression: binding power {:?} should break at min {:?} (assoc {:?}), breaking",
                binding_power.0, min_binding_power.0, associativity
            );
            break;
        }

        let op_token = current_token;
        parser.advance(); // Consume the operator token

        // Dispatch to the correct parsing function based on the operator kind
        left = match op_token.kind {
            // Postfix operators are handled here directly
            TokenKind::Increment => parse_postfix_increment(parser, left, op_token)?,
            TokenKind::Decrement => parse_postfix_decrement(parser, left, op_token)?,
            TokenKind::LeftParen => parse_function_call(parser, left)?,
            TokenKind::LeftBracket => parse_index_access(parser, left)?,
            TokenKind::Dot => parse_member_access(parser, left, false)?,
            TokenKind::Arrow => parse_member_access(parser, left, true)?,

            // Ternary operator is a special case
            TokenKind::Question => {
                // The middle operand is an `expression`, which allows assignment.
                // C11: logical-OR-expression ? expression : conditional-expression
                let true_expr = parser.parse_expr_assignment()?;
                parser.expect(TokenKind::Colon)?;
                // The third operand is a `conditional-expression`, which has higher precedence.
                let false_expr = parser.parse_expr_bp(BindingPower::CONDITIONAL)?;

                let span = SourceSpan::new(
                    parser.ast.get_node(left).span.start(),
                    parser.ast.get_node(false_expr).span.end(),
                );
                parser.push_node(ParsedNodeKind::TernaryOp(left, true_expr, false_expr), span)
            }

            // All other operators are binary/infix
            _ => {
                let next_min_bp = if associativity == Associativity::Left {
                    BindingPower(binding_power.0 + 1)
                } else {
                    binding_power
                };
                parse_infix(parser, left, op_token, next_min_bp)?
            }
        };
    }

    Ok(left)
}

/// Parse prefix expression
fn parse_prefix(parser: &mut Parser) -> Result<ParsedNodeRef, ParseError> {
    let token = parser.current_token()?;

    debug!("parse_prefix: token={:?} at {}", token.kind, token.span);
    match token.kind {
        TokenKind::Identifier(symbol) => {
            parser.advance();
            debug!("parse_prefix: parsed identifier {:?}", symbol);
            let node = parser.push_node(ParsedNodeKind::Ident(symbol), token.span);
            Ok(node)
        }
        TokenKind::IntegerConstant(val, suffix) => {
            parser.advance();
            let node = parser.push_node(
                ParsedNodeKind::Literal(literal::Literal::Int { val, suffix }),
                token.span,
            );
            Ok(node)
        }
        TokenKind::FloatConstant(val, suffix) => {
            parser.advance();
            let node = parser.push_node(
                ParsedNodeKind::Literal(literal::Literal::Float { val, suffix }),
                token.span,
            );
            Ok(node)
        }
        TokenKind::StringLiteral(s) => {
            parser.advance();
            let node = parser.push_node(ParsedNodeKind::Literal(literal::Literal::String(s)), token.span);
            Ok(node)
        }
        TokenKind::CharacterConstant(c) => {
            parser.advance();
            let node = parser.push_node(ParsedNodeKind::Literal(literal::Literal::Char(c)), token.span);
            Ok(node)
        }
        TokenKind::LeftParen => {
            let left_paren_token = token; // Save the opening paren token for span calculation
            parser.advance();
            // Check if this is a cast expression or compound literal by looking ahead for a type name
            if parser.is_cast_expression_start() {
                // Parse the type name
                let parsed_type = super::parsed_type_builder::parse_parsed_type_name(parser)?;
                // Expect closing parenthesis
                parser.expect(TokenKind::RightParen)?;

                // Check if this is a compound literal (next token is '{')
                if parser.is_token(TokenKind::LeftBrace) {
                    // This is a compound literal: (type-name){initializer}
                    parser.parse_compound_literal_from_type_and_start(parsed_type, left_paren_token.span.start())
                } else {
                    // This is a cast expression: (type-name)expression
                    let dummy_right_paren = Token {
                        kind: TokenKind::RightParen,
                        span: SourceSpan::new(left_paren_token.span.end(), left_paren_token.span.end()),
                    };
                    parser.parse_cast_expression_from_type_and_paren(parsed_type, dummy_right_paren)
                }
            } else if parser.is_token(TokenKind::LeftBrace) {
                // This is a GNU statement expression: ({ ... })
                parse_gnu_statement_expression(parser, left_paren_token.span.start())
            } else {
                // Regular parenthesized expression
                let expr = parser.parse_expr_min()?;
                parser.expect(TokenKind::RightParen)?;
                Ok(expr)
            }
        }
        TokenKind::Plus
        | TokenKind::Minus
        | TokenKind::Not
        | TokenKind::Tilde
        | TokenKind::Increment
        | TokenKind::Decrement
        | TokenKind::Star
        | TokenKind::And => parse_unary_operator(parser, token),
        TokenKind::Generic => parse_generic_selection(parser),
        TokenKind::Alignof => parse_alignof(parser),
        TokenKind::Sizeof => {
            debug!(
                "parse_prefix: parsing sizeof expression at position {}",
                parser.current_idx
            );
            parse_sizeof(parser)
        }
        TokenKind::BuiltinVaArg => parse_builtin_va_arg(parser),
        TokenKind::BuiltinVaStart => parse_builtin_va_start(parser),
        TokenKind::BuiltinVaEnd => parse_builtin_va_end(parser),
        TokenKind::BuiltinVaCopy => parse_builtin_va_copy(parser),
        TokenKind::BuiltinExpect => parse_builtin_expect(parser),
        TokenKind::BuiltinOffsetof => parse_builtin_offsetof(parser),
        TokenKind::BuiltinAtomicLoadN => parse_atomic_op(parser, AtomicOp::LoadN),
        TokenKind::BuiltinAtomicStoreN => parse_atomic_op(parser, AtomicOp::StoreN),
        TokenKind::BuiltinAtomicExchangeN => parse_atomic_op(parser, AtomicOp::ExchangeN),
        TokenKind::BuiltinAtomicCompareExchangeN => parse_atomic_op(parser, AtomicOp::CompareExchangeN),
        TokenKind::BuiltinAtomicFetchAdd => parse_atomic_op(parser, AtomicOp::FetchAdd),
        TokenKind::BuiltinAtomicFetchSub => parse_atomic_op(parser, AtomicOp::FetchSub),
        TokenKind::BuiltinAtomicFetchAnd => parse_atomic_op(parser, AtomicOp::FetchAnd),
        TokenKind::BuiltinAtomicFetchOr => parse_atomic_op(parser, AtomicOp::FetchOr),
        TokenKind::BuiltinAtomicFetchXor => parse_atomic_op(parser, AtomicOp::FetchXor),
        _ => {
            let expected = "identifier, integer, float, string, char, or '('";
            Err(ParseError::UnexpectedToken {
                expected_tokens: expected.to_string(),
                found: token.kind,
                span: token.span,
            })
        }
    }
}

/// Parse unary operator
fn parse_unary_operator(parser: &mut Parser, token: Token) -> Result<ParsedNodeRef, ParseError> {
    let op = match token.kind {
        TokenKind::Plus => UnaryOp::Plus,
        TokenKind::Minus => UnaryOp::Minus,
        TokenKind::Not => UnaryOp::LogicNot,
        TokenKind::Tilde => UnaryOp::BitNot,
        TokenKind::Increment => UnaryOp::PreIncrement,
        TokenKind::Decrement => UnaryOp::PreDecrement,
        TokenKind::Star => UnaryOp::Deref,
        TokenKind::And => UnaryOp::AddrOf,
        _ => {
            return Err(ParseError::InvalidUnaryOperator { span: token.span });
        }
    };

    parser.advance();
    let operand_node = parser.parse_expr_bp(BindingPower::UNARY)?;
    let span = SourceSpan::new(token.span.start(), parser.ast.get_node(operand_node).span.end());
    let node = parser.push_node(ParsedNodeKind::UnaryOp(op, operand_node), span);
    Ok(node)
}

/// Parse infix operator
fn parse_infix(
    parser: &mut Parser,
    left: ParsedNodeRef,
    operator_token: Token,
    min_bp: BindingPower,
) -> Result<ParsedNodeRef, ParseError> {
    debug!(
        "parse_infix: processing operator {:?} at {}",
        operator_token.kind, operator_token.span
    );

    // For all binary operators, parse the right operand
    let right_node = parser.parse_expression(min_bp)?;

    let op = match operator_token.kind {
        TokenKind::Plus => BinaryOp::Add,
        TokenKind::Minus => BinaryOp::Sub,
        TokenKind::Star => BinaryOp::Mul,
        TokenKind::Slash => BinaryOp::Div,
        TokenKind::Percent => BinaryOp::Mod,
        TokenKind::Equal => BinaryOp::Equal,
        TokenKind::NotEqual => BinaryOp::NotEqual,
        TokenKind::Less => BinaryOp::Less,
        TokenKind::Greater => BinaryOp::Greater,
        TokenKind::LessEqual => BinaryOp::LessEqual,
        TokenKind::GreaterEqual => BinaryOp::GreaterEqual,
        TokenKind::And => BinaryOp::BitAnd,
        TokenKind::Or => BinaryOp::BitOr,
        TokenKind::Xor => BinaryOp::BitXor,
        TokenKind::LeftShift => BinaryOp::LShift,
        TokenKind::RightShift => BinaryOp::RShift,
        TokenKind::LogicAnd => BinaryOp::LogicAnd,
        TokenKind::LogicOr => BinaryOp::LogicOr,
        TokenKind::Assign => BinaryOp::Assign,
        TokenKind::PlusAssign => BinaryOp::AssignAdd,
        TokenKind::MinusAssign => BinaryOp::AssignSub,
        TokenKind::StarAssign => BinaryOp::AssignMul,
        TokenKind::DivAssign => BinaryOp::AssignDiv,
        TokenKind::ModAssign => BinaryOp::AssignMod,
        TokenKind::AndAssign => BinaryOp::AssignBitAnd,
        TokenKind::OrAssign => BinaryOp::AssignBitOr,
        TokenKind::XorAssign => BinaryOp::AssignBitXor,
        TokenKind::LeftShiftAssign => BinaryOp::AssignLShift,
        TokenKind::RightShiftAssign => BinaryOp::AssignRShift,
        TokenKind::Comma => BinaryOp::Comma,
        // Postfix operators are handled in `parse_expression` and should not reach here.
        _ => {
            return Err(ParseError::UnexpectedToken {
                expected_tokens: "binary operator".to_string(),
                found: operator_token.kind,
                span: operator_token.span,
            });
        }
    };

    let span = SourceSpan::new(
        parser.ast.get_node(left).span.start(),
        parser.ast.get_node(right_node).span.end(),
    );

    let node = if op.is_assignment() {
        parser.push_node(ParsedNodeKind::Assignment(op, left, right_node), span)
    } else {
        parser.push_node(ParsedNodeKind::BinaryOp(op, left, right_node), span)
    };
    Ok(node)
}

/// Parse GNU statement expression: ({ compound-statement })
fn parse_gnu_statement_expression(parser: &mut Parser, start_loc: SourceLoc) -> Result<ParsedNodeRef, ParseError> {
    debug!("parse_gnu_statement_expression: parsing GNU statement expression");

    // Parse the compound statement (parse_compound_statement expects LeftBrace)
    let (compound_stmt, _) = super::statements::parse_compound_statement(parser)?;

    // Expect the closing parenthesis
    let right_paren_token = parser.expect(TokenKind::RightParen)?;

    // For GNU statement expressions, the result is the last expression in the compound statement
    // We need to extract it from the compound statement
    let result_expr = extract_last_expression_from_compound_statement(parser, compound_stmt);

    let end_loc = right_paren_token.span.end();
    let span = SourceSpan::new(start_loc, end_loc);

    let node = parser.push_node(ParsedNodeKind::GnuStatementExpression(compound_stmt, result_expr), span);
    debug!("parse_gnu_statement_expression: successfully parsed GNU statement expression");
    Ok(node)
}

/// Extract the last expression from a compound statement for GNU statement expressions
fn extract_last_expression_from_compound_statement(
    parser: &mut Parser,
    compound_stmt_node_ref: ParsedNodeRef,
) -> ParsedNodeRef {
    // Get the compound statement node
    let compound_stmt_node = parser.ast.get_node(compound_stmt_node_ref);

    if let ParsedNodeKind::CompoundStatement(statements) = &compound_stmt_node.kind {
        // Find the last expression statement in the compound statement
        for &stmt_ref in statements.iter().rev() {
            let stmt_node = parser.ast.get_node(stmt_ref);
            if let ParsedNodeKind::ExpressionStatement(Some(expr)) = &stmt_node.kind {
                return *expr;
            }
        }

        // If no expression statement found, create a dummy expression
        // This shouldn't happen in valid GNU statement expressions
        let dummy_expr = parser.push_node(ParsedNodeKind::Dummy, compound_stmt_node.span);
        return dummy_expr;
    }

    // Fallback: create a dummy expression
    parser.push_node(ParsedNodeKind::Dummy, compound_stmt_node.span)
}

/// Parse function call
fn parse_function_call(parser: &mut Parser, function: ParsedNodeRef) -> Result<ParsedNodeRef, ParseError> {
    debug!("parse_function_call: parsing function call with LeftParen");

    // Parse the argument list using the utility function
    let args = super::utils::expr_patterns::parse_expr_list(parser, BindingPower::ASSIGNMENT)?;

    let right_paren_token = parser.expect(TokenKind::RightParen)?;
    debug!(
        "parse_function_call: successfully parsed function call with {} arguments",
        args.len()
    );

    let span = SourceSpan::new(parser.ast.get_node(function).span.start(), right_paren_token.span.end());
    let node = parser.push_node(ParsedNodeKind::FunctionCall(function, args), span);
    Ok(node)
}

/// Parse array index access
fn parse_index_access(parser: &mut Parser, array: ParsedNodeRef) -> Result<ParsedNodeRef, ParseError> {
    debug!("parse_index_access: parsing array index");

    // The `[` token has already been consumed by the caller (`parse_infix`).
    // We are now at the start of the index expression.
    let index_node = parser.parse_expr_min()?;

    let right_bracket_token = parser.expect(TokenKind::RightBracket)?;
    debug!(
        "parse_index_access: parsed closing bracket, current token now {:?}",
        parser.current_token_kind()
    );

    let span = SourceSpan::new(parser.ast.get_node(array).span.start(), right_bracket_token.span.end());
    let node = parser.push_node(ParsedNodeKind::IndexAccess(array, index_node), span);
    Ok(node)
}

/// Parse member access
fn parse_member_access(
    parser: &mut Parser,
    object: ParsedNodeRef,
    is_arrow: bool,
) -> Result<ParsedNodeRef, ParseError> {
    let (symbol, span) = parser.expect_name()?;
    let span = SourceSpan::new(parser.ast.get_node(object).span.start(), span.end());
    let node = parser.push_node(ParsedNodeKind::MemberAccess(object, symbol, is_arrow), span);
    Ok(node)
}

/// Parse postfix increment
fn parse_postfix_increment(
    parser: &mut Parser,
    operand: ParsedNodeRef,
    operator_token: Token,
) -> Result<ParsedNodeRef, ParseError> {
    let span = SourceSpan::new(parser.ast.get_node(operand).span.start(), operator_token.span.end());
    let node = parser.push_node(ParsedNodeKind::PostIncrement(operand), span);
    Ok(node)
}

/// Parse postfix decrement
fn parse_postfix_decrement(
    parser: &mut Parser,
    operand: ParsedNodeRef,
    operator_token: Token,
) -> Result<ParsedNodeRef, ParseError> {
    let span = SourceSpan::new(parser.ast.get_node(operand).span.start(), operator_token.span.end());
    let node = parser.push_node(ParsedNodeKind::PostDecrement(operand), span);
    Ok(node)
}

/// Parse _Generic selection (C11)
fn parse_generic_selection(parser: &mut Parser) -> Result<ParsedNodeRef, ParseError> {
    let token = parser.expect(TokenKind::Generic)?;
    let start_loc = token.span.start();

    parser.expect(TokenKind::LeftParen)?;

    // The controlling expression is an assignment-expression, so we parse with ASSIGNMENT binding power.
    let controlling_expr = parser.parse_expr_bp(BindingPower::ASSIGNMENT)?;

    parser.expect(TokenKind::Comma)?;

    // Reserve slot for the generic selection node so that any nested parsing
    // that might push nodes won't accidentally observe an unstable index.
    let dummy = parser.push_dummy();

    let mut associations: Vec<ParsedGenericAssociation> = Vec::new();

    loop {
        let type_name = if parser.accept(TokenKind::Default).is_some() {
            None
        } else {
            let parsed_type = super::parsed_type_builder::parse_parsed_type_name(parser)?;
            Some(parsed_type)
        };

        parser.expect(TokenKind::Colon)?;

        let result_expr = parser.parse_expression(BindingPower::COMMA)?;

        associations.push(ParsedGenericAssociation { type_name, result_expr });

        if !parser.is_token(TokenKind::Comma) {
            break;
        }
        parser.advance(); // consume comma
    }

    let right_paren_token = parser.expect(TokenKind::RightParen)?;
    let end_loc = right_paren_token.span.end();
    let span = SourceSpan::new(start_loc, end_loc);

    let node = parser.replace_node(
        dummy,
        ParsedNodeKind::GenericSelection(controlling_expr, associations),
        span,
    );
    Ok(node)
}

/// Parse compound literal given the type and start location
pub(crate) fn parse_compound_literal_from_type_and_start(
    parser: &mut Parser,
    parsed_type: ParsedType,
    start_loc: SourceLoc,
) -> Result<ParsedNodeRef, ParseError> {
    let initializer_ref = super::declaration_core::parse_initializer(parser)?;

    let end_loc = parser.current_token_span()?.end();
    let span = SourceSpan::new(start_loc, end_loc);
    let node = parser.push_node(ParsedNodeKind::CompoundLiteral(parsed_type, initializer_ref), span);
    Ok(node)
}

/// Parse sizeof expression or type
fn parse_sizeof(parser: &mut Parser) -> Result<ParsedNodeRef, ParseError> {
    let token = parser.expect(TokenKind::Sizeof)?;
    let start_loc = token.span.start();

    let node = if parser.accept(TokenKind::LeftParen).is_some() {
        debug!(
            "parse_sizeof: found '(', now at position {}, token {:?}",
            parser.current_idx,
            parser.current_token_kind()
        );

        // Check if it's a type name or expression
        if parser.is_type_name_start() {
            debug!("parse_sizeof: detected type name start, parsing type name");
            let parsed_type = super::parsed_type_builder::parse_parsed_type_name(parser)?;
            debug!(
                "parse_sizeof: parsed type name, now at position {}, token {:?}",
                parser.current_idx,
                parser.current_token_kind()
            );

            let right_paren_token = parser.expect(TokenKind::RightParen)?;

            let end_loc = right_paren_token.span.end();
            let span = SourceSpan::new(start_loc, end_loc);

            debug!("parse_sizeof: successfully parsed sizeof(type)");
            parser.push_node(ParsedNodeKind::SizeOfType(parsed_type), span)
        } else {
            debug!("parse_sizeof: detected expression, parsing expression");
            let expr = parser.parse_expr_min()?;
            let right_paren_token = parser.expect(TokenKind::RightParen)?;

            let end_loc = right_paren_token.span.end();
            let span = SourceSpan::new(start_loc, end_loc);

            debug!("parse_sizeof: successfully parsed sizeof(expression)");
            parser.push_node(ParsedNodeKind::SizeOfExpr(expr), span)
        }
    } else {
        debug!("parse_sizeof: no '(', parsing unary expression");
        let expr = parser.parse_expr_bp(BindingPower::UNARY)?;

        let end_loc = parser.ast.get_node(expr).span.end();
        let span = SourceSpan::new(start_loc, end_loc);

        debug!("parse_sizeof: successfully parsed sizeof unary expression");
        parser.push_node(ParsedNodeKind::SizeOfExpr(expr), span)
    };

    Ok(node)
}

/// Parse _Alignof (C11)
fn parse_alignof(parser: &mut Parser) -> Result<ParsedNodeRef, ParseError> {
    let token = parser.expect(TokenKind::Alignof)?;
    let start_loc = token.span.start();

    parser.expect(TokenKind::LeftParen)?;

    let parsed_type = super::parsed_type_builder::parse_parsed_type_name(parser)?;
    let right_paren_token = parser.expect(TokenKind::RightParen)?;

    let end_loc = right_paren_token.span.end();

    let span = SourceSpan::new(start_loc, end_loc);

    // Use ParsedAlignOf for the parser phase
    let node = parser.push_node(ParsedNodeKind::AlignOf(parsed_type), span);
    Ok(node)
}

/// Check if a cast expression starts at the current position
/// This is called after consuming an opening parenthesis
pub(crate) fn is_cast_expression_start(parser: &Parser) -> bool {
    // ⚡ Bolt: This is much more efficient than the old lookahead implementation.
    // It avoids a manual loop over the token stream by using the centralized
    // `is_type_name_start` helper, which performs a simple and fast check
    // on the current token.
    parser.is_type_name_start()
}

/// Parse cast expression given the already parsed type and right paren token
pub(crate) fn parse_cast_expression_from_type_and_paren(
    parser: &mut Parser,
    parsed_type: ParsedType,
    right_paren_token: Token,
) -> Result<ParsedNodeRef, ParseError> {
    // Parse the expression being cast
    let expr_node = parser.parse_expr_bp(BindingPower::CAST)?;

    let span = SourceSpan::new(
        right_paren_token.span.start(), // Start from the opening paren
        parser.ast.get_node(expr_node).span.end(),
    );

    let node = parser.push_node(ParsedNodeKind::Cast(parsed_type, expr_node), span);

    debug!("parse_cast_expression: successfully parsed cast expression");
    Ok(node)
}

/// Parse __builtin_va_arg(expr, type)
fn parse_builtin_va_arg(parser: &mut Parser) -> Result<ParsedNodeRef, ParseError> {
    let token = parser.expect(TokenKind::BuiltinVaArg)?;
    let start_loc = token.span.start();

    parser.expect(TokenKind::LeftParen)?;

    // Parse expression (ap)
    let expr = parser.parse_expr_assignment()?;

    parser.expect(TokenKind::Comma)?;

    // Parse type
    let parsed_type = super::parsed_type_builder::parse_parsed_type_name(parser)?;

    let right_paren = parser.expect(TokenKind::RightParen)?;
    let end_loc = right_paren.span.end();
    let span = SourceSpan::new(start_loc, end_loc);

    let node = parser.push_node(ParsedNodeKind::BuiltinVaArg(parsed_type, expr), span);
    Ok(node)
}

/// Parse __builtin_va_start(ap, last_param)
fn parse_builtin_va_start(parser: &mut Parser) -> Result<ParsedNodeRef, ParseError> {
    let token = parser.expect(TokenKind::BuiltinVaStart)?;
    let start_loc = token.span.start();

    parser.expect(TokenKind::LeftParen)?;

    let ap = parser.parse_expr_assignment()?;
    parser.expect(TokenKind::Comma)?;
    let last = parser.parse_expr_assignment()?;

    let right_paren = parser.expect(TokenKind::RightParen)?;
    let end_loc = right_paren.span.end();
    let span = SourceSpan::new(start_loc, end_loc);

    let node = parser.push_node(ParsedNodeKind::BuiltinVaStart(ap, last), span);
    Ok(node)
}

/// Parse __builtin_va_end(ap)
fn parse_builtin_va_end(parser: &mut Parser) -> Result<ParsedNodeRef, ParseError> {
    let token = parser.expect(TokenKind::BuiltinVaEnd)?;
    let start_loc = token.span.start();

    parser.expect(TokenKind::LeftParen)?;

    let ap = parser.parse_expr_assignment()?;

    let right_paren = parser.expect(TokenKind::RightParen)?;
    let end_loc = right_paren.span.end();
    let span = SourceSpan::new(start_loc, end_loc);

    let node = parser.push_node(ParsedNodeKind::BuiltinVaEnd(ap), span);
    Ok(node)
}

/// Parse __builtin_va_copy(dst, src)
fn parse_builtin_va_copy(parser: &mut Parser) -> Result<ParsedNodeRef, ParseError> {
    let token = parser.expect(TokenKind::BuiltinVaCopy)?;
    let start_loc = token.span.start();

    parser.expect(TokenKind::LeftParen)?;

    let dst = parser.parse_expr_assignment()?;
    parser.expect(TokenKind::Comma)?;
    let src = parser.parse_expr_assignment()?;

    let right_paren = parser.expect(TokenKind::RightParen)?;
    let end_loc = right_paren.span.end();
    let span = SourceSpan::new(start_loc, end_loc);

    let node = parser.push_node(ParsedNodeKind::BuiltinVaCopy(dst, src), span);
    Ok(node)
}

/// Parse __builtin_expect(exp, c)
fn parse_builtin_expect(parser: &mut Parser) -> Result<ParsedNodeRef, ParseError> {
    let token = parser.expect(TokenKind::BuiltinExpect)?;
    let start_loc = token.span.start();

    parser.expect(TokenKind::LeftParen)?;

    let exp = parser.parse_expr_assignment()?;
    parser.expect(TokenKind::Comma)?;
    let c = parser.parse_expr_assignment()?;

    let right_paren = parser.expect(TokenKind::RightParen)?;
    let end_loc = right_paren.span.end();
    let span = SourceSpan::new(start_loc, end_loc);

    let node = parser.push_node(ParsedNodeKind::BuiltinExpect(exp, c), span);
    Ok(node)
}

fn parse_builtin_offsetof(parser: &mut Parser) -> Result<ParsedNodeRef, ParseError> {
    let token = parser.expect(TokenKind::BuiltinOffsetof)?;
    let start_loc = token.span.start();

    parser.expect(TokenKind::LeftParen)?;

    // Parse type
    let parsed_type = super::parsed_type_builder::parse_parsed_type_name(parser)?;

    parser.expect(TokenKind::Comma)?;

    // Parse member-designator.
    // C11 7.19p3: "The member-designator shall be such that given static type t* p;
    // the expression &(p->member-designator) is an integer constant expression."
    // We'll parse this into a tree of MemberAccess and IndexAccess nodes.
    // We start with a dummy base representing 'p'.
    let mut current_node = parser.push_node(ParsedNodeKind::Dummy, parser.previous_token_span());

    // First element MUST be a member name.
    let (first_member_name, first_member_span) = parser.expect_name()?;

    current_node = parser.push_node(
        ParsedNodeKind::MemberAccess(current_node, first_member_name, false /* is_arrow */),
        first_member_span,
    );

    // Subsequent elements can be .member or [index]
    loop {
        let tok = parser.current_token()?;
        match tok.kind {
            TokenKind::Dot => {
                parser.advance();
                let (member_name, member_span) = parser.expect_name()?;
                current_node = parser.push_node(
                    ParsedNodeKind::MemberAccess(current_node, member_name, false /* is_arrow */),
                    tok.span.merge(member_span),
                );
            }
            TokenKind::LeftBracket => {
                parser.advance();
                let index_expr = parser.parse_expr_min()?; // Use parse_expr_min for full expression
                let right_bracket = parser.expect(TokenKind::RightBracket)?;
                current_node = parser.push_node(
                    ParsedNodeKind::IndexAccess(current_node, index_expr),
                    tok.span.merge(right_bracket.span),
                );
            }
            _ => break,
        }
    }

    let right_paren = parser.expect(TokenKind::RightParen)?;
    let end_loc = right_paren.span.end();
    let span = SourceSpan::new(start_loc, end_loc);

    let node = parser.push_node(ParsedNodeKind::BuiltinOffsetof(parsed_type, current_node), span);
    Ok(node)
}

/// Parse atomic builtins
fn parse_atomic_op(parser: &mut Parser, op: AtomicOp) -> Result<ParsedNodeRef, ParseError> {
    let token = parser.advance(); // Consume the builtin token
    let start_loc = token.expect("atomic op token").span.start();

    parser.expect(TokenKind::LeftParen)?;

    let args = super::utils::expr_patterns::parse_expr_list(parser, BindingPower::ASSIGNMENT)?;

    let right_paren = parser.expect(TokenKind::RightParen)?;
    let end_loc = right_paren.span.end();
    let span = SourceSpan::new(start_loc, end_loc);

    let node = parser.push_node(ParsedNodeKind::AtomicOp(op, args), span);
    Ok(node)
}
