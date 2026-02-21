//! Expression parsing module
//!
//! This module handles all expression parsing logic, including the Pratt parser
//! implementation for operator precedence and associativity.

use crate::ast::literal::Literal;
use crate::ast::{parsed::*, *};
use crate::diagnostic::ParseError;
use crate::parser::{Token, TokenKind};
use crate::source_manager::{SourceLoc, SourceSpan};

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
pub(crate) fn parse_expression(parser: &mut Parser, min_bp: BindingPower) -> Result<ParsedNodeRef, ParseError> {
    let mut left = parse_prefix(parser)?;

    while let Some(token) = parser.try_current_token() {
        let Some((bp, assoc)) = PrattParser::get_binding_power(token.kind) else {
            break;
        };

        if match assoc {
            Associativity::Left => bp <= min_bp,
            Associativity::Right => bp < min_bp,
        } {
            break;
        }

        parser.advance();

        left = match token.kind {
            TokenKind::Increment => parse_postfix_increment(parser, left, token)?,
            TokenKind::Decrement => parse_postfix_decrement(parser, left, token)?,
            TokenKind::LeftParen => parse_function_call(parser, left)?,
            TokenKind::LeftBracket => parse_index_access(parser, left)?,
            TokenKind::Dot => parse_member_access(parser, left, false)?,
            TokenKind::Arrow => parse_member_access(parser, left, true)?,
            TokenKind::Question => {
                let true_expr = parser.parse_expr_assignment()?;
                parser.expect(TokenKind::Colon)?;
                let false_expr = parser.parse_expr_bp(BindingPower::CONDITIONAL)?;
                let span = parser
                    .ast
                    .get_node(left)
                    .span
                    .merge(parser.ast.get_node(false_expr).span);
                parser.push_node(ParsedNodeKind::TernaryOp(left, true_expr, false_expr), span)
            }
            _ => {
                let next_bp = if assoc == Associativity::Left {
                    BindingPower(bp.0 + 1)
                } else {
                    bp
                };
                parse_infix(parser, left, token, next_bp)?
            }
        };
    }

    Ok(left)
}

fn parse_prefix(parser: &mut Parser) -> Result<ParsedNodeRef, ParseError> {
    let token = parser.current_token()?;

    match token.kind {
        TokenKind::Identifier(symbol) => {
            parser.advance();
            Ok(parser.push_node(ParsedNodeKind::Ident(symbol), token.span))
        }
        TokenKind::IntegerConstant(val, suffix, base) => {
            parser.advance();
            Ok(parser.push_node(ParsedNodeKind::Literal(Literal::Int { val, suffix, base }), token.span))
        }
        TokenKind::FloatConstant(val, suffix) => {
            parser.advance();
            Ok(parser.push_node(ParsedNodeKind::Literal(Literal::Float { val, suffix }), token.span))
        }
        TokenKind::StringLiteral(s) => {
            parser.advance();
            Ok(parser.push_node(ParsedNodeKind::Literal(Literal::String(s)), token.span))
        }
        TokenKind::CharacterConstant(c) => {
            parser.advance();
            Ok(parser.push_node(ParsedNodeKind::Literal(Literal::Char(c)), token.span))
        }
        TokenKind::LeftParen => {
            parser.advance();
            if parser.is_cast_expression_start() {
                let parsed_type = super::parsed_type_builder::parse_parsed_type_name(parser)?;
                parser.expect(TokenKind::RightParen)?;

                if parser.is_token(TokenKind::LeftBrace) {
                    parser.parse_compound_literal_from_type_and_start(parsed_type, token.span.start())
                } else {
                    let dummy_right_paren = Token {
                        kind: TokenKind::RightParen,
                        span: SourceSpan::new(token.span.end(), token.span.end()),
                    };
                    parser.parse_cast_expression_from_type_and_paren(parsed_type, dummy_right_paren)
                }
            } else if parser.is_token(TokenKind::LeftBrace) {
                parse_gnu_statement_expression(parser, token.span.start())
            } else {
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
        | TokenKind::And
        | TokenKind::Real
        | TokenKind::Imag => parse_unary_operator(parser, token),

        TokenKind::Generic => parse_generic_selection(parser),
        TokenKind::Alignof => parse_alignof(parser),
        TokenKind::Sizeof => parse_sizeof(parser),

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
        _ => Err(ParseError::UnexpectedToken {
            expected_tokens: "identifier, literal, or '('".to_string(),
            found: token.kind,
            span: token.span,
        }),
    }
}

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
        TokenKind::Real => UnaryOp::Real,
        TokenKind::Imag => UnaryOp::Imag,
        _ => unreachable!(),
    };

    parser.advance();
    let operand_node = parser.parse_expr_bp(BindingPower::UNARY)?;
    let span = token.span.merge(parser.ast.get_node(operand_node).span);
    Ok(parser.push_node(ParsedNodeKind::UnaryOp(op, operand_node), span))
}

fn parse_infix(
    parser: &mut Parser,
    left: ParsedNodeRef,
    token: Token,
    min_bp: BindingPower,
) -> Result<ParsedNodeRef, ParseError> {
    let right = parser.parse_expression(min_bp)?;

    let op = match token.kind {
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
        _ => unreachable!(),
    };

    let span = parser.ast.get_node(left).span.merge(parser.ast.get_node(right).span);
    let kind = if op.is_assignment() {
        ParsedNodeKind::Assignment(op, left, right)
    } else {
        ParsedNodeKind::BinaryOp(op, left, right)
    };
    Ok(parser.push_node(kind, span))
}

/// Parse GNU statement expression: ({ compound-statement })
fn parse_gnu_statement_expression(parser: &mut Parser, start_loc: SourceLoc) -> Result<ParsedNodeRef, ParseError> {
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

fn parse_function_call(parser: &mut Parser, function: ParsedNodeRef) -> Result<ParsedNodeRef, ParseError> {
    let args = super::utils::expr_patterns::parse_expr_list(parser, BindingPower::ASSIGNMENT)?;
    let right_paren = parser.expect(TokenKind::RightParen)?;
    let span = parser.ast.get_node(function).span.merge(right_paren.span);
    Ok(parser.push_node(ParsedNodeKind::FunctionCall(function, args), span))
}

fn parse_index_access(parser: &mut Parser, array: ParsedNodeRef) -> Result<ParsedNodeRef, ParseError> {
    let index = parser.parse_expr_min()?;
    let right_bracket = parser.expect(TokenKind::RightBracket)?;
    let span = parser.ast.get_node(array).span.merge(right_bracket.span);
    Ok(parser.push_node(ParsedNodeKind::IndexAccess(array, index), span))
}

fn parse_member_access(
    parser: &mut Parser,
    object: ParsedNodeRef,
    is_arrow: bool,
) -> Result<ParsedNodeRef, ParseError> {
    let (symbol, span) = parser.expect_name()?;
    let span = parser.ast.get_node(object).span.merge(span);
    Ok(parser.push_node(ParsedNodeKind::MemberAccess(object, symbol, is_arrow), span))
}

fn parse_postfix_increment(
    parser: &mut Parser,
    operand: ParsedNodeRef,
    token: Token,
) -> Result<ParsedNodeRef, ParseError> {
    let span = parser.ast.get_node(operand).span.merge(token.span);
    Ok(parser.push_node(ParsedNodeKind::PostIncrement(operand), span))
}

fn parse_postfix_decrement(
    parser: &mut Parser,
    operand: ParsedNodeRef,
    token: Token,
) -> Result<ParsedNodeRef, ParseError> {
    let span = parser.ast.get_node(operand).span.merge(token.span);
    Ok(parser.push_node(ParsedNodeKind::PostDecrement(operand), span))
}

fn parse_generic_selection(parser: &mut Parser) -> Result<ParsedNodeRef, ParseError> {
    let start = parser.expect(TokenKind::Generic)?.span.start();
    parser.expect(TokenKind::LeftParen)?;

    let controlling_expr = parser.parse_expr_bp(BindingPower::ASSIGNMENT)?;
    parser.expect(TokenKind::Comma)?;

    let dummy = parser.push_dummy();
    let mut associations = Vec::new();

    loop {
        let type_name = if parser.accept(TokenKind::Default).is_some() {
            None
        } else {
            Some(super::parsed_type_builder::parse_parsed_type_name(parser)?)
        };

        parser.expect(TokenKind::Colon)?;
        let result_expr = parser.parse_expression(BindingPower::COMMA)?;
        associations.push(ParsedGenericAssociation { type_name, result_expr });

        if !parser.accept(TokenKind::Comma).is_some() {
            break;
        }
    }

    let end = parser.expect(TokenKind::RightParen)?.span.end();
    Ok(parser.replace_node(
        dummy,
        ParsedNodeKind::GenericSelection(controlling_expr, associations),
        SourceSpan::new(start, end),
    ))
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

fn parse_sizeof(parser: &mut Parser) -> Result<ParsedNodeRef, ParseError> {
    let start = parser.expect(TokenKind::Sizeof)?.span.start();

    let (kind, end) = if parser.accept(TokenKind::LeftParen).is_some() {
        let (kind, end) = if parser.is_type_name_start() {
            let ty = super::parsed_type_builder::parse_parsed_type_name(parser)?;
            let end = parser.expect(TokenKind::RightParen)?.span.end();
            (ParsedNodeKind::SizeOfType(ty), end)
        } else {
            let expr = parser.parse_expr_min()?;
            let end = parser.expect(TokenKind::RightParen)?.span.end();
            (ParsedNodeKind::SizeOfExpr(expr), end)
        };
        (kind, end)
    } else {
        let expr = parser.parse_expr_bp(BindingPower::UNARY)?;
        let end = parser.ast.get_node(expr).span.end();
        (ParsedNodeKind::SizeOfExpr(expr), end)
    };

    Ok(parser.push_node(kind, SourceSpan::new(start, end)))
}

fn parse_alignof(parser: &mut Parser) -> Result<ParsedNodeRef, ParseError> {
    let start = parser.expect(TokenKind::Alignof)?.span.start();
    parser.expect(TokenKind::LeftParen)?;
    let ty = super::parsed_type_builder::parse_parsed_type_name(parser)?;
    let end = parser.expect(TokenKind::RightParen)?.span.end();
    Ok(parser.push_node(ParsedNodeKind::AlignOf(ty), SourceSpan::new(start, end)))
}

pub(crate) fn is_cast_expression_start(parser: &Parser) -> bool {
    parser.is_type_name_start()
}

pub(crate) fn parse_cast_expression_from_type_and_paren(
    parser: &mut Parser,
    ty: ParsedType,
    right_paren: Token,
) -> Result<ParsedNodeRef, ParseError> {
    let expr = parser.parse_expr_bp(BindingPower::CAST)?;
    let span = right_paren.span.merge(parser.ast.get_node(expr).span);
    Ok(parser.push_node(ParsedNodeKind::Cast(ty, expr), span))
}

fn parse_builtin_va_arg(parser: &mut Parser) -> Result<ParsedNodeRef, ParseError> {
    let start = parser.expect(TokenKind::BuiltinVaArg)?.span.start();
    parser.expect(TokenKind::LeftParen)?;
    let expr = parser.parse_expr_assignment()?;
    parser.expect(TokenKind::Comma)?;
    let ty = super::parsed_type_builder::parse_parsed_type_name(parser)?;
    let end = parser.expect(TokenKind::RightParen)?.span.end();
    Ok(parser.push_node(ParsedNodeKind::BuiltinVaArg(ty, expr), SourceSpan::new(start, end)))
}

fn parse_builtin_va_start(parser: &mut Parser) -> Result<ParsedNodeRef, ParseError> {
    let start = parser.expect(TokenKind::BuiltinVaStart)?.span.start();
    parser.expect(TokenKind::LeftParen)?;
    let ap = parser.parse_expr_assignment()?;
    parser.expect(TokenKind::Comma)?;
    let last = parser.parse_expr_assignment()?;
    let end = parser.expect(TokenKind::RightParen)?.span.end();
    Ok(parser.push_node(ParsedNodeKind::BuiltinVaStart(ap, last), SourceSpan::new(start, end)))
}

fn parse_builtin_va_end(parser: &mut Parser) -> Result<ParsedNodeRef, ParseError> {
    let start = parser.expect(TokenKind::BuiltinVaEnd)?.span.start();
    parser.expect(TokenKind::LeftParen)?;
    let ap = parser.parse_expr_assignment()?;
    let end = parser.expect(TokenKind::RightParen)?.span.end();
    Ok(parser.push_node(ParsedNodeKind::BuiltinVaEnd(ap), SourceSpan::new(start, end)))
}

fn parse_builtin_va_copy(parser: &mut Parser) -> Result<ParsedNodeRef, ParseError> {
    let start = parser.expect(TokenKind::BuiltinVaCopy)?.span.start();
    parser.expect(TokenKind::LeftParen)?;
    let dst = parser.parse_expr_assignment()?;
    parser.expect(TokenKind::Comma)?;
    let src = parser.parse_expr_assignment()?;
    let end = parser.expect(TokenKind::RightParen)?.span.end();
    Ok(parser.push_node(ParsedNodeKind::BuiltinVaCopy(dst, src), SourceSpan::new(start, end)))
}

fn parse_builtin_expect(parser: &mut Parser) -> Result<ParsedNodeRef, ParseError> {
    let start = parser.expect(TokenKind::BuiltinExpect)?.span.start();
    parser.expect(TokenKind::LeftParen)?;
    let exp = parser.parse_expr_assignment()?;
    parser.expect(TokenKind::Comma)?;
    let c = parser.parse_expr_assignment()?;
    let end = parser.expect(TokenKind::RightParen)?.span.end();
    Ok(parser.push_node(ParsedNodeKind::BuiltinExpect(exp, c), SourceSpan::new(start, end)))
}

fn parse_builtin_offsetof(parser: &mut Parser) -> Result<ParsedNodeRef, ParseError> {
    let start = parser.expect(TokenKind::BuiltinOffsetof)?.span.start();
    parser.expect(TokenKind::LeftParen)?;
    let ty = super::parsed_type_builder::parse_parsed_type_name(parser)?;
    parser.expect(TokenKind::Comma)?;

    let mut node = parser.push_node(ParsedNodeKind::Dummy, parser.previous_token_span());
    let (name, span) = parser.expect_name()?;
    node = parser.push_node(ParsedNodeKind::MemberAccess(node, name, false), span);

    loop {
        match parser.current_token_kind() {
            Some(TokenKind::Dot) => {
                parser.advance();
                let (name, span) = parser.expect_name()?;
                node = parser.push_node(ParsedNodeKind::MemberAccess(node, name, false), span);
            }
            Some(TokenKind::LeftBracket) => {
                parser.advance();
                let index = parser.parse_expr_min()?;
                let end = parser.expect(TokenKind::RightBracket)?.span;
                node = parser.push_node(ParsedNodeKind::IndexAccess(node, index), end);
            }
            _ => break,
        }
    }

    let end = parser.expect(TokenKind::RightParen)?.span.end();
    Ok(parser.push_node(ParsedNodeKind::BuiltinOffsetof(ty, node), SourceSpan::new(start, end)))
}

fn parse_atomic_op(parser: &mut Parser, op: AtomicOp) -> Result<ParsedNodeRef, ParseError> {
    let start = parser.advance().unwrap().span.start();
    parser.expect(TokenKind::LeftParen)?;
    let args = super::utils::expr_patterns::parse_expr_list(parser, BindingPower::ASSIGNMENT)?;
    let end = parser.expect(TokenKind::RightParen)?.span.end();
    Ok(parser.push_node(ParsedNodeKind::AtomicOp(op, args), SourceSpan::new(start, end)))
}
