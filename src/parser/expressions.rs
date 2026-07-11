//! Expression parsing module
//!
//! This module handles all expression parsing logic, including the Pratt parser
//! implementation for operator precedence and associativity.

use crate::ast::{parsed::*, *};
use crate::parser::type_builder::parse_type_name;
use crate::parser::{ParseDiag, ParseError, Token, TokenKind};
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
pub(crate) fn parse_expression(parser: &mut Parser, min_bp: BindingPower) -> Result<ParsedNodeRef, ParseDiag> {
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
            TokenKind::Increment => {
                let span = parser.ast.get_node(left).span.merge(token.span);
                parser.push_node(ParsedNodeKind::PostIncrement(left), span)
            }
            TokenKind::Decrement => {
                let span = parser.ast.get_node(left).span.merge(token.span);
                parser.push_node(ParsedNodeKind::PostDecrement(left), span)
            }
            TokenKind::LeftParen => parse_function_call(parser, left)?,
            TokenKind::LeftBracket => parse_index_access(parser, left)?,
            TokenKind::Dot => parse_member_access(parser, left, false)?,
            TokenKind::Arrow => parse_member_access(parser, left, true)?,
            TokenKind::Question => {
                let true_expr = parser.parse_expr_min()?;
                parser.expect(TokenKind::Colon)?;
                let false_expr = parser.parse_expression(BindingPower::CONDITIONAL)?;
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

fn parse_prefix(parser: &mut Parser) -> Result<ParsedNodeRef, ParseDiag> {
    let token = parser.current_token()?;

    match token.kind {
        TokenKind::Identifier(symbol) => {
            parser.advance();
            Ok(parser.push_node(ParsedNodeKind::Ident(symbol), token.span))
        }
        TokenKind::Func | TokenKind::Function | TokenKind::PrettyFunction => {
            parser.advance();
            let symbol = match token.kind {
                TokenKind::Func => StringId::new("__func__"),
                TokenKind::Function => StringId::new("__FUNCTION__"),
                TokenKind::PrettyFunction => StringId::new("__PRETTY_FUNCTION__"),
                _ => unreachable!(),
            };
            Ok(parser.push_node(ParsedNodeKind::Ident(symbol), token.span))
        }
        TokenKind::Literal(lit) => {
            parser.advance();
            Ok(parser.push_node(ParsedNodeKind::Literal(lit), token.span))
        }
        TokenKind::LeftParen => {
            parser.advance();
            if parser.is_type_name_start() {
                let parsed_type = parse_type_name(parser)?;
                parser.expect(TokenKind::RightParen)?;

                if parser.is_token(TokenKind::LeftBrace) {
                    parse_compound_literal(parser, parsed_type, token.span)
                } else {
                    let span = SourceSpan::from_loc(token.span.end());
                    parse_cast(parser, parsed_type, span)
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

        TokenKind::LogicAnd => {
            parser.advance();
            let (label, _) = parser.expect_name()?;
            let span = SourceSpan::new(token.span.start(), parser.previous_token_span().end());
            Ok(parser.push_node(ParsedNodeKind::LabelAddr(label), span))
        }

        TokenKind::Generic => parse_generic_selection(parser),
        TokenKind::Alignof => parse_alignof(parser),
        TokenKind::Sizeof => parse_sizeof(parser),

        TokenKind::BuiltinVaArg => parse_builtin_va_arg(parser),
        TokenKind::BuiltinOffsetof => parse_builtin_offsetof(parser),
        TokenKind::BuiltinChooseExpr => parse_builtin_choose_expr(parser),
        TokenKind::BuiltinComplex => parse_builtin_complex(parser),
        TokenKind::BuiltinBitCast => parse_builtin_bit_cast(parser),
        TokenKind::BuiltinConvertVector => parse_builtin_convertvector(parser),
        TokenKind::BuiltinTypesCompatibleP => parse_builtin_types_compatible_p(parser),

        _ => Err(ParseDiag {
            span: token.span,
            kind: ParseError::UnexpectedToken {
                expected: "identifier, literal, or '('",
                found: token.kind,
            },
        }),
    }
}

fn parse_unary_operator(parser: &mut Parser, mut token: Token) -> Result<ParsedNodeRef, ParseDiag> {
    let mut ops = Vec::new();

    loop {
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
            _ => break,
        };

        ops.push((op, token.span));
        parser.advance();

        if let Some(next_token) = parser.try_current_token() {
            match next_token.kind {
                TokenKind::Plus
                | TokenKind::Minus
                | TokenKind::Not
                | TokenKind::Tilde
                | TokenKind::Increment
                | TokenKind::Decrement
                | TokenKind::Star
                | TokenKind::And
                | TokenKind::Real
                | TokenKind::Imag => {
                    token = next_token;
                }
                _ => break,
            }
        } else {
            break;
        }
    }

    let mut current_node = parser.parse_expression(BindingPower::UNARY)?;

    for (op, span) in ops.into_iter().rev() {
        let full_span = span.merge(parser.ast.get_node(current_node).span);
        current_node = parser.push_node(ParsedNodeKind::UnaryOp(op, current_node), full_span);
    }

    Ok(current_node)
}

fn parse_infix(
    parser: &mut Parser,
    left: ParsedNodeRef,
    token: Token,
    min_bp: BindingPower,
) -> Result<ParsedNodeRef, ParseDiag> {
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
fn parse_gnu_statement_expression(parser: &mut Parser, start_loc: SourceLoc) -> Result<ParsedNodeRef, ParseDiag> {
    // Parse the compound statement (parse_compound_statement expects LeftBrace)
    let (compound_stmt, _) = super::statements::parse_compound_statement(parser)?;

    // Expect the closing parenthesis
    let right_paren_token = parser.expect(TokenKind::RightParen)?;

    // For GNU statement expressions, the result is the last expression in the compound statement
    // We need to extract it from the compound statement
    let result_expr = extract_last_expr_from_compound_stmt(parser, compound_stmt);

    let end_loc = right_paren_token.span.end();
    let span = SourceSpan::new(start_loc, end_loc);

    let node = parser.push_node(ParsedNodeKind::GnuStatementExpr(compound_stmt, result_expr), span);
    Ok(node)
}

/// Extract the last expression from a compound statement for GNU statement expressions
fn extract_last_expr_from_compound_stmt(parser: &mut Parser, compound_stmt: ParsedNodeRef) -> ParsedNodeRef {
    // Get the compound statement node
    let compound_stmt_node = parser.ast.get_node(compound_stmt);

    if let ParsedNodeKind::CompoundStmt(statements, _) = &compound_stmt_node.kind {
        // Find the last expression statement in the compound statement
        for &stmt in statements.iter().rev() {
            let stmt = parser.ast.get_node(stmt);
            if let ParsedNodeKind::ExpressionStmt(Some(expr)) = &stmt.kind {
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

fn parse_function_call(parser: &mut Parser, function: ParsedNodeRef) -> Result<ParsedNodeRef, ParseDiag> {
    let args = super::utils::parse_expr_list(parser, BindingPower::ASSIGNMENT)?;
    let right_paren = parser.expect(TokenKind::RightParen)?;
    let span = parser.ast.get_node(function).span.merge(right_paren.span);
    Ok(parser.push_node(ParsedNodeKind::FunctionCall(function, args.into_boxed_slice()), span))
}

fn parse_index_access(parser: &mut Parser, array: ParsedNodeRef) -> Result<ParsedNodeRef, ParseDiag> {
    let index = parser.parse_expr_min()?;
    let right_bracket = parser.expect(TokenKind::RightBracket)?;
    let span = parser.ast.get_node(array).span.merge(right_bracket.span);
    Ok(parser.push_node(ParsedNodeKind::IndexAccess(array, index), span))
}

fn parse_member_access(parser: &mut Parser, object: ParsedNodeRef, is_arrow: bool) -> Result<ParsedNodeRef, ParseDiag> {
    let (symbol, span) = parser.expect_name()?;
    let span = parser.ast.get_node(object).span.merge(span);
    Ok(parser.push_node(ParsedNodeKind::MemberAccess(object, symbol, is_arrow), span))
}

fn parse_generic_selection(parser: &mut Parser) -> Result<ParsedNodeRef, ParseDiag> {
    let start = parser.expect(TokenKind::Generic)?.span.start();
    parser.expect(TokenKind::LeftParen)?;

    let controlling_expr = parser.parse_expression(BindingPower::ASSIGNMENT)?;
    parser.expect(TokenKind::Comma)?;

    let dummy = parser.push_dummy();

    let associations = crate::parser::utils::parse_comma_separated_list(parser, TokenKind::RightParen, |p| {
        let type_name = if p.accept(TokenKind::Default).is_some() {
            None
        } else {
            Some(parse_type_name(p)?)
        };

        p.expect(TokenKind::Colon)?;
        let result_expr = p.parse_expression(BindingPower::COMMA)?;
        Ok(ParsedGenericAssociation { type_name, result_expr })
    })?;

    let end = parser.expect(TokenKind::RightParen)?.span.end();
    Ok(parser.replace_node(
        dummy,
        ParsedNodeKind::GenericSelection(controlling_expr, associations.into_boxed_slice()),
        SourceSpan::new(start, end),
    ))
}

/// Parse compound literal given the type and start location
pub(crate) fn parse_compound_literal(
    parser: &mut Parser,
    parsed_type: ParsedType,
    start: SourceSpan,
) -> Result<ParsedNodeRef, ParseDiag> {
    let init = super::declarations::parse_initializer(parser)?;
    let end_loc = parser.current_token_span()?;
    let span = start.merge(end_loc);
    let node = parser.push_node(ParsedNodeKind::CompoundLiteral(parsed_type, init), span);
    Ok(node)
}

fn is_type_name_in_parens(parser: &mut Parser) -> bool {
    if !parser.is_token(TokenKind::LeftParen)
        || !parser.peek_token(0).is_some_and(|t| parser.is_type_name_start_token(t))
    {
        return false;
    }

    let mut depth = 1;
    let mut peek_idx = 0;
    while depth > 0 {
        if let Some(token) = parser.peek_token(peek_idx) {
            match token.kind {
                TokenKind::LeftParen => depth += 1,
                TokenKind::RightParen => depth -= 1,
                TokenKind::EndOfFile => break,
                _ => {}
            }
            peek_idx += 1;
        } else {
            break;
        }
    }

    if depth == 0 {
        if let Some(token) = parser.peek_token(peek_idx) {
            token.kind != TokenKind::LeftBrace
        } else {
            true
        }
    } else {
        true
    }
}

fn parse_sizeof(parser: &mut Parser) -> Result<ParsedNodeRef, ParseDiag> {
    let start = parser.expect(TokenKind::Sizeof)?.span;

    let (kind, end) = if is_type_name_in_parens(parser) {
        parser.expect(TokenKind::LeftParen)?;
        let ty = parse_type_name(parser)?;
        let right_paren_end = parser.expect(TokenKind::RightParen)?.span;
        (ParsedNodeKind::SizeOfType(ty), right_paren_end)
    } else {
        let expr = parser.parse_expression(BindingPower::UNARY)?;
        let end = parser.ast.get_node(expr).span;
        (ParsedNodeKind::SizeOfExpr(expr), end)
    };

    Ok(parser.push_node(kind, start.merge(end)))
}

fn parse_alignof(parser: &mut Parser) -> Result<ParsedNodeRef, ParseDiag> {
    let start = parser.expect(TokenKind::Alignof)?.span.start();

    let (kind, end) = if is_type_name_in_parens(parser) {
        parser.expect(TokenKind::LeftParen)?;
        let ty = parse_type_name(parser)?;
        let end = parser.expect(TokenKind::RightParen)?.span.end();
        (ParsedNodeKind::AlignOfType(ty), end)
    } else {
        let expr = parser.parse_expression(BindingPower::UNARY)?;
        let end = parser.ast.get_node(expr).span.end();
        (ParsedNodeKind::AlignOfExpr(expr), end)
    };

    Ok(parser.push_node(kind, SourceSpan::new(start, end)))
}

pub(crate) fn parse_cast(parser: &mut Parser, ty: ParsedType, span: SourceSpan) -> Result<ParsedNodeRef, ParseDiag> {
    let expr = parser.parse_expression(BindingPower::CAST)?;
    let span = span.merge(parser.ast.get_node(expr).span);
    Ok(parser.push_node(ParsedNodeKind::Cast(ty, expr), span))
}

fn parse_builtin_va_arg(parser: &mut Parser) -> Result<ParsedNodeRef, ParseDiag> {
    let start = parser.expect(TokenKind::BuiltinVaArg)?.span.start();
    parser.expect(TokenKind::LeftParen)?;
    let expr = parser.parse_expr_assignment()?;
    parser.expect(TokenKind::Comma)?;
    let ty = parse_type_name(parser)?;
    let end = parser.expect(TokenKind::RightParen)?.span.end();
    Ok(parser.push_node(ParsedNodeKind::BuiltinVaArg(ty, expr), SourceSpan::new(start, end)))
}

fn parse_builtin_choose_expr(parser: &mut Parser) -> Result<ParsedNodeRef, ParseDiag> {
    let start = parser.expect(TokenKind::BuiltinChooseExpr)?.span.start();
    parser.expect(TokenKind::LeftParen)?;
    let cond = parser.parse_expr_assignment()?;
    parser.expect(TokenKind::Comma)?;
    let true_expr = parser.parse_expr_assignment()?;
    parser.expect(TokenKind::Comma)?;
    let false_expr = parser.parse_expr_assignment()?;
    let end = parser.expect(TokenKind::RightParen)?.span.end();
    Ok(parser.push_node(
        ParsedNodeKind::BuiltinChooseExpr(cond, true_expr, false_expr),
        SourceSpan::new(start, end),
    ))
}

fn parse_builtin_complex(parser: &mut Parser) -> Result<ParsedNodeRef, ParseDiag> {
    let start = parser.expect(TokenKind::BuiltinComplex)?.span.start();
    parser.expect(TokenKind::LeftParen)?;
    let real = parser.parse_expr_assignment()?;
    parser.expect(TokenKind::Comma)?;
    let imag = parser.parse_expr_assignment()?;
    let end = parser.expect(TokenKind::RightParen)?.span.end();
    Ok(parser.push_node(ParsedNodeKind::BuiltinComplex(real, imag), SourceSpan::new(start, end)))
}

fn parse_builtin_bit_cast(parser: &mut Parser) -> Result<ParsedNodeRef, ParseDiag> {
    let start = parser.expect(TokenKind::BuiltinBitCast)?.span.start();
    parser.expect(TokenKind::LeftParen)?;
    let ty = parse_type_name(parser)?;
    parser.expect(TokenKind::Comma)?;
    let expr = parser.parse_expr_assignment()?;
    let end = parser.expect(TokenKind::RightParen)?.span.end();
    Ok(parser.push_node(ParsedNodeKind::BuiltinBitCast(ty, expr), SourceSpan::new(start, end)))
}

fn parse_builtin_convertvector(parser: &mut Parser) -> Result<ParsedNodeRef, ParseDiag> {
    let start = parser.expect(TokenKind::BuiltinConvertVector)?.span.start();
    parser.expect(TokenKind::LeftParen)?;
    let expr = parser.parse_expr_assignment()?;
    parser.expect(TokenKind::Comma)?;
    let ty = parse_type_name(parser)?;
    let end = parser.expect(TokenKind::RightParen)?.span.end();
    Ok(parser.push_node(
        ParsedNodeKind::BuiltinConvertVector(expr, ty),
        SourceSpan::new(start, end),
    ))
}

fn parse_builtin_offsetof(parser: &mut Parser) -> Result<ParsedNodeRef, ParseDiag> {
    let start = parser.expect(TokenKind::BuiltinOffsetof)?.span.start();
    parser.expect(TokenKind::LeftParen)?;
    let ty = parse_type_name(parser)?;
    parser.expect(TokenKind::Comma)?;

    let span = parser.previous_token_span();
    let mut node = parser.push_node(ParsedNodeKind::Dummy, span);
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

fn parse_builtin_types_compatible_p(parser: &mut Parser) -> Result<ParsedNodeRef, ParseDiag> {
    let start = parser.expect(TokenKind::BuiltinTypesCompatibleP)?.span.start();
    parser.expect(TokenKind::LeftParen)?;
    let ty1 = parse_type_name(parser)?;
    parser.expect(TokenKind::Comma)?;
    let ty2 = parse_type_name(parser)?;
    let end = parser.expect(TokenKind::RightParen)?.span.end();
    Ok(parser.push_node(
        ParsedNodeKind::BuiltinTypesCompatibleP(Box::new((ty1, ty2))),
        SourceSpan::new(start, end),
    ))
}
