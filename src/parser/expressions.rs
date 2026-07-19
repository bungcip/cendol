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
pub(crate) fn parse_expression(parser: &mut Parser, min_bp: BindingPower) -> Result<PNodeRef, ParseDiag> {
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
                parser.push_node(PNodeKind::PostIncrement(left), span)
            }
            TokenKind::Decrement => {
                let span = parser.ast.get_node(left).span.merge(token.span);
                parser.push_node(PNodeKind::PostDecrement(left), span)
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
                parser.push_node(PNodeKind::TernaryOp(left, true_expr, false_expr), span)
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

fn parse_prefix(parser: &mut Parser) -> Result<PNodeRef, ParseDiag> {
    let token = parser.current_token()?;

    // Check for unary prefix operators first
    if token.kind.as_prefix_unary_op().is_some() {
        return parse_unary_operator(parser, token);
    }

    match token.kind {
        TokenKind::Identifier(symbol) => {
            parser.advance();
            Ok(parser.push_node(PNodeKind::Ident(symbol), token.span))
        }
        TokenKind::Literal(lit) => {
            parser.advance();
            Ok(parser.push_node(PNodeKind::Literal(lit), token.span))
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

        TokenKind::LogicAnd => {
            parser.advance();
            let (label, _) = parser.expect_name()?;
            let span = SourceSpan::new(token.span.start(), parser.previous_token_span().end());
            Ok(parser.push_node(PNodeKind::LabelAddr(label), span))
        }

        TokenKind::Generic => parse_generic_selection(parser),
        TokenKind::Alignof => parse_sizeof_or_alignof(parser, true),
        TokenKind::Sizeof => parse_sizeof_or_alignof(parser, false),

        TokenKind::BuiltinVaArg => parse_builtin_va_arg(parser),
        TokenKind::BuiltinOffsetof => parse_builtin_offsetof(parser),
        TokenKind::BuiltinChooseExpr => parse_builtin_choose_expr(parser),
        TokenKind::BuiltinComplex => {
            parse_builtin_two_expr(parser, TokenKind::BuiltinComplex, PNodeKind::BuiltinComplex)
        }
        TokenKind::BuiltinBitCast => parse_builtin_type_and_expr(parser, TokenKind::BuiltinBitCast, |ty, expr| {
            PNodeKind::BuiltinBitCast(ty, expr)
        }),
        TokenKind::BuiltinConvertVector => {
            parse_builtin_type_and_expr(parser, TokenKind::BuiltinConvertVector, |ty, expr| {
                PNodeKind::BuiltinConvertVector(expr, ty)
            })
        }
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

fn parse_unary_operator(parser: &mut Parser, mut token: Token) -> Result<PNodeRef, ParseDiag> {
    let mut ops = smallvec::SmallVec::<[(UnaryOp, SourceSpan); 8]>::new();

    loop {
        let Some(op) = token.kind.as_prefix_unary_op() else {
            break;
        };

        ops.push((op, token.span));
        parser.advance();

        match parser.try_current_token() {
            Some(next) if next.kind.as_prefix_unary_op().is_some() => token = next,
            _ => break,
        }
    }

    let mut current_node = parser.parse_expression(BindingPower::UNARY)?;

    for (op, span) in ops.into_iter().rev() {
        let full_span = span.merge(parser.ast.get_node(current_node).span);
        current_node = parser.push_node(PNodeKind::UnaryOp(op, current_node), full_span);
    }

    Ok(current_node)
}

fn parse_infix(parser: &mut Parser, left: PNodeRef, token: Token, min_bp: BindingPower) -> Result<PNodeRef, ParseDiag> {
    let right = parser.parse_expression(min_bp)?;
    let op = token
        .kind
        .as_binary_op()
        .expect("ICE: parse_infix called with non-binary-op token");

    let span = parser.ast.get_node(left).span.merge(parser.ast.get_node(right).span);
    let kind = if op.is_assignment() {
        PNodeKind::Assignment(op, left, right)
    } else {
        PNodeKind::BinaryOp(op, left, right)
    };
    Ok(parser.push_node(kind, span))
}

/// Parse GNU statement expression: ({ compound-statement })
fn parse_gnu_statement_expression(parser: &mut Parser, start_loc: SourceLoc) -> Result<PNodeRef, ParseDiag> {
    // Parse the compound statement (parse_compound_statement expects LeftBrace)
    let (compound_stmt, _) = super::statements::parse_compound_statement(parser)?;

    // Expect the closing parenthesis
    let right_paren_token = parser.expect(TokenKind::RightParen)?;

    // For GNU statement expressions, the result is the last expression in the compound statement
    // We need to extract it from the compound statement
    let result_expr = extract_last_expr_from_compound_stmt(parser, compound_stmt);

    let end_loc = right_paren_token.span.end();
    let span = SourceSpan::new(start_loc, end_loc);

    let node = parser.push_node(PNodeKind::GnuStatementExpr(compound_stmt, result_expr), span);
    Ok(node)
}

/// Extract the last expression from a compound statement for GNU statement expressions
fn extract_last_expr_from_compound_stmt(parser: &mut Parser, compound_stmt: PNodeRef) -> PNodeRef {
    // Get the compound statement node
    let compound_stmt_node = parser.ast.get_node(compound_stmt);

    if let PNodeKind::CompoundStmt(statements, _) = &compound_stmt_node.kind {
        // Find the last expression statement in the compound statement
        for &stmt in statements.iter().rev() {
            let stmt = parser.ast.get_node(stmt);
            if let PNodeKind::ExpressionStmt(Some(expr)) = &stmt.kind {
                return *expr;
            }
        }

        // If no expression statement found, create a dummy expression
        // This shouldn't happen in valid GNU statement expressions
        let dummy_expr = parser.push_node(PNodeKind::Dummy, compound_stmt_node.span);
        return dummy_expr;
    }

    // Fallback: create a dummy expression
    parser.push_node(PNodeKind::Dummy, compound_stmt_node.span)
}

fn parse_function_call(parser: &mut Parser, function: PNodeRef) -> Result<PNodeRef, ParseDiag> {
    let args = super::utils::parse_expr_list(parser, BindingPower::ASSIGNMENT)?;
    let right_paren = parser.expect(TokenKind::RightParen)?;
    let span = parser.ast.get_node(function).span.merge(right_paren.span);
    Ok(parser.push_node(PNodeKind::FunctionCall(function, args.into_boxed_slice()), span))
}

fn parse_index_access(parser: &mut Parser, array: PNodeRef) -> Result<PNodeRef, ParseDiag> {
    let index = parser.parse_expr_min()?;
    let right_bracket = parser.expect(TokenKind::RightBracket)?;
    let span = parser.ast.get_node(array).span.merge(right_bracket.span);
    Ok(parser.push_node(PNodeKind::IndexAccess(array, index), span))
}

fn parse_member_access(parser: &mut Parser, object: PNodeRef, is_arrow: bool) -> Result<PNodeRef, ParseDiag> {
    let (symbol, span) = parser.expect_name()?;
    let span = parser.ast.get_node(object).span.merge(span);
    Ok(parser.push_node(PNodeKind::MemberAccess(object, symbol, is_arrow), span))
}

fn parse_generic_selection(parser: &mut Parser) -> Result<PNodeRef, ParseDiag> {
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
        Ok(PGenericAssociation { type_name, result_expr })
    })?;

    let end = parser.expect(TokenKind::RightParen)?.span.end();
    Ok(parser.replace_node(
        dummy,
        PNodeKind::GenericSelection(controlling_expr, associations.into_boxed_slice()),
        SourceSpan::new(start, end),
    ))
}

/// Parse compound literal given the type and start location
pub(crate) fn parse_compound_literal(
    parser: &mut Parser,
    parsed_type: PType,
    start: SourceSpan,
) -> Result<PNodeRef, ParseDiag> {
    let init = super::declarations::parse_initializer(parser)?;
    let end_loc = parser.current_token_span()?;
    let span = start.merge(end_loc);
    let node = parser.push_node(PNodeKind::CompoundLiteral(parsed_type, init), span);
    Ok(node)
}

fn is_type_name_in_parens(parser: &mut Parser) -> bool {
    if !parser.is_token(TokenKind::LeftParen)
        || !parser
            .peek_token(0)
            .is_some_and(|t| parser.is_type_name_start_token(&t.kind))
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

/// Shared parser for `sizeof` and `_Alignof` — both accept either `(type-name)` or expression.
fn parse_sizeof_or_alignof(parser: &mut Parser, is_alignof: bool) -> Result<PNodeRef, ParseDiag> {
    let keyword = if is_alignof {
        TokenKind::Alignof
    } else {
        TokenKind::Sizeof
    };
    let start = parser.expect(keyword)?.span;

    let (kind, end_span) = if is_type_name_in_parens(parser) {
        parser.expect(TokenKind::LeftParen)?;
        let ty = parse_type_name(parser)?;
        let end = parser.expect(TokenKind::RightParen)?.span;
        let kind = if is_alignof {
            PNodeKind::AlignOfType(ty)
        } else {
            PNodeKind::SizeOfType(ty)
        };
        (kind, end)
    } else {
        let expr = parser.parse_expression(BindingPower::UNARY)?;
        let end = parser.ast.get_node(expr).span;
        let kind = if is_alignof {
            PNodeKind::AlignOfExpr(expr)
        } else {
            PNodeKind::SizeOfExpr(expr)
        };
        (kind, end)
    };

    Ok(parser.push_node(kind, start.merge(end_span)))
}

pub(crate) fn parse_cast(parser: &mut Parser, ty: PType, span: SourceSpan) -> Result<PNodeRef, ParseDiag> {
    let expr = parser.parse_expression(BindingPower::CAST)?;
    let span = span.merge(parser.ast.get_node(expr).span);
    Ok(parser.push_node(PNodeKind::Cast(ty, expr), span))
}

fn parse_builtin_va_arg(parser: &mut Parser) -> Result<PNodeRef, ParseDiag> {
    let start = parser.expect(TokenKind::BuiltinVaArg)?.span.start();
    parser.expect(TokenKind::LeftParen)?;
    let expr = parser.parse_expr_assignment()?;
    parser.expect(TokenKind::Comma)?;
    let ty = parse_type_name(parser)?;
    let end = parser.expect(TokenKind::RightParen)?.span.end();
    Ok(parser.push_node(PNodeKind::BuiltinVaArg(ty, expr), SourceSpan::new(start, end)))
}

fn parse_builtin_choose_expr(parser: &mut Parser) -> Result<PNodeRef, ParseDiag> {
    let start = parser.expect(TokenKind::BuiltinChooseExpr)?.span.start();
    parser.expect(TokenKind::LeftParen)?;
    let cond = parser.parse_expr_assignment()?;
    parser.expect(TokenKind::Comma)?;
    let true_expr = parser.parse_expr_assignment()?;
    parser.expect(TokenKind::Comma)?;
    let false_expr = parser.parse_expr_assignment()?;
    let end = parser.expect(TokenKind::RightParen)?.span.end();
    Ok(parser.push_node(
        PNodeKind::BuiltinChooseExpr(cond, true_expr, false_expr),
        SourceSpan::new(start, end),
    ))
}

/// Parse builtins of the form `__builtin_xxx(expr, expr)` → constructor(expr1, expr2).
fn parse_builtin_two_expr(
    parser: &mut Parser,
    keyword: TokenKind,
    constructor: fn(PNodeRef, PNodeRef) -> PNodeKind,
) -> Result<PNodeRef, ParseDiag> {
    let start = parser.expect(keyword)?.span.start();
    parser.expect(TokenKind::LeftParen)?;
    let first = parser.parse_expr_assignment()?;
    parser.expect(TokenKind::Comma)?;
    let second = parser.parse_expr_assignment()?;
    let end = parser.expect(TokenKind::RightParen)?.span.end();
    Ok(parser.push_node(constructor(first, second), SourceSpan::new(start, end)))
}

/// Parse builtins of the form `__builtin_xxx(type, expr)` or `__builtin_xxx(expr, type)`.
/// The `constructor` receives (type, expr) and returns the node kind.
fn parse_builtin_type_and_expr(
    parser: &mut Parser,
    keyword: TokenKind,
    constructor: fn(PType, PNodeRef) -> PNodeKind,
) -> Result<PNodeRef, ParseDiag> {
    let start = parser.expect(keyword)?.span.start();
    parser.expect(TokenKind::LeftParen)?;

    // Determine argument order by peeking: if it starts with a type name, parse type first.
    let (ty, expr) = if parser.is_type_name_start() {
        let ty = parse_type_name(parser)?;
        parser.expect(TokenKind::Comma)?;
        let expr = parser.parse_expr_assignment()?;
        (ty, expr)
    } else {
        let expr = parser.parse_expr_assignment()?;
        parser.expect(TokenKind::Comma)?;
        let ty = parse_type_name(parser)?;
        (ty, expr)
    };

    let end = parser.expect(TokenKind::RightParen)?.span.end();
    Ok(parser.push_node(constructor(ty, expr), SourceSpan::new(start, end)))
}

fn parse_builtin_offsetof(parser: &mut Parser) -> Result<PNodeRef, ParseDiag> {
    let start = parser.expect(TokenKind::BuiltinOffsetof)?.span.start();
    parser.expect(TokenKind::LeftParen)?;
    let ty = parse_type_name(parser)?;
    parser.expect(TokenKind::Comma)?;

    let span = parser.previous_token_span();
    let mut node = parser.push_node(PNodeKind::Dummy, span);
    let (name, span) = parser.expect_name()?;
    node = parser.push_node(PNodeKind::MemberAccess(node, name, false), span);

    loop {
        match parser.current_token_kind() {
            Some(TokenKind::Dot) => {
                parser.advance();
                let (name, span) = parser.expect_name()?;
                node = parser.push_node(PNodeKind::MemberAccess(node, name, false), span);
            }
            Some(TokenKind::LeftBracket) => {
                parser.advance();
                let index = parser.parse_expr_min()?;
                let end = parser.expect(TokenKind::RightBracket)?.span;
                node = parser.push_node(PNodeKind::IndexAccess(node, index), end);
            }
            _ => break,
        }
    }

    let end = parser.expect(TokenKind::RightParen)?.span.end();
    Ok(parser.push_node(PNodeKind::BuiltinOffsetof(ty, node), SourceSpan::new(start, end)))
}

fn parse_builtin_types_compatible_p(parser: &mut Parser) -> Result<PNodeRef, ParseDiag> {
    let start = parser.expect(TokenKind::BuiltinTypesCompatibleP)?.span.start();
    parser.expect(TokenKind::LeftParen)?;
    let ty1 = parse_type_name(parser)?;
    parser.expect(TokenKind::Comma)?;
    let ty2 = parse_type_name(parser)?;
    let end = parser.expect(TokenKind::RightParen)?.span.end();
    Ok(parser.push_node(
        PNodeKind::BuiltinTypesCompatibleP(Box::new((ty1, ty2))),
        SourceSpan::new(start, end),
    ))
}
