//! Statement parsing module
//!
//! This module handles all statement parsing logic, including control flow
//! statements, compound statements, and expression statements.

use super::Parser;
use crate::ast::*;
use crate::diagnostic::ParseError;
use crate::parser::TokenKind;
use crate::parser::declaration_core::parse_declaration_specifiers;
use crate::parser::declarator::parse_declarator;
use crate::parser::utils::expr_patterns::parse_parenthesized_expr;
use crate::source_manager::SourceLoc;
use thin_vec::thin_vec;

pub(crate) fn parse_statement(parser: &mut Parser) -> Result<ParsedNodeRef, ParseError> {
    let token = parser.current_token()?;

    if let TokenKind::Identifier(name) = token.kind
        && let Some(next) = parser.peek_token(0)
        && next.kind == TokenKind::Colon
    {
        return parse_label_statement(parser, name);
    }

    match token.kind {
        TokenKind::LeftBrace => parse_compound_statement(parser).map(|(node, _)| node),
        TokenKind::If => parse_if_statement(parser),
        TokenKind::Switch => parse_switch_statement(parser),
        TokenKind::While => parse_while_statement(parser),
        TokenKind::Do => parse_do_while_statement(parser),
        TokenKind::For => parse_for_statement(parser),
        TokenKind::Goto => parse_goto_statement(parser),
        TokenKind::Continue => parse_continue_statement(parser),
        TokenKind::Break => parse_break_statement(parser),
        TokenKind::Return => parse_return_statement(parser),
        TokenKind::Semicolon => parse_empty_statement(parser),
        TokenKind::Case => parse_case_statement(parser),
        TokenKind::Default => parse_default_statement(parser),
        _ => parse_expression_statement(parser),
    }
}

pub(crate) fn parse_compound_statement(parser: &mut Parser) -> Result<(ParsedNodeRef, SourceLoc), ParseError> {
    let start = parser.expect(TokenKind::LeftBrace)?.span;
    let dummy = parser.push_dummy();
    let mut items = Vec::new();

    while !parser.at_eof() && !parser.is_token(TokenKind::RightBrace) {
        let mut decl_error = None;
        if parser.starts_declaration() {
            let trx = parser.start_transaction();
            match super::declarations::parse_declaration(trx.parser) {
                Ok(decl) => {
                    items.push(decl);
                    trx.commit();
                    continue;
                }
                Err(e) => decl_error = Some(e),
            }
        }

        match parse_statement(parser) {
            Ok(stmt) => items.push(stmt),
            Err(stmt_err) => {
                parser.diag.report(decl_error.unwrap_or(stmt_err));
                parser.synchronize_until(&[TokenKind::RightBrace]);
            }
        }
    }

    let end = parser.expect(TokenKind::RightBrace)?.span;
    let span = start.merge(end);
    let node = parser.replace_node(dummy, ParsedNodeKind::CompoundStatement(items), span);
    Ok((node, end.end()))
}

fn parse_if_statement(parser: &mut Parser) -> Result<ParsedNodeRef, ParseError> {
    let start = parser.expect(TokenKind::If)?.span;
    let condition = parse_parenthesized_expr(parser)?;
    let then_branch = parse_statement(parser)?;

    let else_branch = if parser.accept(TokenKind::Else).is_some() {
        Some(parse_statement(parser)?)
    } else {
        None
    };

    let end = else_branch
        .map(|e| parser.ast.get_node(e).span)
        .unwrap_or_else(|| parser.ast.get_node(then_branch).span);

    Ok(parser.push_node(
        ParsedNodeKind::If(ParsedIfStmt {
            condition,
            then_branch,
            else_branch,
        }),
        start.merge(end),
    ))
}

fn parse_switch_statement(parser: &mut Parser) -> Result<ParsedNodeRef, ParseError> {
    let start = parser.expect(TokenKind::Switch)?.span;
    let condition = parse_parenthesized_expr(parser)?;
    let body = parse_statement(parser)?;
    let span = start.merge(parser.ast.get_node(body).span);
    Ok(parser.push_node(ParsedNodeKind::Switch(condition, body), span))
}

fn parse_while_statement(parser: &mut Parser) -> Result<ParsedNodeRef, ParseError> {
    let start = parser.expect(TokenKind::While)?.span;
    let condition = parse_parenthesized_expr(parser)?;
    let body = parse_statement(parser)?;
    let span = start.merge(parser.ast.get_node(body).span);
    Ok(parser.push_node(ParsedNodeKind::While(ParsedWhileStmt { condition, body }), span))
}

fn parse_do_while_statement(parser: &mut Parser) -> Result<ParsedNodeRef, ParseError> {
    let start = parser.expect(TokenKind::Do)?.span;
    let body = parse_statement(parser)?;
    parser.expect(TokenKind::While)?;
    let condition = parse_parenthesized_expr(parser)?;
    let end = parser.expect(TokenKind::Semicolon)?.span;
    Ok(parser.push_node(ParsedNodeKind::DoWhile(body, condition), start.merge(end)))
}

fn parse_for_statement(parser: &mut Parser) -> Result<ParsedNodeRef, ParseError> {
    let start = parser.expect(TokenKind::For)?.span;
    let dummy = parser.push_dummy();

    parser.expect(TokenKind::LeftParen)?;

    let init = if parser.accept(TokenKind::Semicolon).is_some() {
        None
    } else if parser.starts_declaration() {
        let specifiers = parse_declaration_specifiers(parser)?;
        let start_span = parser.current_token_span_or_empty();
        let declarator = parse_declarator(parser)?;
        let initializer = if parser.accept(TokenKind::Assign).is_some() {
            Some(super::declaration_core::parse_initializer(parser)?)
        } else {
            None
        };

        let span = start_span.merge(parser.last_token_span().unwrap_or(start_span));
        let decl = ParsedDeclarationData {
            specifiers,
            init_declarators: thin_vec![ParsedInitDeclarator {
                declarator,
                initializer,
                span
            }],
        };
        let node = parser.push_node(
            ParsedNodeKind::Declaration(decl),
            start.merge(parser.current_token_span()?),
        );
        parser.expect(TokenKind::Semicolon)?;
        Some(node)
    } else {
        let expr = parser.parse_expr_min()?;
        parser.expect(TokenKind::Semicolon)?;
        Some(expr)
    };

    let condition = if parser.accept(TokenKind::Semicolon).is_some() {
        None
    } else {
        let expr = parser.parse_expr_min()?;
        parser.expect(TokenKind::Semicolon)?;
        Some(expr)
    };

    let increment = if parser.accept(TokenKind::RightParen).is_some() {
        None
    } else {
        let expr = parser.parse_expr_min()?;
        parser.expect(TokenKind::RightParen)?;
        Some(expr)
    };

    let body = parse_statement(parser)?;
    let span = start.merge(parser.ast.get_node(body).span);
    Ok(parser.replace_node(
        dummy,
        ParsedNodeKind::For(ParsedForStmt {
            init,
            condition,
            increment,
            body,
        }),
        span,
    ))
}

fn parse_goto_statement(parser: &mut Parser) -> Result<ParsedNodeRef, ParseError> {
    let start = parser.expect(TokenKind::Goto)?.span;
    let (label, _) = parser.expect_name()?;
    let end = parser.expect(TokenKind::Semicolon)?.span;
    Ok(parser.push_node(ParsedNodeKind::Goto(label), start.merge(end)))
}

fn parse_continue_statement(parser: &mut Parser) -> Result<ParsedNodeRef, ParseError> {
    let start = parser.expect(TokenKind::Continue)?.span;
    let end = parser.expect(TokenKind::Semicolon)?.span;
    Ok(parser.push_node(ParsedNodeKind::Continue, start.merge(end)))
}

fn parse_break_statement(parser: &mut Parser) -> Result<ParsedNodeRef, ParseError> {
    let start = parser.expect(TokenKind::Break)?.span;
    let end = parser.expect(TokenKind::Semicolon)?.span;
    Ok(parser.push_node(ParsedNodeKind::Break, start.merge(end)))
}

fn parse_return_statement(parser: &mut Parser) -> Result<ParsedNodeRef, ParseError> {
    let start = parser.expect(TokenKind::Return)?.span;
    let value = (!parser.is_token(TokenKind::Semicolon))
        .then(|| parser.parse_expr_min())
        .transpose()?;
    let end = parser.expect(TokenKind::Semicolon)?.span;
    Ok(parser.push_node(ParsedNodeKind::Return(value), start.merge(end)))
}

fn parse_empty_statement(parser: &mut Parser) -> Result<ParsedNodeRef, ParseError> {
    let span = parser.expect(TokenKind::Semicolon)?.span;
    Ok(parser.push_node(ParsedNodeKind::EmptyStatement, span))
}

fn parse_case_statement(parser: &mut Parser) -> Result<ParsedNodeRef, ParseError> {
    let start = parser.expect(TokenKind::Case)?.span;
    let start_expr = parser.parse_expr_min()?;
    let end_expr = parser
        .accept(TokenKind::Ellipsis)
        .map(|_| parser.parse_expr_min())
        .transpose()?;
    parser.expect(TokenKind::Colon)?;
    let stmt = parse_statement(parser)?;
    let span = start.merge(parser.ast.get_node(stmt).span);
    let kind = match end_expr {
        Some(end) => ParsedNodeKind::CaseRange(start_expr, end, stmt),
        None => ParsedNodeKind::Case(start_expr, stmt),
    };
    Ok(parser.push_node(kind, span))
}

fn parse_default_statement(parser: &mut Parser) -> Result<ParsedNodeRef, ParseError> {
    let start = parser.expect(TokenKind::Default)?.span;
    parser.expect(TokenKind::Colon)?;
    let stmt = parse_statement(parser)?;
    let span = start.merge(parser.ast.get_node(stmt).span);
    Ok(parser.push_node(ParsedNodeKind::Default(stmt), span))
}

fn parse_label_statement(parser: &mut Parser, name: NameId) -> Result<ParsedNodeRef, ParseError> {
    let start = parser.advance().unwrap().span;
    parser.expect(TokenKind::Colon)?;
    let stmt = parse_statement(parser)?;
    let span = start.merge(parser.ast.get_node(stmt).span);
    Ok(parser.push_node(ParsedNodeKind::Label(name, stmt), span))
}

fn parse_expression_statement(parser: &mut Parser) -> Result<ParsedNodeRef, ParseError> {
    let dummy = parser.push_dummy();
    let start = parser.current_token_span()?;
    let expr = parser.parse_expr_min()?;
    let end = parser.expect(TokenKind::Semicolon)?.span;
    let span = start.merge(end);
    Ok(parser.replace_node(dummy, ParsedNodeKind::ExpressionStatement(Some(expr)), span))
}
