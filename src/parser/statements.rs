//! Statement parsing module
//!
//! This module handles all statement parsing logic, including control flow
//! statements, compound statements, and expression statements.

use super::Parser;
use crate::ast::*;
use crate::parser::utils::parse_parenthesized_expr;
use crate::parser::{ParseDiag, TokenKind};
use crate::semantic::ScopeId;
use crate::source_manager::SourceLoc;

pub(crate) fn parse_statement(parser: &mut Parser) -> Result<ParsedNodeRef, ParseDiag> {
    parser.skip_attributes()?;

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
        TokenKind::Asm => parse_asm_statement(parser),
        TokenKind::PragmaPack(kind) => {
            parser.advance();
            Ok(parser.push_node(ParsedNodeKind::PragmaPack(kind), token.span))
        }
        TokenKind::PragmaVisibility(kind) => {
            parser.advance();
            Ok(parser.push_node(ParsedNodeKind::PragmaVisibility(kind), token.span))
        }
        _ => parse_expression_statement(parser),
    }
}

pub(crate) fn parse_compound_statement(parser: &mut Parser) -> Result<(ParsedNodeRef, SourceLoc), ParseDiag> {
    let (scope_id, pushed) = if let Some(sid) = parser.next_compound_uses_scope.take() {
        (sid, false)
    } else {
        (parser.symbol_table.push_scope(), true)
    };

    let old_scope = parser.symbol_table.current_scope();
    parser.symbol_table.set_current_scope(scope_id);

    let res = parse_compound_statement_inner(parser, scope_id);

    if pushed {
        parser.symbol_table.pop_scope();
    } else {
        parser.symbol_table.set_current_scope(old_scope);
    }
    res
}

fn parse_compound_statement_inner(
    parser: &mut Parser,
    scope_id: ScopeId,
) -> Result<(ParsedNodeRef, SourceLoc), ParseDiag> {
    let start = parser.expect(TokenKind::LeftBrace)?.span;
    let dummy = parser.push_dummy();
    let mut items = Vec::new();

    while !parser.at_eof() && !parser.is_token(TokenKind::RightBrace) {
        let mut decl_error = None;
        if parser.starts_declaration() {
            match parser.transaction(|p| super::declarations::parse_decl(p, false)) {
                Ok(decl) => {
                    items.push(decl);
                    continue;
                }
                Err(e) => decl_error = Some(e),
            }
        }

        if let Some(token) = parser.accept(TokenKind::Label) {
            let mut labels = Vec::new();
            loop {
                let (name, _) = parser.expect_name()?;
                labels.push(name);
                if parser.accept(TokenKind::Comma).is_none() {
                    break;
                }
            }
            let end_token = parser.expect(TokenKind::Semicolon)?;
            let span = token.span.merge(end_token.span);
            let node = parser.push_node(ParsedNodeKind::GnuLocalLabel(labels.into_boxed_slice()), span);
            items.push(node);
            continue;
        }

        if let Some(token) = parser.try_current_token()
            && let TokenKind::PragmaPack(kind) = token.kind
        {
            let node = parser.push_node(ParsedNodeKind::PragmaPack(kind), token.span);
            items.push(node);
            parser.advance();
            continue;
        }

        if let Some(token) = parser.try_current_token()
            && let TokenKind::PragmaVisibility(kind) = token.kind
        {
            let node = parser.push_node(ParsedNodeKind::PragmaVisibility(kind), token.span);
            items.push(node);
            parser.advance();
            continue;
        }

        match parse_statement(parser) {
            Ok(stmt) => items.push(stmt),
            Err(stmt_err) => {
                parser.report_error(decl_error.unwrap_or(stmt_err));
                parser.synchronize_until(&[TokenKind::RightBrace]);
            }
        }
    }

    let end = parser.expect(TokenKind::RightBrace)?.span;
    let span = start.merge(end);
    let node = parser.replace_node(
        dummy,
        ParsedNodeKind::CompoundStmt(items.into_boxed_slice(), scope_id),
        span,
    );
    Ok((node, end.end()))
}

fn parse_if_statement(parser: &mut Parser) -> Result<ParsedNodeRef, ParseDiag> {
    let start = parser.expect(TokenKind::If)?.span;
    let condition = parse_parenthesized_expr(parser)?;
    let then_branch = parse_statement(parser)?;

    let else_branch = parser
        .accept(TokenKind::Else)
        .map(|_| parse_statement(parser))
        .transpose()?;

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

fn parse_switch_statement(parser: &mut Parser) -> Result<ParsedNodeRef, ParseDiag> {
    let start = parser.expect(TokenKind::Switch)?.span;
    let condition = parse_parenthesized_expr(parser)?;
    let body = parse_statement(parser)?;
    let span = start.merge(parser.ast.get_node(body).span);
    Ok(parser.push_node(ParsedNodeKind::Switch(condition, body), span))
}

fn parse_while_statement(parser: &mut Parser) -> Result<ParsedNodeRef, ParseDiag> {
    let start = parser.expect(TokenKind::While)?.span;
    let condition = parse_parenthesized_expr(parser)?;
    let body = parse_statement(parser)?;
    let span = start.merge(parser.ast.get_node(body).span);
    Ok(parser.push_node(ParsedNodeKind::While(ParsedWhileStmt { condition, body }), span))
}

fn parse_do_while_statement(parser: &mut Parser) -> Result<ParsedNodeRef, ParseDiag> {
    let start = parser.expect(TokenKind::Do)?.span;
    let body = parse_statement(parser)?;
    parser.expect(TokenKind::While)?;
    let condition = parse_parenthesized_expr(parser)?;
    let end = parser.expect(TokenKind::Semicolon)?.span;
    Ok(parser.push_node(ParsedNodeKind::DoWhile(body, condition), start.merge(end)))
}

fn parse_for_statement(parser: &mut Parser) -> Result<ParsedNodeRef, ParseDiag> {
    let start = parser.expect(TokenKind::For)?.span;
    let dummy = parser.push_dummy();

    parser.expect(TokenKind::LeftParen)?;

    let scope_id = parser.symbol_table.push_scope();

    let init = if parser.starts_declaration() {
        Some(super::declarations::parse_decl(parser, false)?)
    } else {
        parser.parse_optional_expr_before(TokenKind::Semicolon)?
    };

    let condition = parser.parse_optional_expr_before(TokenKind::Semicolon)?;
    let increment = parser.parse_optional_expr_before(TokenKind::RightParen)?;

    let body = parse_statement(parser)?;

    parser.symbol_table.pop_scope();

    let span = start.merge(parser.ast.get_node(body).span);
    Ok(parser.replace_node(
        dummy,
        ParsedNodeKind::For(ParsedForStmt {
            init,
            condition,
            increment,
            body,
            scope_id,
        }),
        span,
    ))
}

fn parse_goto_statement(parser: &mut Parser) -> Result<ParsedNodeRef, ParseDiag> {
    let start = parser.expect(TokenKind::Goto)?.span;
    let node_kind = if parser.accept(TokenKind::Star).is_some() {
        ParsedNodeKind::ComputedGoto(parser.parse_expr_min()?)
    } else {
        ParsedNodeKind::Goto(parser.expect_name()?.0)
    };
    let end = parser.expect(TokenKind::Semicolon)?.span;
    Ok(parser.push_node(node_kind, start.merge(end)))
}

fn parse_continue_statement(parser: &mut Parser) -> Result<ParsedNodeRef, ParseDiag> {
    let start = parser.expect(TokenKind::Continue)?.span;
    let end = parser.expect(TokenKind::Semicolon)?.span;
    Ok(parser.push_node(ParsedNodeKind::Continue, start.merge(end)))
}

fn parse_break_statement(parser: &mut Parser) -> Result<ParsedNodeRef, ParseDiag> {
    let start = parser.expect(TokenKind::Break)?.span;
    let end = parser.expect(TokenKind::Semicolon)?.span;
    Ok(parser.push_node(ParsedNodeKind::Break, start.merge(end)))
}

fn parse_return_statement(parser: &mut Parser) -> Result<ParsedNodeRef, ParseDiag> {
    let start = parser.expect(TokenKind::Return)?.span;
    let value = parser.parse_optional_expr_before(TokenKind::Semicolon)?;
    Ok(parser.push_node(
        ParsedNodeKind::Return(value),
        start.merge(parser.last_token_span().unwrap_or(start)),
    ))
}

fn parse_empty_statement(parser: &mut Parser) -> Result<ParsedNodeRef, ParseDiag> {
    let span = parser.expect(TokenKind::Semicolon)?.span;
    Ok(parser.push_node(ParsedNodeKind::EmptyStmt, span))
}

fn parse_statement_after_label(parser: &mut Parser, colon_span: SourceSpan) -> Result<ParsedNodeRef, ParseDiag> {
    if parser.is_token(TokenKind::RightBrace) || parser.starts_declaration() {
        Ok(parser.push_node(ParsedNodeKind::EmptyStmt, colon_span))
    } else {
        parse_statement(parser)
    }
}

fn parse_case_statement(parser: &mut Parser) -> Result<ParsedNodeRef, ParseDiag> {
    let start = parser.expect(TokenKind::Case)?.span;
    let start_expr = parser.parse_expr_min()?;
    let end_expr = parser
        .accept(TokenKind::Ellipsis)
        .map(|_| parser.parse_expr_min())
        .transpose()?;
    let colon_span = parser.expect(TokenKind::Colon)?.span;
    let stmt = parse_statement_after_label(parser, colon_span)?;
    let span = start.merge(parser.ast.get_node(stmt).span);
    let kind = match end_expr {
        Some(end) => ParsedNodeKind::CaseRange(start_expr, end, stmt),
        None => ParsedNodeKind::Case(start_expr, stmt),
    };
    Ok(parser.push_node(kind, span))
}

fn parse_default_statement(parser: &mut Parser) -> Result<ParsedNodeRef, ParseDiag> {
    let start = parser.expect(TokenKind::Default)?.span;
    let colon_span = parser.expect(TokenKind::Colon)?.span;
    let stmt = parse_statement_after_label(parser, colon_span)?;
    let span = start.merge(parser.ast.get_node(stmt).span);
    Ok(parser.push_node(ParsedNodeKind::Default(stmt), span))
}

fn parse_label_statement(parser: &mut Parser, name: NameId) -> Result<ParsedNodeRef, ParseDiag> {
    let start = parser.advance().unwrap().span;
    let colon_span = parser.expect(TokenKind::Colon)?.span;
    let stmt = parse_statement_after_label(parser, colon_span)?;
    let span = start.merge(parser.ast.get_node(stmt).span);
    Ok(parser.push_node(ParsedNodeKind::Label(name, stmt), span))
}

fn parse_expression_statement(parser: &mut Parser) -> Result<ParsedNodeRef, ParseDiag> {
    let dummy = parser.push_dummy();
    let start = parser.current_token_span()?;
    let expr = parser.parse_expr_min()?;
    let end = parser.expect(TokenKind::Semicolon)?.span;
    let span = start.merge(end);
    Ok(parser.replace_node(dummy, ParsedNodeKind::ExpressionStmt(Some(expr)), span))
}

fn parse_asm_statement(parser: &mut Parser) -> Result<ParsedNodeRef, ParseDiag> {
    let start = parser.expect(TokenKind::Asm)?.span;

    let mut is_volatile = false;
    // consume qualifiers like volatile, inline, goto
    while !parser.matches(&[TokenKind::LeftParen, TokenKind::Semicolon]) && !parser.at_eof() {
        if parser.accept(TokenKind::Volatile).is_some() {
            is_volatile = true;
        } else {
            parser.advance();
        }
    }

    parser.expect(TokenKind::LeftParen)?;
    let (template, _) = parser.expect_string_literal()?;

    let mut outputs = Vec::new();
    let mut inputs = Vec::new();
    let mut clobbers = Vec::new();

    let parse_operands = |parser: &mut Parser| -> Result<Vec<ParsedAsmOperand>, ParseDiag> {
        let mut ops = Vec::new();
        while !parser.matches(&[TokenKind::RightParen, TokenKind::Colon]) {
            // Optional [ name ]
            if parser.accept(TokenKind::LeftBracket).is_some() {
                parser.expect_name()?;
                parser.expect(TokenKind::RightBracket)?;
            }

            let (constraint, _) = parser.expect_string_literal()?;
            parser.expect(TokenKind::LeftParen)?;
            let expr = parser.parse_expr_min()?;
            parser.expect(TokenKind::RightParen)?;

            ops.push(ParsedAsmOperand { constraint, expr });

            if parser.accept(TokenKind::Comma).is_none() {
                break;
            }
        }
        Ok(ops)
    };

    if parser.accept(TokenKind::Colon).is_some() {
        outputs = parse_operands(parser)?;
    }

    if parser.accept(TokenKind::Colon).is_some() {
        inputs = parse_operands(parser)?;
    }

    if parser.accept(TokenKind::Colon).is_some() {
        while !parser.matches(&[TokenKind::RightParen, TokenKind::Colon]) {
            let (clobber, _) = parser.expect_string_literal()?;
            clobbers.push(clobber);

            if parser.accept(TokenKind::Comma).is_none() {
                break;
            }
        }
    }

    // Ignore any remaining colons for goto labels, etc.
    while parser.accept(TokenKind::Colon).is_some() {
        while !parser.matches(&[TokenKind::Colon, TokenKind::RightParen]) && !parser.at_eof() {
            parser.advance();
        }
    }

    parser.expect(TokenKind::RightParen)?;
    let end = parser.expect(TokenKind::Semicolon)?.span;

    let asm_stmt = Box::new(ParsedAsmStmt {
        template,
        outputs,
        inputs,
        clobbers,
        is_volatile,
    });
    Ok(parser.push_node(ParsedNodeKind::AsmStmt(asm_stmt), start.merge(end)))
}
