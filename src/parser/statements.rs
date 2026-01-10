//! Statement parsing module
//!
//! This module handles all statement parsing logic, including control flow
//! statements, compound statements, and expression statements.

use super::Parser;
use crate::ast::*;
use crate::diagnostic::ParseError;
use crate::lexer::TokenKind;
use crate::parser::declaration_core::parse_declaration_specifiers;
use crate::parser::declarator::parse_declarator;
use crate::parser::utils::expr_patterns::parse_parenthesized_expr;
use crate::source_manager::{SourceLoc, SourceSpan};
use log::debug;
use thin_vec::thin_vec;

/// Parse a statement
pub(crate) fn parse_statement(parser: &mut Parser) -> Result<ParsedNodeRef, ParseError> {
    let token = parser.current_token()?;

    // Check for label: identifier :
    debug!("parse_statement: token is {:?}, looking for label pattern", token.kind);

    // Try to check if current token is identifier followed by colon
    if let TokenKind::Identifier(label_symbol) = token.kind
        && let Some(next_token) = parser.peek_token(0)
    {
        debug!(
            "parse_statement: identifier '{}' followed by {:?}",
            label_symbol, next_token.kind
        );
        if next_token.kind == TokenKind::Colon {
            debug!("parse_statement: found label pattern, calling parse_label_statement");
            return parse_label_statement(parser, label_symbol);
        }
    }

    match token.kind {
        TokenKind::LeftBrace => {
            let (node, _) = parse_compound_statement(parser)?;
            Ok(node)
        }
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

/// Parse compound statement (block)
pub(crate) fn parse_compound_statement(parser: &mut Parser) -> Result<(ParsedNodeRef, SourceLoc), ParseError> {
    let token = parser.expect(TokenKind::LeftBrace)?;
    let start_loc = token.span.start();
    let dummy = parser.push_dummy();

    let mut block_items = Vec::new();

    while !parser.is_token(TokenKind::RightBrace) {
        let initial_idx = parser.current_idx;

        debug!(
            "parse_compound_statement: parsing block item, current token {:?}, position {}",
            parser.current_token_kind(),
            initial_idx
        );

        // Try parsing as declaration first, but only if it looks like a declaration start
        let should_try_declaration = parser.starts_declaration();
        let mut declaration_attempt: Option<Result<ParsedNodeRef, ParseError>> = None;

        if should_try_declaration {
            let trx = parser.start_transaction();
            debug!(
                "parse_compound_statement: trying declaration parsing at position {}",
                trx.parser.current_idx
            );
            match super::declarations::parse_declaration(trx.parser) {
                Ok(declaration) => {
                    debug!("parse_compound_statement: successfully parsed declaration");
                    block_items.push(declaration);
                    trx.commit();
                }
                Err(decl_error) => {
                    debug!("parse_compound_statement: declaration parsing failed: {:?}", decl_error);
                    declaration_attempt = Some(Err(decl_error));
                }
            }
        }

        // If declaration failed or wasn't attempted, try as statement
        if declaration_attempt.is_some() || !should_try_declaration {
            if declaration_attempt.is_some() {
                debug!(
                    "parse_compound_statement: reset to position {}, trying statement",
                    initial_idx
                );
            } else {
                debug!("parse_compound_statement: not a declaration start, trying statement");
            }

            match parse_statement(parser) {
                Ok(statement) => {
                    debug!("parse_compound_statement: successfully parsed statement");
                    block_items.push(statement);
                }
                Err(stmt_error) => {
                    debug!(
                        "parse_compound_statement: statement parsing also failed: {:?}",
                        stmt_error
                    );
                    // Both declaration and statement parsing failed
                    // Report the declaration error and try to synchronize
                    if let Some(Err(decl_error)) = declaration_attempt {
                        parser.diag.report(decl_error);
                    } else {
                        parser.diag.report(stmt_error);
                    }
                    parser.synchronize();
                }
            }
        }
    }

    let right_brace_token = parser.expect(TokenKind::RightBrace)?;
    let end_loc = right_brace_token.span.end();

    let span = SourceSpan::new(start_loc, end_loc);

    let node = parser.replace_node(dummy, ParsedNodeKind::CompoundStatement(block_items), span);
    Ok((node, end_loc))
}

/// Parse if statement
fn parse_if_statement(parser: &mut Parser) -> Result<ParsedNodeRef, ParseError> {
    let token = parser.expect(TokenKind::If)?;
    let start_loc = token.span.start();

    let condition = parse_parenthesized_expr(parser)?;
    let then_branch = parse_statement(parser)?;

    let else_branch = if parser.accept(TokenKind::Else).is_some() {
        Some(parse_statement(parser)?)
    } else {
        None
    };

    let end_loc = match &else_branch {
        Some(else_stmt) => parser.ast.get_node(*else_stmt).span.end(),
        None => parser.ast.get_node(then_branch).span.end(),
    };

    let span = SourceSpan::new(start_loc, end_loc);

    let if_stmt = ParsedIfStmt {
        condition,
        then_branch,
        else_branch,
    };

    let node = parser.push_node(ParsedNodeKind::If(if_stmt), span);
    Ok(node)
}

/// Parse switch statement
fn parse_switch_statement(parser: &mut Parser) -> Result<ParsedNodeRef, ParseError> {
    let token = parser.expect(TokenKind::Switch)?;
    let start_loc = token.span.start();

    let condition = parse_parenthesized_expr(parser)?;

    debug!("parse_for_statement: parsing body");

    let body = parse_statement(parser)?;

    let end_loc = parser.ast.get_node(body).span.end();

    let span = SourceSpan::new(start_loc, end_loc);

    let node = parser.push_node(ParsedNodeKind::Switch(condition, body), span);
    Ok(node)
}

/// Parse while statement
fn parse_while_statement(parser: &mut Parser) -> Result<ParsedNodeRef, ParseError> {
    let token = parser.expect(TokenKind::While)?;
    let start_loc = token.span.start();

    let condition = parse_parenthesized_expr(parser)?;
    let body = parse_statement(parser)?;

    let end_loc = parser.ast.get_node(body).span.end();

    let span = SourceSpan::new(start_loc, end_loc);

    let while_stmt = ParsedWhileStmt { condition, body };

    let node = parser.push_node(ParsedNodeKind::While(while_stmt), span);
    Ok(node)
}

/// Parse do-while statement
fn parse_do_while_statement(parser: &mut Parser) -> Result<ParsedNodeRef, ParseError> {
    let token = parser.expect(TokenKind::Do)?;
    let start_loc = token.span.start();

    let body = parse_statement(parser)?;

    parser.expect(TokenKind::While)?;
    let condition = parse_parenthesized_expr(parser)?;
    let semicolon_token = parser.expect(TokenKind::Semicolon)?;
    let end_loc = semicolon_token.span.end();

    let span = SourceSpan::new(start_loc, end_loc);

    let node = parser.push_node(ParsedNodeKind::DoWhile(body, condition), span);
    Ok(node)
}

/// Parse for statement
fn parse_for_statement(parser: &mut Parser) -> Result<ParsedNodeRef, ParseError> {
    let token = parser.expect(TokenKind::For)?;
    let start_loc = token.span.start();
    let dummy = parser.push_dummy();

    parser.expect(TokenKind::LeftParen)?;

    debug!("parse_for_statement: parsing initialization");

    // Parse initialization
    let init = if parser.is_token(TokenKind::Semicolon) {
        None
    } else if parser.starts_declaration() {
        debug!("parse_for_statement: parsing declaration in init");
        // Parse declaration specifiers
        let specifiers = parse_declaration_specifiers(parser)?;
        let declarator_start_span = parser.current_token_span_or_empty();
        // Parse declarator
        let declarator = parse_declarator(parser, None)?;
        // Parse initializer if present
        let initializer = if parser.accept(TokenKind::Assign).is_some() {
            Some(super::declaration_core::parse_initializer(parser)?)
        } else {
            None
        };

        let end_span = parser.last_token_span().unwrap_or(declarator_start_span);
        let span = declarator_start_span.merge(end_span);

        let init_declarator = ParsedInitDeclarator {
            declarator,
            initializer,
            span,
        };

        let declaration_data = ParsedDeclarationData {
            specifiers,
            init_declarators: thin_vec![init_declarator],
        };

        // Don't consume semicolon here - it will be consumed by the normal for loop flow
        let span = SourceSpan::new(start_loc, parser.current_token_span()?.end());

        Some(parser.push_node(ParsedNodeKind::Declaration(declaration_data), span))
    } else {
        debug!("parse_for_statement: parsing expression in init");
        Some(parser.parse_expr_min()?)
    };

    parser.expect(TokenKind::Semicolon)?;

    debug!("parse_for_statement: parsing condition");

    // Parse condition
    let condition = if parser.is_token(TokenKind::Semicolon) {
        None
    } else {
        Some(parser.parse_expr_min()?)
    };

    parser.expect(TokenKind::Semicolon)?;

    debug!("parse_for_statement: parsing increment");

    // Parse increment
    let increment = if parser.is_token(TokenKind::RightParen) {
        None
    } else {
        Some(parser.parse_expr_min()?)
    };

    parser.expect(TokenKind::RightParen)?;

    let body = parse_statement(parser)?;

    let end_loc = parser.ast.get_node(body).span.end();

    let span = SourceSpan::new(start_loc, end_loc);

    let for_stmt = ParsedForStmt {
        init,
        condition,
        increment,
        body,
    };

    let node = parser.replace_node(dummy, ParsedNodeKind::For(for_stmt), span);
    Ok(node)
}

/// Parse goto statement
fn parse_goto_statement(parser: &mut Parser) -> Result<ParsedNodeRef, ParseError> {
    let token = parser.expect(TokenKind::Goto)?;
    let start_loc = token.span.start();

    let (label, _) = parser.expect_name()?;

    let semicolon_token = parser.expect(TokenKind::Semicolon)?;
    let end_loc = semicolon_token.span.end();

    let span = SourceSpan::new(start_loc, end_loc);
    let node = parser.push_node(ParsedNodeKind::Goto(label), span);
    Ok(node)
}

/// Parse continue statement
fn parse_continue_statement(parser: &mut Parser) -> Result<ParsedNodeRef, ParseError> {
    let token = parser.expect(TokenKind::Continue)?;
    let start_loc = token.span.start();

    let semicolon_token = parser.expect(TokenKind::Semicolon)?;
    let end_loc = semicolon_token.span.end();

    let span = SourceSpan::new(start_loc, end_loc);

    let node = parser.push_node(ParsedNodeKind::Continue, span);
    Ok(node)
}

/// Parse break statement
fn parse_break_statement(parser: &mut Parser) -> Result<ParsedNodeRef, ParseError> {
    let token = parser.expect(TokenKind::Break)?;
    let start_loc = token.span.start();

    let semicolon_token = parser.expect(TokenKind::Semicolon)?;
    let end_loc = semicolon_token.span.end();

    let span = SourceSpan::new(start_loc, end_loc);

    let node = parser.push_node(ParsedNodeKind::Break, span);
    Ok(node)
}

/// Parse return statement
fn parse_return_statement(parser: &mut Parser) -> Result<ParsedNodeRef, ParseError> {
    let token = parser.expect(TokenKind::Return)?;
    let start_loc = token.span.start();

    let value = if parser.is_token(TokenKind::Semicolon) {
        None
    } else {
        let expr = parser.parse_expr_min()?;
        Some(expr)
    };

    let semicolon_token = parser.expect(TokenKind::Semicolon)?;
    let end_loc = semicolon_token.span.end();

    let span = SourceSpan::new(start_loc, end_loc);

    let node = parser.push_node(ParsedNodeKind::Return(value), span);
    Ok(node)
}

/// Parse empty statement
fn parse_empty_statement(parser: &mut Parser) -> Result<ParsedNodeRef, ParseError> {
    let token = parser.expect(TokenKind::Semicolon)?;
    let span = token.span;
    let node = parser.push_node(ParsedNodeKind::EmptyStatement, span);
    Ok(node)
}

/// Parse case statement (including GNU case ranges)
fn parse_case_statement(parser: &mut Parser) -> Result<ParsedNodeRef, ParseError> {
    let token = parser.expect(TokenKind::Case)?;
    let start_loc = token.span.start();

    let start_expr = parser.parse_expr_min()?;

    // Check for GNU case range extension: case 1 ... 10:
    let (end_expr, is_range) = if parser.accept(TokenKind::Ellipsis).is_some() {
        let end_expr = parser.parse_expr_min()?;
        (Some(end_expr), true)
    } else {
        (None, false)
    };

    parser.expect(TokenKind::Colon)?;

    let statement = parse_statement(parser)?;

    let end_loc = parser.ast.get_node(statement).span.end();

    let span = SourceSpan::new(start_loc, end_loc);

    let node = if is_range {
        parser.push_node(
            ParsedNodeKind::CaseRange(start_expr, end_expr.unwrap(), statement),
            span,
        )
    } else {
        parser.push_node(ParsedNodeKind::Case(start_expr, statement), span)
    };
    Ok(node)
}

/// Parse default statement
fn parse_default_statement(parser: &mut Parser) -> Result<ParsedNodeRef, ParseError> {
    let token = parser.expect(TokenKind::Default)?;
    let start_loc = token.span.start();

    parser.expect(TokenKind::Colon)?;

    let statement = parse_statement(parser)?;
    let end_loc = parser.ast.get_node(statement).span.end();

    let span = SourceSpan::new(start_loc, end_loc);

    let node = parser.push_node(ParsedNodeKind::Default(statement), span);
    Ok(node)
}

/// Parse label statement
fn parse_label_statement(parser: &mut Parser, label_symbol: NameId) -> Result<ParsedNodeRef, ParseError> {
    let token = parser.advance().unwrap(); // consume the identifier
    let start_loc = token.span.start();

    parser.expect(TokenKind::Colon)?; // consume the colon

    let statement = parse_statement(parser)?;
    let end_loc = parser.ast.get_node(statement).span.end();

    let span = SourceSpan::new(start_loc, end_loc);

    // ParsedNodeKind::Label(NameId, ParsedNodeRef)
    let node = parser.push_node(ParsedNodeKind::Label(label_symbol, statement), span);
    Ok(node)
}

/// Parse expression statement
fn parse_expression_statement(parser: &mut Parser) -> Result<ParsedNodeRef, ParseError> {
    let start_loc = parser.current_token_span()?.start();
    let dummy = parser.push_dummy();

    let (semi, expr) = if let Some(token) = parser.accept(TokenKind::Semicolon) {
        (token, None)
    } else {
        let expr = parser.parse_expr_min()?;
        (parser.expect(TokenKind::Semicolon)?, Some(expr))
    };

    let end_loc = semi.span.end();
    let span = SourceSpan::new(start_loc, end_loc);

    let node = parser.replace_node(dummy, ParsedNodeKind::ExpressionStatement(expr), span);
    Ok(node)
}
