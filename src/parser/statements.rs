//! Statement parsing module
//!
//! This module handles all statement parsing logic, including control flow
//! statements, compound statements, and expression statements.

use super::Parser;
use super::utils::ParserExt;
use crate::ast::*;
use crate::diagnostic::ParseError;
use crate::lexer::TokenKind;
use crate::parser::declaration_core::parse_declaration_specifiers;
use crate::parser::declarator::parse_declarator;
use crate::source_manager::{SourceLoc, SourceSpan};
use log::debug;
use symbol_table::GlobalSymbol as Symbol;
use thin_vec::thin_vec;

/// Parse a statement
pub fn parse_statement(parser: &mut Parser) -> Result<NodeRef, ParseError> {
    let token = parser.try_current_token().ok_or_else(|| ParseError::SyntaxError {
        message: "Expected statement".to_string(),
        location: SourceSpan::empty(),
    })?;

    // Check for label: identifier :
    if let TokenKind::Identifier(label_symbol) = token.kind
        && let Some(next_token) = parser.peek_token(0)
        && next_token.kind == TokenKind::Colon
    {
        return parse_label_statement(parser, label_symbol);
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
pub fn parse_compound_statement(parser: &mut Parser) -> Result<(NodeRef, SourceLoc), ParseError> {
    let start_span = parser.current_token()?.location.start;
    parser.expect(TokenKind::LeftBrace)?;

    let mut block_items = Vec::new();

    while !parser.is_token(TokenKind::RightBrace) {
        let initial_idx = parser.current_idx;

        debug!(
            "parse_compound_statement: parsing block item, current token {:?}, position {}",
            parser.current_token_kind(),
            initial_idx
        );

        // Try parsing as declaration first, but only if it looks like a declaration start
        let should_try_declaration = parser.is_declaration_start();
        let mut declaration_attempt: Option<Result<NodeRef, ParseError>> = None;

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
                        parser.diag.report_parse_error(decl_error);
                    } else {
                        parser.diag.report_parse_error(stmt_error);
                    }
                    parser.synchronize();
                }
            }
        }
    }

    let right_brace_token = parser.expect(TokenKind::RightBrace)?;
    let end_span = right_brace_token.location.end;

    let span = SourceSpan::new(start_span, end_span);

    let node = parser.push_node(NodeKind::CompoundStatement(block_items), span);
    Ok((node, end_span))
}

/// Parse if statement
fn parse_if_statement(parser: &mut Parser) -> Result<NodeRef, ParseError> {
    let start_span = parser.current_token()?.location.start;
    parser.expect(TokenKind::If)?;
    parser.expect(TokenKind::LeftParen)?;

    let condition = parser.parse_expr_min()?;

    parser.expect(TokenKind::RightParen)?;

    let then_branch = parse_statement(parser)?;

    let else_branch = if parser.accept(TokenKind::Else).is_some() {
        Some(parse_statement(parser)?)
    } else {
        None
    };

    let end_span = match &else_branch {
        Some(else_stmt) => parser.ast.get_node(*else_stmt).span.end,
        None => parser.ast.get_node(then_branch).span.end,
    };

    let span = SourceSpan::new(start_span, end_span);

    let if_stmt = IfStmt {
        condition,
        then_branch,
        else_branch,
    };

    let node = parser.push_node(NodeKind::If(if_stmt), span);
    Ok(node)
}

/// Parse switch statement
fn parse_switch_statement(parser: &mut Parser) -> Result<NodeRef, ParseError> {
    let start_span = parser.current_token()?.location.start;
    parser.expect(TokenKind::Switch)?;
    parser.expect(TokenKind::LeftParen)?;

    let condition = parser.parse_expr_min()?;

    parser.expect(TokenKind::RightParen)?;

    debug!("parse_for_statement: parsing body");

    let body = parse_statement(parser)?;

    let end_span = parser.ast.get_node(body).span.end;

    let span = SourceSpan::new(start_span, end_span);

    let node = parser.push_node(NodeKind::Switch(condition, body), span);
    Ok(node)
}

/// Parse while statement
fn parse_while_statement(parser: &mut Parser) -> Result<NodeRef, ParseError> {
    let start_span = parser.current_token()?.location.start;
    parser.expect(TokenKind::While)?;
    parser.expect(TokenKind::LeftParen)?;

    let condition = parser.parse_expr_min()?;

    parser.expect(TokenKind::RightParen)?;

    let body = parse_statement(parser)?;

    let end_span = parser.ast.get_node(body).span.end;

    let span = SourceSpan::new(start_span, end_span);

    let while_stmt = WhileStmt { condition, body };

    let node = parser.push_node(NodeKind::While(while_stmt), span);
    Ok(node)
}

/// Parse do-while statement
fn parse_do_while_statement(parser: &mut Parser) -> Result<NodeRef, ParseError> {
    let start_span = parser.current_token()?.location.start;
    parser.expect(TokenKind::Do)?;

    let body = parse_statement(parser)?;

    parser.expect(TokenKind::While)?;
    parser.expect(TokenKind::LeftParen)?;

    let condition = parser.parse_expr_min()?;

    parser.expect(TokenKind::RightParen)?;
    let semicolon_token = parser.expect(TokenKind::Semicolon)?;
    let end_span = semicolon_token.location.end;

    let span = SourceSpan::new(start_span, end_span);

    let node = parser.push_node(NodeKind::DoWhile(body, condition), span);
    Ok(node)
}

/// Parse for statement
fn parse_for_statement(parser: &mut Parser) -> Result<NodeRef, ParseError> {
    let start_span = parser.current_token()?.location.start;
    parser.expect(TokenKind::For)?;
    parser.expect(TokenKind::LeftParen)?;

    debug!("parse_for_statement: parsing initialization");

    // Parse initialization
    let init = if parser.is_token(TokenKind::Semicolon) {
        None
    } else if parser.is_declaration_start() {
        debug!("parse_for_statement: parsing declaration in init");
        // Parse declaration specifiers
        let specifiers = parse_declaration_specifiers(parser)?;
        // Parse declarator
        let declarator = parse_declarator(parser, None)?;
        // Parse initializer if present
        let initializer = if parser.accept(TokenKind::Assign).is_some() {
            Some(super::declaration_core::parse_initializer(parser)?)
        } else {
            None
        };

        let init_declarator = InitDeclarator {
            declarator,
            initializer,
        };

        let declaration_data = DeclarationData {
            specifiers,
            init_declarators: thin_vec![init_declarator],
        };

        // Don't consume semicolon here - it will be consumed by the normal for loop flow
        let span = SourceSpan::new(start_span, parser.current_token().unwrap().location.end);

        Some(parser.push_node(NodeKind::Declaration(declaration_data), span))
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

    let end_span = parser.ast.get_node(body).span.end;

    let span = SourceSpan::new(start_span, end_span);

    let for_stmt = ForStmt {
        init,
        condition,
        increment,
        body,
    };

    let node = parser.push_node(NodeKind::For(for_stmt), span);
    Ok(node)
}

/// Parse goto statement
fn parse_goto_statement(parser: &mut Parser) -> Result<NodeRef, ParseError> {
    let start_token = parser.expect(TokenKind::Goto)?;
    let start_span = start_token.location.start;

    let (label, _) = parser.expect_name()?;

    let semicolon_token = parser.expect(TokenKind::Semicolon)?;
    let end_span = semicolon_token.location.end;

    let span = SourceSpan::new(start_span, end_span);
    let node = parser.push_node(NodeKind::Goto(label), span);
    Ok(node)
}

/// Parse continue statement
fn parse_continue_statement(parser: &mut Parser) -> Result<NodeRef, ParseError> {
    let start_span = parser.current_token()?.location.start;
    parser.expect(TokenKind::Continue)?;
    let semicolon_token = parser.expect(TokenKind::Semicolon)?;
    let end_span = semicolon_token.location.end;

    let span = SourceSpan::new(start_span, end_span);

    let node = parser.push_node(NodeKind::Continue, span);
    Ok(node)
}

/// Parse break statement
fn parse_break_statement(parser: &mut Parser) -> Result<NodeRef, ParseError> {
    let start_span = parser.current_token()?.location.start;

    parser.expect(TokenKind::Break)?;
    let semicolon_token = parser.expect(TokenKind::Semicolon)?;
    let end_span = semicolon_token.location.end;

    let span = SourceSpan::new(start_span, end_span);

    let node = parser.push_node(NodeKind::Break, span);
    Ok(node)
}

/// Parse return statement
fn parse_return_statement(parser: &mut Parser) -> Result<NodeRef, ParseError> {
    let start_span = parser.current_token()?.location.start;

    let _return_token = parser.expect(TokenKind::Return)?;
    debug!("parse_return_statement: parsing return expression");

    let value = if parser.is_token(TokenKind::Semicolon) {
        debug!("parse_return_statement: empty return");
        None
    } else {
        debug!(
            "parse_return_statement: parsing return expression with current token {:?}",
            parser.current_token_kind()
        );
        let expr = parser.parse_expr_min()?;
        debug!("parse_return_statement: parsed expression successfully");
        Some(expr)
    };

    let semicolon_token = parser.expect(TokenKind::Semicolon)?;
    let end_span = semicolon_token.location.end;

    let span = SourceSpan::new(start_span, end_span);

    let node = parser.push_node(NodeKind::Return(value), span);
    Ok(node)
}

/// Parse empty statement
fn parse_empty_statement(parser: &mut Parser) -> Result<NodeRef, ParseError> {
    let start_span = parser.current_token()?.location.start;

    let semicolon_token = parser.expect(TokenKind::Semicolon)?;
    let end_span = semicolon_token.location.end;

    let span = SourceSpan::new(start_span, end_span);

    let node = parser.push_node(NodeKind::EmptyStatement, span);
    Ok(node)
}

/// Parse case statement (including GNU case ranges)
fn parse_case_statement(parser: &mut Parser) -> Result<NodeRef, ParseError> {
    let start_span = parser.current_token()?.location.start;

    parser.expect(TokenKind::Case)?;

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

    let end_span = parser.ast.get_node(statement).span.end;

    let span = SourceSpan::new(start_span, end_span);

    let node = if is_range {
        parser.push_node(NodeKind::CaseRange(start_expr, end_expr.unwrap(), statement), span)
    } else {
        parser.push_node(NodeKind::Case(start_expr, statement), span)
    };
    Ok(node)
}

/// Parse default statement
fn parse_default_statement(parser: &mut Parser) -> Result<NodeRef, ParseError> {
    let start_span = parser.current_token()?.location.start;

    parser.expect(TokenKind::Default)?;
    parser.expect(TokenKind::Colon)?;

    let statement = parse_statement(parser)?;
    let end_span = parser.ast.get_node(statement).span.end;

    let span = SourceSpan::new(start_span, end_span);

    let node = parser.push_node(NodeKind::Default(statement), span);
    Ok(node)
}

/// Parse label statement
fn parse_label_statement(parser: &mut Parser, label_symbol: Symbol) -> Result<NodeRef, ParseError> {
    let start_span = parser.current_token()?.location.start;

    parser.advance(); // consume the identifier
    parser.expect(TokenKind::Colon)?; // consume the colon

    let statement = parse_statement(parser)?;
    let end_span = parser.ast.get_node(statement).span.end;

    let span = SourceSpan::new(start_span, end_span);

    let node = parser.push_node(NodeKind::Label(label_symbol, statement), span);
    Ok(node)
}

/// Parse expression statement
fn parse_expression_statement(parser: &mut Parser) -> Result<NodeRef, ParseError> {
    let start_span = parser.current_token()?.location.start;

    let (semi, expr) = if let Some(token) = parser.accept(TokenKind::Semicolon) {
        (token, None)
    } else {
        let expr = parser.parse_expr_min()?;
        (parser.expect(TokenKind::Semicolon)?, Some(expr))
    };

    let end_span = semi.location.end;
    let span = SourceSpan::new(start_span, end_span);

    let node = parser.push_node(NodeKind::ExpressionStatement(expr), span);
    Ok(node)
}
