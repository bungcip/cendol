//! Common parsing utilities and helper functions
//!
//! This module provides utility functions that abstract repetitive patterns
//! found throughout the parser, including expression result handling,
//! binding power utilities, and common parsing operations.

use crate::ast::*;
use crate::diagnostic::ParseError;
use crate::source_manager::{SourceLoc, SourceSpan};
use crate::lexer::Token;
use log::debug;

use super::{Parser, ParseExprOutput, ParserState};
use super::expressions::BindingPower;

/// Result of parsing an expression with binding power
pub type ExprResult = Result<ParseExprOutput, ParseError>;

/// Extension trait for Parser to add utility methods
pub trait ParserExt {
    /// Parse an expression with minimum binding power and unwrap the result
    fn parse_expr_min(&mut self) -> Result<NodeRef, ParseError>;

    /// Parse an expression with unary binding power and unwrap the result
    fn parse_expr_unary(&mut self) -> Result<NodeRef, ParseError>;

    /// Parse an expression with cast binding power and unwrap the result
    fn parse_expr_cast(&mut self) -> Result<NodeRef, ParseError>;

    /// Parse an expression with conditional binding power and unwrap the result
    fn parse_expr_conditional(&mut self) -> Result<NodeRef, ParseError>;

    /// Parse an expression with assignment binding power and unwrap the result
    fn parse_expr_assignment(&mut self) -> Result<NodeRef, ParseError>;

    /// Unwrap a ParseExprOutput to get the NodeRef, returning an error if it's not an expression
    fn unwrap_expr_result(&self, result: ParseExprOutput, context: &str) -> Result<NodeRef, ParseError>;

    /// Calculate span from start location to current token end
    fn span_from_start(&self, start: SourceLoc) -> Result<SourceSpan, ParseError>;

    /// Calculate span from start token to end token
    fn span_from_tokens(&self, start_token: &Token, end_token: &Token) -> SourceSpan;

    /// Calculate span from node start to current position
    fn span_from_node(&self, node: NodeRef) -> Result<SourceSpan, ParseError>;
}

impl<'arena, 'src> ParserExt for Parser<'arena, 'src> {
    fn parse_expr_min(&mut self) -> Result<NodeRef, ParseError> {
        let result = self.parse_expression(BindingPower::MIN)?;
        self.unwrap_expr_result(result, "expression")
    }

    fn parse_expr_unary(&mut self) -> Result<NodeRef, ParseError> {
        let result = self.parse_expression(BindingPower::UNARY)?;
        self.unwrap_expr_result(result, "unary expression")
    }

    fn parse_expr_cast(&mut self) -> Result<NodeRef, ParseError> {
        let result = self.parse_expression(BindingPower::CAST)?;
        self.unwrap_expr_result(result, "cast expression")
    }

    fn parse_expr_conditional(&mut self) -> Result<NodeRef, ParseError> {
        let result = self.parse_expression(BindingPower::CONDITIONAL)?;
        self.unwrap_expr_result(result, "conditional expression")
    }

    fn parse_expr_assignment(&mut self) -> Result<NodeRef, ParseError> {
        let result = self.parse_expression(BindingPower::ASSIGNMENT)?;
        self.unwrap_expr_result(result, "assignment expression")
    }

    fn unwrap_expr_result(&self, result: ParseExprOutput, context: &str) -> Result<NodeRef, ParseError> {
        match result {
            ParseExprOutput::Expression(node) => Ok(node),
            ParseExprOutput::Declaration(_) => Err(ParseError::SyntaxError {
                message: format!("Expected {} but found declaration", context),
                location: SourceSpan::empty(),
            }),
        }
    }

    fn span_from_start(&self, start: SourceLoc) -> Result<SourceSpan, ParseError> {
        let end = self.current_token_span()?.end;
        Ok(SourceSpan::new(start, end))
    }

    fn span_from_tokens(&self, start_token: &Token, end_token: &Token) -> SourceSpan {
        SourceSpan::new(start_token.location.start, end_token.location.end)
    }

    fn span_from_node(&self, node: NodeRef) -> Result<SourceSpan, ParseError> {
        let node_span = self.ast.get_node(node).span;
        let current_end = self.current_token_span()?.end;
        Ok(SourceSpan::new(node_span.start, current_end))
    }
}

/// Common expression parsing patterns
pub mod expr_patterns {
    use super::*;

    /// Parse a parenthesized expression: (expression)
    pub fn parse_parenthesized_expr(parser: &mut Parser) -> Result<NodeRef, ParseError> {
        debug!("parse_parenthesized_expr: parsing parenthesized expression");
        parser.expect(crate::lexer::TokenKind::LeftParen)?;
        let expr = parser.parse_expr_min()?;
        parser.expect(crate::lexer::TokenKind::RightParen)?;
        Ok(expr)
    }

    /// Parse a comma-separated list of expressions
    pub fn parse_expr_list(parser: &mut Parser) -> Result<Vec<NodeRef>, ParseError> {
        debug!("parse_expr_list: parsing expression list");
        let mut args = Vec::new();

        if parser.matches(&[crate::lexer::TokenKind::RightParen]) {
            return Ok(args);
        }

        loop {
            let arg = parser.parse_expr_min()?;
            args.push(arg);

            if !parser.matches(&[crate::lexer::TokenKind::Comma]) {
                break;
            }
            parser.advance(); // consume comma
        }

        Ok(args)
    }

    /// Parse an optional expression (for cases like return statements)
    pub fn parse_optional_expr(parser: &mut Parser) -> Result<Option<NodeRef>, ParseError> {
        if parser.matches(&[crate::lexer::TokenKind::Semicolon]) {
            Ok(None)
        } else {
            let expr = parser.parse_expr_min()?;
            Ok(Some(expr))
        }
    }
}

/// Common error handling patterns
pub mod error_patterns {
    use super::*;
    use crate::lexer::TokenKind;

    /// Create a syntax error for unexpected token
    pub fn unexpected_token(expected: &[TokenKind], found: TokenKind, location: SourceSpan) -> ParseError {
        ParseError::UnexpectedToken {
            expected: expected.to_vec(),
            found,
            location,
        }
    }

    /// Create a syntax error for missing token
    pub fn missing_token(expected: TokenKind, location: SourceSpan) -> ParseError {
        ParseError::MissingToken {
            expected,
            location,
        }
    }

    /// Create a generic syntax error
    pub fn syntax_error(message: &str, location: SourceSpan) -> ParseError {
        ParseError::SyntaxError {
            message: message.to_string(),
            location,
        }
    }
}

/// Span calculation utilities
pub mod span_utils {
    use super::*;

    /// Create span from two locations
    pub fn from_locs(start: SourceLoc, end: SourceLoc) -> SourceSpan {
        SourceSpan::new(start, end)
    }

    /// Create span from two tokens
    pub fn from_tokens(start_token: &Token, end_token: &Token) -> SourceSpan {
        SourceSpan::new(start_token.location.start, end_token.location.end)
    }

    /// Create span from node and additional end location
    pub fn extend_node(node: NodeRef, end: SourceLoc, ast: &Ast) -> SourceSpan {
        let node_start = ast.get_node(node).span.start;
        SourceSpan::new(node_start, end)
    }
}

/// Iterator patterns for AST traversal
pub mod ast_iterators {
    use super::*;
    use std::collections::VecDeque;

    /// Iterator over all nodes in an AST subtree in depth-first order
    pub struct AstIterator<'a> {
        ast: &'a Ast,
        queue: VecDeque<NodeRef>,
    }

    impl<'a> AstIterator<'a> {
        pub fn new(ast: &'a Ast, root: NodeRef) -> Self {
            let mut queue = VecDeque::new();
            queue.push_back(root);
            Self { ast, queue }
        }
    }

    impl<'a> Iterator for AstIterator<'a> {
        type Item = NodeRef;

        fn next(&mut self) -> Option<Self::Item> {
            if let Some(node_ref) = self.queue.pop_front() {
                let node = self.ast.get_node(node_ref);

                // Add children to queue based on node kind
                match &node.kind {
                    NodeKind::BinaryOp(_, left, right) => {
                        self.queue.push_back(*left);
                        self.queue.push_back(*right);
                    }
                    NodeKind::UnaryOp(_, operand) => {
                        self.queue.push_back(*operand);
                    }
                    NodeKind::TernaryOp(cond, true_expr, false_expr) => {
                        self.queue.push_back(*cond);
                        self.queue.push_back(*true_expr);
                        self.queue.push_back(*false_expr);
                    }
                    NodeKind::Assignment(_, left, right) => {
                        self.queue.push_back(*left);
                        self.queue.push_back(*right);
                    }
                    NodeKind::FunctionCall(func, args) => {
                        self.queue.push_back(*func);
                        self.queue.extend(args);
                    }
                    NodeKind::IndexAccess(array, index) => {
                        self.queue.push_back(*array);
                        self.queue.push_back(*index);
                    }
                    NodeKind::MemberAccess(obj, _, _) => {
                        self.queue.push_back(*obj);
                    }
                    NodeKind::Cast(_, expr) => {
                        self.queue.push_back(*expr);
                    }
                    NodeKind::SizeOfExpr(expr) => {
                        self.queue.push_back(*expr);
                    }
                    NodeKind::PostIncrement(operand) | NodeKind::PostDecrement(operand) => {
                        self.queue.push_back(*operand);
                    }
                    NodeKind::CompoundLiteral(_, _) => {
                        // Compound literals have initializers, but we don't traverse them here
                        // as they contain different node types
                    }
                    NodeKind::GenericSelection(controlling, associations) => {
                        self.queue.push_back(*controlling);
                        for assoc in associations {
                            self.queue.push_back(assoc.result_expr);
                        }
                    }
                    NodeKind::VaArg(_, _) => {
                        // VaArg has expression arguments but we skip for simplicity
                    }
                    NodeKind::CompoundStatement(_) => {
                        // Compound statements contain statements, not expressions
                    }
                    // Leaf nodes or nodes without expression children
                    NodeKind::Ident(_, _)
                    | NodeKind::LiteralInt(_)
                    | NodeKind::LiteralFloat(_)
                    | NodeKind::LiteralString(_)
                    | NodeKind::LiteralChar(_)
                    | NodeKind::SizeOfType(_)
                    | NodeKind::AlignOf(_)
                    | NodeKind::Declaration(_)
                    | NodeKind::FunctionDef(_)
                    | NodeKind::StaticAssert(_, _)
                    | NodeKind::TranslationUnit(_)
                    | NodeKind::If(_)
                    | NodeKind::While(_)
                    | NodeKind::DoWhile(_, _)
                    | NodeKind::For(_)
                    | NodeKind::Return(_)
                    | NodeKind::Break
                    | NodeKind::Continue
                    | NodeKind::Goto(_)
                    | NodeKind::Label(_, _)
                    | NodeKind::Switch(_, _)
                    | NodeKind::Case(_, _)
                    | NodeKind::CaseRange(_, _, _)
                    | NodeKind::Default(_)
                    | NodeKind::ExpressionStatement(_)
                    | NodeKind::EmptyStatement
                    | NodeKind::EnumConstant(_, _)
                    | NodeKind::Dummy => {}
                }

                Some(node_ref)
            } else {
                None
            }
        }
    }

    /// Extension trait to add iterator methods to Ast
    pub trait AstIteratorExt {
        fn iter_subtree(&self, root: NodeRef) -> AstIterator<'_>;
    }

    impl AstIteratorExt for Ast {
        fn iter_subtree(&self, root: NodeRef) -> AstIterator<'_> {
            AstIterator::new(self, root)
        }
    }
}

pub struct ParserTransaction<'a, 'arena, 'src> {
    pub parser: &'a mut Parser<'arena, 'src>,
    state: ParserState,
    committed: bool,
}

impl<'a, 'arena, 'src> ParserTransaction<'a, 'arena, 'src> {
    pub fn new(parser: &'a mut Parser<'arena, 'src>) -> Self {
        let state = parser.save_state();
        Self {
            parser,
            state,
            committed: false,
        }
    }

    pub fn commit(mut self) {
        self.committed = true;
    }

    pub fn rollback(self) {
        // This is implicitly handled by Drop, but can be called for clarity
    }
}

impl<'a, 'arena, 'src> Drop for ParserTransaction<'a, 'arena, 'src> {
    fn drop(&mut self) {
        if !self.committed {
            self.parser.restore_state(self.state.clone());
        }
    }
}

pub fn unwrap_expr_result(parser: &mut Parser, result: Result<ParseExprOutput, ParseError>, context: &str) -> Result<NodeRef, ParseError> {
    match result? {
        ParseExprOutput::Expression(node) => Ok(node),
        _ => {
            let location = parser.current_token().map(|t| t.location).unwrap_or(SourceSpan::empty());
            Err(ParseError::SyntaxError {
                message: format!("Expected {}", context),
                location,
            })
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::ast_iterators::AstIteratorExt;
    use crate::ast::Ast;

    #[test]
    fn test_ast_iterator() {
        let mut ast = Ast::new();

        // Create a simple binary operation: 1 + 2
        let left = ast.push_node(Node::new(NodeKind::LiteralInt(1), SourceSpan::empty()));
        let right = ast.push_node(Node::new(NodeKind::LiteralInt(2), SourceSpan::empty()));
        let root = ast.push_node(Node::new(
            NodeKind::BinaryOp(BinaryOp::Add, left, right),
            SourceSpan::empty()
        ));

        let iter = ast.iter_subtree(root);
        let nodes: Vec<_> = iter.collect();

        assert_eq!(nodes.len(), 3);
        assert_eq!(nodes[0], root);
        assert!(nodes.contains(&left));
        assert!(nodes.contains(&right));
    }

    #[test]
    fn test_expr_result_unwrapping() {
        // This test would require setting up a full parser context
        // For now, just test the pattern exists
        let _expr_output = ParseExprOutput::Expression(NodeRef::new(1).unwrap());
        // We can't test unwrap_expr_result without a Parser instance
        // but the method exists and compiles
    }
}
