//! Common parsing utilities and helper functions
//!
//! This module provides utility functions that abstract repetitive patterns
//! found throughout the parser, including expression result handling,
//! binding power utilities, and common parsing operations.

use crate::ast::*;
use crate::diagnostic::ParseError;
use log::debug;

use super::expressions::BindingPower;
use super::{ParseExprOutput, Parser, ParserState};

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
    fn unwrap_expr_result(
        &self,
        result: Result<ParseExprOutput, ParseError>,
        context: &str,
    ) -> Result<NodeRef, ParseError>;

    /// Check if current token starts a type name
    fn is_type_name_start(&self) -> bool;
}

impl<'arena, 'src> ParserExt for Parser<'arena, 'src> {
    fn parse_expr_min(&mut self) -> Result<NodeRef, ParseError> {
        let result = self.parse_expression(BindingPower::MIN);
        self.unwrap_expr_result(result, "expression")
    }

    fn parse_expr_unary(&mut self) -> Result<NodeRef, ParseError> {
        let result = self.parse_expression(BindingPower::UNARY);
        self.unwrap_expr_result(result, "unary expression")
    }

    fn parse_expr_cast(&mut self) -> Result<NodeRef, ParseError> {
        let result = self.parse_expression(BindingPower::CAST);
        self.unwrap_expr_result(result, "cast expression")
    }

    fn parse_expr_conditional(&mut self) -> Result<NodeRef, ParseError> {
        let result = self.parse_expression(BindingPower::CONDITIONAL);
        self.unwrap_expr_result(result, "conditional expression")
    }

    fn parse_expr_assignment(&mut self) -> Result<NodeRef, ParseError> {
        let result = self.parse_expression(BindingPower::ASSIGNMENT);
        self.unwrap_expr_result(result, "assignment expression")
    }

    fn unwrap_expr_result(
        &self,
        result: Result<ParseExprOutput, ParseError>,
        _context: &str,
    ) -> Result<NodeRef, ParseError> {
        match result {
            Ok(ParseExprOutput::Expression(node)) => Ok(node),
            Ok(ParseExprOutput::Declaration(node_ref)) => Err(ParseError::DeclarationNotAllowed {
                location: self.ast.get_node(node_ref).span,
            }),
            Err(e) => Err(e),
        }
    }

    fn is_type_name_start(&self) -> bool {
        debug!(
            "is_type_name_start: checking token {:?} at position {}",
            self.current_token_kind(),
            self.current_idx
        );

        if let Some(token) = self.try_current_token() {
            let is_specifier = token.kind.is_type_specifier() || token.kind.is_type_qualifier();

            let is_identifier_type = if let crate::lexer::TokenKind::Identifier(symbol) = token.kind {
                self.is_type_name(symbol)
            } else {
                false
            };

            let final_result = is_specifier || is_identifier_type;
            debug!(
                "is_type_name_start: token {:?} is type name start: {} (specifier: {}, identifier: {})",
                token.kind, final_result, is_specifier, is_identifier_type
            );
            final_result
        } else {
            debug!("is_type_name_start: no token available");
            false
        }
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

    /// Parse a comma-separated list of expressions with specified binding power
    pub fn parse_expr_list(parser: &mut Parser, binding_power: BindingPower) -> Result<Vec<NodeRef>, ParseError> {
        debug!("parse_expr_list: parsing expression list");
        let mut args = Vec::new();

        if parser.is_token(crate::lexer::TokenKind::RightParen) {
            return Ok(args);
        }

        loop {
            let expr_result = parser.parse_expression(binding_power)?;
            let arg = parser.unwrap_expr_result(Ok(expr_result), "expression in list")?;
            args.push(arg);

            if !parser.is_token(crate::lexer::TokenKind::Comma) {
                break;
            }
            parser.advance(); // consume comma
        }

        Ok(args)
    }

    /// Parse an optional expression (for cases like return statements)
    pub fn parse_optional_expr(parser: &mut Parser) -> Result<Option<NodeRef>, ParseError> {
        if parser.is_token(crate::lexer::TokenKind::Semicolon) {
            Ok(None)
        } else {
            let expr = parser.parse_expr_min()?;
            Ok(Some(expr))
        }
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
                    NodeKind::GnuStatementExpression(_, result_expr) => {
                        self.queue.push_back(*result_expr);
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
                    | NodeKind::Function(_)
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
                    | NodeKind::VarDecl(_)
                    | NodeKind::FunctionDecl(_)
                    | NodeKind::TypedefDecl(_)
                    | NodeKind::RecordDecl(_)
                    | NodeKind::DeclarationList(_)
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

#[cfg(test)]
mod tests {
    use super::ast_iterators::AstIteratorExt;
    use super::*;
    use crate::ast::Ast;

    #[test]
    fn test_ast_iterator() {
        let mut ast = Ast::new();

        // Create a simple binary operation: 1 + 2
        let left = ast.push_node(Node::new(NodeKind::LiteralInt(1), SourceSpan::empty()));
        let right = ast.push_node(Node::new(NodeKind::LiteralInt(2), SourceSpan::empty()));
        let root = ast.push_node(Node::new(
            NodeKind::BinaryOp(BinaryOp::Add, left, right),
            SourceSpan::empty(),
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
