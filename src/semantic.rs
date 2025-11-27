//! Semantic analysis module.
//!
//! This module provides comprehensive semantic analysis for C11 code, including:
//! - Symbol collection and scope management
//! - Name resolution
//! - Type checking
//! - Semantic validation
//!
//! The analysis is performed in distinct phases using the visitor pattern
//! for clean separation of concerns and maintainable code.

pub mod symbol_table;
pub mod name_resolver;
pub mod type_checker;
pub mod utils;
pub mod visitor;

// Re-export key types for public API
pub use symbol_table::{ScopeId, ScopeKind, Scope, SymbolTable};
pub use name_resolver::NameResolver;
pub use type_checker::TypeChecker;

use bitvec::prelude::*;
use log::debug;

use crate::ast::*;
use crate::diagnostic::{DiagnosticEngine, SemanticWarning};

/// Output of semantic analysis
#[derive(Debug)]
pub struct SemanticOutput {
    pub diagnostics: Vec<crate::diagnostic::Diagnostic>,
}

/// Main semantic analyzer - orchestrates all phases
pub struct SemanticAnalyzer<'arena, 'src> {
    ast: &'arena mut Ast,
    diag: &'src mut DiagnosticEngine,
    pub symbol_table: SymbolTable,
    pub scope_stack: Vec<ScopeId>,
}

impl<'arena, 'src> SemanticAnalyzer<'arena, 'src> {
    pub fn new(ast: &'arena mut Ast, diag: &'src mut DiagnosticEngine) -> Self {
        SemanticAnalyzer {
            ast,
            diag,
            symbol_table: SymbolTable::new(),
            scope_stack: vec![ScopeId::GLOBAL],
        }
    }

    pub fn analyze(&mut self) -> SemanticOutput {
        debug!(
            "Starting semantic analysis with {} nodes",
            self.ast.nodes.len()
        );

        // Phase 1: Collect symbols
        self.collect_symbols();

        // Phase 2: Resolve names
        self.resolve_names();

        // Phase 3: Type checking (placeholder for now)
        self.check_types();

        // Return diagnostics
        SemanticOutput {
            diagnostics: self.diag.diagnostics.clone(),
        }
    }

    fn collect_symbols(&mut self) {
        // Check if we have a root node to start traversal from
        let Some(_root_node) = self.ast.get_root_node() else {
            debug!("No root node found, skipping symbol collection");
            return;
        };

        // Get the root node reference for stack-based traversal
        let _root_node_ref = self.ast.root.unwrap();

        debug!(
            "Starting symbol collection from root node: {}",
            _root_node_ref.get()
        );

        // Collect function definitions and ONLY global declarations (top-level)
        let mut function_defs = Vec::new();
        let mut global_declarations = Vec::new();

        // Get the translation unit children to identify top-level items
        let root_node_children = self.get_child_nodes(_root_node_ref);
        debug!(
            "Translation unit has {} top-level items",
            root_node_children.len()
        );

        for top_level_node_ref in &root_node_children {
            let node = self.ast.get_node(*top_level_node_ref);

            match &node.kind {
                NodeKind::FunctionDef(func_def) => {
                    debug!(
                        "Found top-level function definition at node {}",
                        top_level_node_ref.get()
                    );
                    function_defs.push((*top_level_node_ref, func_def.clone(), node.span));
                }
                NodeKind::Declaration(decl) => {
                    debug!(
                        "Found top-level declaration at node {} with {} declarators",
                        top_level_node_ref.get(),
                        decl.init_declarators.len()
                    );
                    global_declarations.push((*top_level_node_ref, decl.clone(), node.span));
                }
                _ => {
                    debug!(
                        "Skipping non-declaration, non-function top-level item: {:?}",
                        std::mem::discriminant(&node.kind)
                    );
                }
            }
        }

        debug!(
            "Symbol collection: found {} top-level function definitions and {} top-level declarations",
            function_defs.len(),
            global_declarations.len()
        );

        // Process function definitions with their local declarations
        for (node_ref, func_def, span) in function_defs {
            debug!("Processing function definition at node {}", node_ref.get());

            // First, process the function and its parameters
            let function_scope_id = self.collect_function_and_params(&func_def, span);

            // Now collect local declarations with proper scope management
            self.collect_local_declarations(func_def.body, function_scope_id);

            // Pop the function scope after processing all its contents
            if self.symbol_table.current_scope() == function_scope_id {
                self.symbol_table.pop_scope();
                debug!(
                    "Popped function scope {} after processing function",
                    function_scope_id.get()
                );
            }
        }

        // Ensure we're back in global scope for global declarations
        self.symbol_table.set_current_scope(ScopeId::GLOBAL);

        // Process only global declarations (those at translation unit level)
        for (node_ref, decl, span) in global_declarations {
            debug!(
                "Processing global declaration at node {} with {} declarators",
                node_ref.get(),
                decl.init_declarators.len()
            );
            self.collect_declaration_symbols(&decl, span);
        }

        debug!(
            "Symbol collection complete. Found {} symbols",
            self.symbol_table.entries.len()
        );
    }

    fn resolve_names(&mut self) {
        let Some(root_node) = self.ast.get_root_node() else {
            debug!("No root node found, skipping name resolution");
            return;
        };

        let root_node_ref = self.ast.root.unwrap();
        debug!("Starting name resolution from root node: {}", root_node_ref.get());

        let mut name_resolver = NameResolver::new();
        name_resolver.resolve_names(self.ast, &mut self.symbol_table, self.diag, root_node_ref);

        debug!("Name resolution complete");
    }

    fn check_types(&mut self) {
        let Some(root_node) = self.ast.get_root_node() else {
            debug!("No root node found, skipping type checking");
            return;
        };

        let root_node_ref = self.ast.root.unwrap();
        debug!("Starting type checking from root node: {}", root_node_ref.get());

        let mut type_checker = TypeChecker::new();
        type_checker.check_types(self.ast, &mut self.symbol_table, self.diag, root_node_ref);

        debug!("Type checking complete");
    }

    fn get_safe_type_ref(&mut self) -> TypeRef {
        // Ensure at least one type exists, create a default int type if needed
        if self.ast.types.is_empty() {
            debug!("No types found, creating default int type");
            let int_type = Type {
                kind: TypeKind::Int { is_signed: true },
                qualifiers: TypeQualifiers::empty(),
                size: None,
                alignment: None,
            };
            self.ast.push_type(int_type)
        } else {
            TypeRef::new(1).unwrap()
        }
    }

    fn collect_function_and_params(
        &mut self,
        func_def: &FunctionDefData,
        span: SourceSpan,
    ) -> ScopeId {
        debug!(
            "collect_function_and_params called with declarator: {:?}",
            func_def.declarator
        );

        let (name, params) = self.extract_function_info(&func_def.declarator);
        let name = name.unwrap_or_else(|| Symbol::new("<anonymous>"));

        debug!(
            "Extracted function name: {}, parameters: {:?}",
            name.as_str(),
            params.len()
        );

        // Check for redeclaration
        if let Some(existing_entry_ref) = self
            .symbol_table
            .lookup_symbol_in_scope(name, self.symbol_table.current_scope())
        {
            let existing_entry = self.symbol_table.get_symbol_entry(existing_entry_ref);
            self.diag.report_warning(SemanticWarning::Redefinition {
                name,
                first_def: existing_entry.definition_span,
                second_def: span,
            });
            // Even on warning, create a function scope to maintain consistent state
            let error_scope_id = self.symbol_table.push_scope(ScopeKind::Function);
            debug!("Created error function scope {}", error_scope_id.get());
            return error_scope_id;
        }

        // Create function scope FIRST
        let function_scope_id = self.symbol_table.push_scope(ScopeKind::Function);
        debug!("Created function scope {}", function_scope_id.get());

        // Get a safe type reference
        let safe_type_ref = self.get_safe_type_ref();

        // Add parameters to function scope FIRST
        for (i, param) in params.iter().enumerate() {
            if let Some(param_name) = param.name {
                debug!(
                    "Adding function parameter {}: '{}' to function scope {}",
                    i,
                    param_name.as_str(),
                    function_scope_id.get()
                );
                let param_entry = SymbolEntry {
                    name: param_name,
                    kind: SymbolKind::Variable {
                        is_global: false,
                        is_static: false,
                        is_extern: false,
                        initializer: None,
                    },
                    type_info: safe_type_ref,
                    storage_class: None,
                    scope_id: function_scope_id.get(),
                    definition_span: span,
                    is_defined: true,
                    is_referenced: false,
                    is_completed: true,
                };
                self.symbol_table.add_symbol(param_name, param_entry);
            }
        }

        // Add function to global scope (this ensures it's available during type resolution)
        let func_entry = SymbolEntry {
            name,
            kind: SymbolKind::Function {
                is_definition: true,
                is_inline: false,
                is_variadic: false,
                parameters: params.clone(),
            },
            type_info: safe_type_ref,
            storage_class: None,
            scope_id: function_scope_id.get(), // Function points to its own scope
            definition_span: span,
            is_defined: true,
            is_referenced: false,
            is_completed: true,
        };
        debug!(
            "Adding function '{}' to global scope (function scope will be {})",
            name.as_str(),
            function_scope_id.get()
        );
        self.symbol_table.set_current_scope(ScopeId::GLOBAL);
        self.symbol_table.add_symbol(name, func_entry);
        self.symbol_table.set_current_scope(function_scope_id);

        // Store the function scope ID so it can be used during type resolution
        // The scope will be popped when we finish processing this function
        debug!(
            "Function scope {} will be used for function body processing",
            function_scope_id.get()
        );
        function_scope_id
    }

    fn collect_local_declarations(&mut self, body_node: NodeRef, function_scope_id: ScopeId) {
        debug!(
            "Collecting local declarations for function scope {}",
            function_scope_id.get()
        );

        // Ensure we're in the function scope
        self.symbol_table.set_current_scope(function_scope_id);

        // Traverse the function body with proper scope management
        // Start with the body node in the function scope (don't create block scope for top-level body)
        let mut stack = vec![(body_node, function_scope_id, true)]; // (node_ref, scope, is_top_level_body)
        let mut visited: BitVec = BitVec::new();

        while let Some((node_ref, expected_scope, is_top_level_body)) = stack.pop() {
            let node_id = node_ref.get() as usize;
            if node_id < visited.len() && visited[node_id] {
                continue;
            }
            if node_id >= visited.len() {
                visited.resize(node_id + 1, false);
            }
            visited.set(node_id, true);

            let node = self.ast.get_node(node_ref);

            match &node.kind {
                NodeKind::Declaration(decl) => {
                    debug!(
                        "Found local declaration with {} declarators",
                        decl.init_declarators.len()
                    );
                    let decl_clone = decl.clone();
                    let span = node.span;
                    self.collect_declaration_symbols(&decl_clone, span);
                    // Duplicate removed to avoid borrow conflict
                }
                NodeKind::For(for_stmt) => {
                    debug!("Found for loop, checking for declaration in initialization");
                    debug!("For loop has init: {}", for_stmt.init.is_some());

                    // Handle for loop with declaration in init
                    if let Some(init_node_ref) = for_stmt.init {
                        // Extract the node information first
                        let init_node = self.ast.get_node(init_node_ref);
                        debug!(
                            "Init node kind: {:?}",
                            std::mem::discriminant(&init_node.kind)
                        );
                        let node_kind = init_node.kind.clone();
                        let span = init_node.span;

                        let _ = init_node; // Drop the borrow

                        if let NodeKind::Declaration(decl) = node_kind {
                            debug!(
                                "For loop has declaration in init, processing with special scope"
                            );

                            // Create a scope for the for loop variable that covers the entire loop
                            let for_scope_id = self.symbol_table.push_scope(ScopeKind::Block);
                            debug!(
                                "Created for loop scope {} for loop variable",
                                for_scope_id.get()
                            );

                            // Process the for loop body in this scope
                            stack.push((for_stmt.body, for_scope_id, false));

                            // Add the for loop init declaration to the new scope first
                            self.collect_declaration_symbols(&decl, span);
                        } else {
                            debug!("For loop init is not a declaration, it's an expression");
                            // Init is an expression, process normally
                            let children = self.get_child_nodes(node_ref);
                            for child in children.into_iter().rev() {
                                stack.push((child, expected_scope, false));
                            }
                        }
                    } else {
                        debug!("For loop has no init");
                        // No init, process normally
                        let children = self.get_child_nodes(node_ref);
                        for child in children.into_iter().rev() {
                            stack.push((child, expected_scope, false));
                        }
                    }
                }
                NodeKind::CompoundStatement(nodes) => {
                    if is_top_level_body {
                        // Top-level function body: don't create new scope, use function scope
                        debug!("Processing top-level function body in function scope");
                        for child in nodes.iter().rev() {
                            stack.push((*child, expected_scope, false));
                        }
                    } else {
                        // Nested compound statement: create a new block scope
                        debug!("Creating block scope for nested compound statement");
                        let block_scope_id = self.symbol_table.push_scope(ScopeKind::Block);
                        for child in nodes.iter().rev() {
                            stack.push((*child, block_scope_id, false));
                        }
                    }
                }
                _ => {
                    // For other node types, just traverse their children in the current scope
                    let children = self.get_child_nodes(node_ref);
                    for child in children.into_iter().rev() {
                        stack.push((child, expected_scope, false));
                    }
                }
            }
        }
    }

    fn collect_declaration_symbols(&mut self, decl: &DeclarationData, span: SourceSpan) {
        for init_declarator in &decl.init_declarators {
            // Use extract_identifier to handle all declarator types (Identifier, Pointer, Array, etc.)
            if let Some(name) = Self::extract_identifier(&init_declarator.declarator) {
                // Check for redeclaration
                if let Some(existing_entry_ref) = self
                    .symbol_table
                    .lookup_symbol_in_scope(name, self.symbol_table.current_scope())
                {
                    let existing_entry = self.symbol_table.get_symbol_entry(existing_entry_ref);
                    self.diag.report_warning(SemanticWarning::Redefinition {
                        name,
                        first_def: existing_entry.definition_span,
                        second_def: span,
                    });
                    continue;
                }

                let safe_type_ref = self.get_safe_type_ref();
                let entry = SymbolEntry {
                    name,
                    kind: SymbolKind::Variable {
                        is_global: self.symbol_table.current_scope().get() == 1,
                        is_static: false,
                        is_extern: false,
                        initializer: init_declarator
                            .initializer
                            .as_ref()
                            .map(|_| NodeRef::new(1).unwrap()),
                    },
                    type_info: safe_type_ref,
                    storage_class: None,
                    scope_id: self.symbol_table.current_scope().get(),
                    definition_span: span,
                    is_defined: true,
                    is_referenced: false,
                    is_completed: true,
                };
                debug!(
                    "Adding variable '{}' to scope {}",
                    name.as_str(),
                    self.symbol_table.current_scope().get()
                );
                self.symbol_table.add_symbol(name, entry);
            } else {
                debug!(
                    "No identifier found in declarator: {:?}",
                    std::mem::discriminant(&init_declarator.declarator)
                );
            }
        }
    }

    fn extract_function_info(
        &self,
        declarator: &Declarator,
    ) -> (Option<Symbol>, Vec<FunctionParameter>) {
        // Find the function declarator that has the identifier as its direct base
        let (name, params) = self.find_function_with_name(declarator);
        if let Some((func_decl, params)) = name.zip(params) {
            debug!(
                "Found function declarator with name: {}, params={}",
                func_decl.as_str(),
                params.len()
            );

            let func_params: Vec<FunctionParameter> = params
                .iter()
                .enumerate()
                .filter_map(|(i, param)| {
                    debug!("Processing param {}: declarator={:?}", i, param.declarator);
                    if let Some(decl) = &param.declarator {
                        let param_name = Self::extract_identifier(decl);
                        debug!(
                            "  Extracted param name: {:?}",
                            param_name.as_ref().map(|s| s.as_str())
                        );
                        param_name.map(|name| FunctionParameter {
                            param_type: TypeRef::new(1).unwrap(),
                            name: Some(name),
                        })
                    } else {
                        debug!("  No declarator for param {}", i);
                        None
                    }
                })
                .collect();
            debug!("Final function params: {}", func_params.len());
            (Some(func_decl), func_params)
        } else {
            debug!("No function with name found");
            (None, Vec::new())
        }
    }

    fn find_function_with_name<'a>(&self, declarator: &'a Declarator) -> (Option<Symbol>, Option<&'a Vec<ParamData>>) {
        match declarator {
            Declarator::Function(base, params) => {
                if let Declarator::Identifier(name, _, _) = base.as_ref() {
                    // Found it
                    (Some(*name), Some(params))
                } else {
                    // Recurse
                    self.find_function_with_name(base)
                }
            }
            Declarator::Pointer(_, Some(base)) => self.find_function_with_name(base),
            Declarator::Array(base, _) => self.find_function_with_name(base),
            _ => (None, None)
        }
    }

    fn extract_identifier(declarator: &Declarator) -> Option<Symbol> {
        match declarator {
            Declarator::Identifier(name, _, _) => {
                debug!("Found identifier: {}", name.as_str());
                Some(*name)
            }
            Declarator::Pointer(_, Some(base)) => {
                debug!("Pointer to base: recursing");
                Self::extract_identifier(base)
            }
            Declarator::Array(base, _) => {
                debug!("Array of base: recursing");
                Self::extract_identifier(base)
            }
            Declarator::Function(base, _) => {
                debug!("Function returning base: recursing");
                Self::extract_identifier(base)
            }
            Declarator::Abstract => {
                debug!("Abstract declarator: no identifier");
                None
            }
            _ => {
                debug!("Other declarator type: no identifier");
                None
            }
        }
    }

    fn get_child_nodes(&self, node_ref: NodeRef) -> Vec<NodeRef> {
        let node = self.ast.get_node(node_ref);

        let children = match &node.kind {
            NodeKind::TranslationUnit(nodes) => {
                debug!("TranslationUnit has {} children", nodes.len());
                nodes.clone()
            }
            NodeKind::FunctionDef(func_def) => {
                debug!("FunctionDef: adding body to children");
                vec![func_def.body]
            }
            NodeKind::CompoundStatement(nodes) => nodes.clone(),
            NodeKind::If(if_stmt) => {
                let mut children = vec![if_stmt.condition, if_stmt.then_branch];
                if let Some(else_branch) = if_stmt.else_branch {
                    children.push(else_branch);
                }
                children
            }
            NodeKind::While(while_stmt) => vec![while_stmt.condition, while_stmt.body],
            NodeKind::DoWhile(body, condition) => vec![*body, *condition],
            NodeKind::For(for_stmt) => {
                let mut children = vec![for_stmt.body];
                if let Some(init) = for_stmt.init {
                    children.insert(0, init);
                }
                if let Some(condition) = for_stmt.condition {
                    children.insert(1, condition);
                }
                if let Some(increment) = for_stmt.increment {
                    children.push(increment);
                }
                children
            }
            NodeKind::Switch(condition, body) => vec![*condition, *body],
            NodeKind::Case(expr, stmt) => vec![*expr, *stmt],
            NodeKind::CaseRange(start_expr, end_expr, stmt) => vec![*start_expr, *end_expr, *stmt],
            NodeKind::Default(stmt) => vec![*stmt],
            NodeKind::Label(_, stmt) => vec![*stmt],
            NodeKind::BinaryOp(_, left, right) => vec![*left, *right],
            NodeKind::Assignment(_, lhs, rhs) => vec![*lhs, *rhs],
            NodeKind::FunctionCall(func, args) => {
                let mut children = vec![*func];
                children.extend(args);
                children
            }
            NodeKind::Return(expr) => {
                if let Some(expr_ref) = expr {
                    vec![*expr_ref]
                } else {
                    Vec::new()
                }
            }
            NodeKind::UnaryOp(_, expr) => vec![*expr],
            NodeKind::Cast(_, expr) => vec![*expr],
            NodeKind::SizeOfExpr(expr) => vec![*expr],
            NodeKind::TernaryOp(cond, then_expr, else_expr) => vec![*cond, *then_expr, *else_expr],
            _ => {
                debug!(
                    "No children for discriminant: {:?}",
                    std::mem::discriminant(&node.kind)
                );
                Vec::new()
            }
        };

        debug!(
            "get_child_nodes for node {} returned {} children",
            node_ref.get(),
            children.len()
        );
        children
    }
}

// Re-export diagnostic types for convenience
pub use crate::diagnostic::*;
