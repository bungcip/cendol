use bitvec::prelude::*;
use std::collections::HashMap;
use std::num::NonZeroU32;

use crate::ast::*;
use log::debug;

/// Scope ID for efficient scope references
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ScopeId(NonZeroU32);

impl ScopeId {
    pub const GLOBAL: Self = Self(NonZeroU32::new(1).unwrap());

    pub fn new(id: u32) -> Option<Self> {
        NonZeroU32::new(id).map(Self)
    }

    pub fn get(self) -> u32 {
        self.0.get()
    }
}

/// Scope types
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScopeKind {
    Global,
    File,
    Function,
    Block,
    FunctionPrototype,
}

/// Scope information
#[derive(Debug)]
pub struct Scope {
    pub parent: Option<ScopeId>,
    pub symbols: HashMap<Symbol, SymbolEntryRef>,
    pub kind: ScopeKind,
    pub level: u32,
}

/// Symbol table using flattened storage
#[derive(Debug)]
pub struct SymbolTable {
    pub entries: Vec<SymbolEntry>,
    pub scopes: Vec<Scope>,
    current_scope_id: ScopeId,
    next_scope_id: u32,
}

impl Default for SymbolTable {
    fn default() -> Self {
        Self::new()
    }
}

impl SymbolTable {
    pub fn new() -> Self {
        let mut table = SymbolTable {
            entries: Vec::new(),
            scopes: Vec::new(),
            current_scope_id: ScopeId::GLOBAL,
            next_scope_id: 2, // Start after GLOBAL
        };

        // Initialize global scope
        table.scopes.push(Scope {
            parent: None,
            symbols: HashMap::new(),
            kind: ScopeKind::Global,
            level: 0,
        });

        table
    }

    pub fn push_scope(&mut self, kind: ScopeKind) -> ScopeId {
        let new_scope_id = ScopeId::new(self.next_scope_id).unwrap();
        self.next_scope_id += 1;

        let new_scope = Scope {
            parent: Some(self.current_scope_id),
            symbols: HashMap::new(),
            kind,
            level: self.scopes[self.current_scope_id.get() as usize - 1].level + 1,
        };

        self.scopes.push(new_scope);
        self.current_scope_id = new_scope_id;
        debug!(
            "SymbolTable: Pushed scope. New current_scope_id: {}",
            self.current_scope_id.get()
        );
        new_scope_id
    }

    pub fn push_scope_with_id(&mut self, scope_id: ScopeId, kind: ScopeKind) -> ScopeId {
        // Update next_scope_id to ensure uniqueness
        if scope_id.get() >= self.next_scope_id {
            self.next_scope_id = scope_id.get() + 1;
        }

        let new_scope = Scope {
            parent: Some(self.current_scope_id),
            symbols: HashMap::new(),
            kind,
            level: self.scopes[self.current_scope_id.get() as usize - 1].level + 1,
        };

        // Ensure the scope vector is large enough
        while self.scopes.len() < scope_id.get() as usize {
            self.scopes.push(Scope {
                parent: None,
                symbols: HashMap::new(),
                kind: ScopeKind::Global,
                level: 0,
            });
        }

        // Replace the scope at the given index
        if scope_id.get() as usize <= self.scopes.len() {
            self.scopes[scope_id.get() as usize - 1] = new_scope;
        } else {
            self.scopes.push(new_scope);
        }

        self.current_scope_id = scope_id;
        debug!(
            "SymbolTable: Pushed scope with ID. New current_scope_id: {}",
            self.current_scope_id.get()
        );
        scope_id
    }

    pub fn pop_scope(&mut self) -> Option<ScopeId> {
        let current_scope_id_before_pop = self.current_scope_id;
        let current_scope = &self.scopes[current_scope_id_before_pop.get() as usize - 1];
        if let Some(parent) = current_scope.parent {
            self.current_scope_id = parent;
            debug!(
                "SymbolTable: Popped scope. Old current_scope_id: {}, New current_scope_id: {}",
                current_scope_id_before_pop.get(),
                self.current_scope_id.get()
            );
            Some(parent)
        } else {
            debug!("SymbolTable: Attempted to pop global scope. No change.");
            None
        }
    }

    pub fn current_scope(&self) -> ScopeId {
        self.current_scope_id
    }

    pub fn set_current_scope(&mut self, scope_id: ScopeId) {
        self.current_scope_id = scope_id;
        debug!(
            "SymbolTable: Set current_scope_id to {}",
            self.current_scope_id.get()
        );
    }

    pub fn get_scope(&self, scope_id: ScopeId) -> &Scope {
        &self.scopes[scope_id.get() as usize - 1]
    }

    pub fn get_scope_mut(&mut self, scope_id: ScopeId) -> &mut Scope {
        &mut self.scopes[scope_id.get() as usize - 1]
    }

    pub fn add_symbol(&mut self, name: Symbol, entry: SymbolEntry) -> SymbolEntryRef {
        let entry_ref = self.push_symbol_entry(entry);
        let current_scope = self.get_scope_mut(self.current_scope_id);
        current_scope.symbols.insert(name, entry_ref);
        entry_ref
    }

    pub fn lookup_symbol(&self, name: Symbol) -> Option<(SymbolEntryRef, ScopeId)> {
        self.lookup_symbol_from(name, self.current_scope_id)
    }

    pub fn lookup_symbol_from(&self, name: Symbol, start_scope: ScopeId) -> Option<(SymbolEntryRef, ScopeId)> {
        let mut scope_id = start_scope;
        loop {
            let scope = self.get_scope(scope_id);
            if let Some(&entry_ref) = scope.symbols.get(&name) {
                return Some((entry_ref, scope_id));
            }
            if let Some(parent) = scope.parent {
                scope_id = parent;
            } else {
                break;
            }
        }
        None
    }

    pub fn lookup_symbol_in_scope(
        &self,
        name: Symbol,
        scope_id: ScopeId,
    ) -> Option<SymbolEntryRef> {
        self.get_scope(scope_id).symbols.get(&name).copied()
    }

    fn push_symbol_entry(&mut self, entry: SymbolEntry) -> SymbolEntryRef {
        let index = self.entries.len() as u32 + 1;
        self.entries.push(entry);
        SymbolEntryRef::new(index).expect("SymbolEntryRef overflow")
    }

    pub fn get_symbol_entry(&self, index: SymbolEntryRef) -> &SymbolEntry {
        &self.entries[(index.get() - 1) as usize]
    }

    pub fn get_symbol_entry_mut(&mut self, index: SymbolEntryRef) -> &mut SymbolEntry {
        &mut self.entries[(index.get() - 1) as usize]
    }
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

        // Collect symbols
        self.collect_symbols();

        // Resolve types and validate
        self.resolve_types();

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

    fn resolve_types(&mut self) {
        // Check if we have a root node to start traversal from
        let Some(_root_node) = self.ast.get_root_node() else {
            debug!("No root node found, skipping type resolution");
            return;
        };

        // Get the root node reference for stack-based traversal
        let _root_node_ref = self.ast.root.unwrap();

        debug!(
            "Starting type resolution from root node: {}",
            _root_node_ref.get()
        );

        // Stack for traversal: (node_ref, expected_scope, is_top_level_body)
        let mut stack = vec![(_root_node_ref, ScopeId::GLOBAL, false)];
        let mut nodes_processed = 0;
        let mut visited_nodes: BitVec = BitVec::new();

        while let Some((node_ref, expected_scope, is_top_level_body)) = stack.pop() {
            // Skip already visited nodes to prevent infinite loops
            let node_id = node_ref.get() as usize;
            if node_id < visited_nodes.len() && visited_nodes[node_id] {
                continue;
            }
            if node_id >= visited_nodes.len() {
                visited_nodes.resize(node_id + 1, false);
            }
            visited_nodes.set(node_id, true);

            nodes_processed += 1;
            if nodes_processed % 50 == 0 {
                debug!(
                    "Type resolution: processed {} nodes, stack has {} items",
                    nodes_processed,
                    stack.len()
                );
            }

            let node = self.ast.get_node(node_ref);

            // Set the current scope for this node
            self.symbol_table.set_current_scope(expected_scope);

            match &node.kind {
                NodeKind::FunctionDef(func_def) => {
                    // For function definitions, we need to resolve in the function scope
                    let func_name = self.extract_function_info(&func_def.declarator).0.unwrap_or_else(|| Symbol::new("<anonymous>"));
                    if let Some((symbol_ref, _)) = self.symbol_table.lookup_symbol(func_name) {
                        let symbol_entry = self.symbol_table.get_symbol_entry(symbol_ref);
                        let func_scope_id = ScopeId::new(symbol_entry.scope_id).unwrap();
                        // Push function body with function scope, mark as top-level body
                        let children = self.get_child_nodes(node_ref);
                        for child in children.into_iter().rev() {
                            let is_body = matches!(self.ast.get_node(child).kind, NodeKind::CompoundStatement(_));
                            stack.push((child, func_scope_id, is_body));
                        }
                    } else {
                        // Fallback: push children with current scope
                        let children = self.get_child_nodes(node_ref);
                        for child in children.into_iter().rev() {
                            stack.push((child, expected_scope, false));
                        }
                    }
                }
                NodeKind::CompoundStatement(_) => {
                    if is_top_level_body {
                        // Top-level function body: don't create new scope
                        let children = self.get_child_nodes(node_ref);
                        for child in children.into_iter().rev() {
                            stack.push((child, expected_scope, false));
                        }
                    } else {
                        // Nested compound statement: create block scope
                        let block_scope = self.symbol_table.push_scope(ScopeKind::Block);
                        let children = self.get_child_nodes(node_ref);
                        for child in children.into_iter().rev() {
                            stack.push((child, block_scope, false));
                        }
                    }
                }
                NodeKind::Ident(name, resolved_symbol) => {
                    debug!(
                        "Resolving identifier: {} in scope {}",
                        name.as_str(),
                        expected_scope.get()
                    );
                    if let Some((symbol_ref, scope_id)) = self.symbol_table.lookup_symbol_from(*name, expected_scope) {
                        debug!("Found symbol {} in scope {}", name.as_str(), scope_id.get());
                        resolved_symbol.set(Some(symbol_ref));
                        // Mark symbol as referenced
                        let symbol_entry = self.symbol_table.get_symbol_entry_mut(symbol_ref);
                        symbol_entry.is_referenced = true;
                    } else {
                        debug!(
                            "Undeclared identifier: {} (expected scope: {}), checking symbol table contents",
                            name.as_str(),
                            expected_scope.get()
                        );
                        // Debug: list all symbols in current scope and parent scopes
                        let mut debug_scope = expected_scope;
                        while let Some(scope) = self.symbol_table.scopes.get(debug_scope.get() as usize - 1) {
                            debug!("Scope {} (kind: {:?}) has {} symbols:", debug_scope.get(), scope.kind, scope.symbols.len());
                            for (sym_name, sym_ref) in &scope.symbols {
                                let entry = self.symbol_table.get_symbol_entry(*sym_ref);
                                debug!("  Symbol: {} -> {:?}", sym_name.as_str(), entry.kind);
                            }
                            if let Some(parent) = scope.parent {
                                debug_scope = parent;
                            } else {
                                break;
                            }
                        }
                        self.diag.report_error(SemanticError::UndeclaredIdentifier {
                            name: *name,
                            location: node.span,
                        });
                    }
                    // Identifiers have no children
                }
                _ => {
                    // For all other nodes, push children with the same scope
                    let children = self.get_child_nodes(node_ref);
                    for child in children.into_iter().rev() {
                        stack.push((child, expected_scope, false));
                    }
                }
            }
        }

        debug!("Type resolution complete");
    }
}

// Re-export diagnostic types for convenience
pub use crate::diagnostic::*;
