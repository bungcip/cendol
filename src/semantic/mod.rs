use std::collections::HashMap;
use std::num::NonZeroU32;

use crate::ast::*;
use crate::diagnostic::*;
use log::debug;

/// Scope ID for efficient scope references
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ScopeId(NonZeroU32);

impl ScopeId {
    pub const GLOBAL: Self = Self(unsafe { NonZeroU32::new_unchecked(1) });

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
        debug!("SymbolTable: Pushed scope. New current_scope_id: {}", self.current_scope_id.get());
        new_scope_id
    }

    pub fn pop_scope(&mut self) -> Option<ScopeId> {
        let current_scope_id_before_pop = self.current_scope_id;
        let current_scope = &self.scopes[current_scope_id_before_pop.get() as usize - 1];
        if let Some(parent) = current_scope.parent {
            self.current_scope_id = parent;
            debug!("SymbolTable: Popped scope. Old current_scope_id: {}, New current_scope_id: {}", current_scope_id_before_pop.get(), self.current_scope_id.get());
            Some(parent)
        } else {
            debug!("SymbolTable: Attempted to pop global scope. No change.");
            None
        }
    }

    pub fn current_scope(&self) -> ScopeId {
        self.current_scope_id
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
        let mut scope_id = self.current_scope_id;
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
        debug!("Starting semantic analysis with {} nodes", self.ast.nodes.len());

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
        let Some(root_node) = self.ast.get_root_node() else {
            debug!("No root node found, skipping symbol collection");
            return;
        };
        
        // Get the root node reference for stack-based traversal
        let root_node_ref = self.ast.root.unwrap();

        debug!("Starting symbol collection from root node: {}", root_node_ref.get());

        // Collect all function definitions and declarations first
        let mut function_defs = Vec::new();
        let mut declarations = Vec::new();
        
        // Use stack-based traversal starting from root
        let mut stack = vec![root_node_ref];
        let mut nodes_visited = 0;

        while let Some(node_ref) = stack.pop() {
            nodes_visited += 1;
            if nodes_visited % 100 == 0 {
                debug!("Symbol collection: visited {} nodes, stack has {} items", nodes_visited, stack.len());
            }

            let node = self.ast.get_node(node_ref);

            match &node.kind {
                NodeKind::FunctionDef(func_def) => {
                    debug!("Found function definition at node {}", node_ref.get());
                    function_defs.push((node_ref, func_def.clone(), node.span));
                }
                NodeKind::Declaration(decl) => {
                    debug!("Found declaration at node {} with {} declarators", node_ref.get(), decl.init_declarators.len());
                    declarations.push((node_ref, decl.clone(), node.span));
                }
                _ => {}
            }

            // Add children to stack for further traversal
            let children = self.get_child_nodes(node_ref);
            for child in children {
                stack.push(child);
            }
        }

        debug!("Symbol collection: found {} function definitions and {} declarations from {} total nodes",
               function_defs.len(), declarations.len(), nodes_visited);
        
        // Process function definitions
        for (node_ref, func_def, span) in function_defs {
            debug!("Processing function definition at node {}", node_ref.get());
            self.collect_function_and_params(&func_def, span);
        }
        
        // Process declarations
        for (node_ref, decl, span) in declarations {
            debug!("Processing declaration at node {} with {} declarators", node_ref.get(), decl.init_declarators.len());
            self.collect_declaration_symbols(&decl, span);
        }
        
        debug!("Symbol collection complete. Found {} symbols", self.symbol_table.entries.len());
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

    fn collect_function_and_params(&mut self, func_def: &FunctionDefData, span: SourceSpan) {
        debug!("collect_function_and_params called with declarator: {:?}", func_def.declarator);
        
        let (name, params) = self.extract_function_info(&func_def.declarator);
        let name = name.unwrap_or_else(|| Symbol::new("<anonymous>"));

        debug!("Extracted function name: {}, parameters: {:?}", name.as_str(), params.len());

        // Check for redeclaration
        if let Some(existing_entry_ref) =
            self.symbol_table.lookup_symbol_in_scope(name, self.symbol_table.current_scope())
        {
            let existing_entry = self.symbol_table.get_symbol_entry(existing_entry_ref);
            self.diag.report_error(SemanticError::Redefinition {
                name,
                first_def: existing_entry.definition_span,
                second_def: span,
            });
            return;
        }

        // Get a safe type reference
        let safe_type_ref = self.get_safe_type_ref();

        // Add function to current scope
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
            scope_id: self.symbol_table.current_scope().get(),
            definition_span: span,
            is_defined: true,
            is_referenced: false,
            is_completed: true,
        };
        debug!("Adding function '{}' to scope {}", name.as_str(), self.symbol_table.current_scope().get());
        self.symbol_table.add_symbol(name, func_entry);

        // Add parameters to function scope - this is the key fix!
        let function_scope_id = self.symbol_table.push_scope(ScopeKind::Function);
        
        for (i, param) in params.iter().enumerate() {
            if let Some(param_name) = param.name {
                debug!("Adding function parameter {}: '{}' to function scope {}", i, param_name.as_str(), function_scope_id.get());
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
        
        // Pop the function scope after processing parameters
        self.symbol_table.pop_scope();
    }

    fn collect_declaration_symbols(&mut self, decl: &DeclarationData, span: SourceSpan) {
        for init_declarator in &decl.init_declarators {
            if let Declarator::Identifier(name, _, _) = &init_declarator.declarator {
                // Check for redeclaration
                if let Some(existing_entry_ref) =
                    self.symbol_table.lookup_symbol_in_scope(*name, self.symbol_table.current_scope())
                {
                    let existing_entry = self.symbol_table.get_symbol_entry(existing_entry_ref);
                    self.diag.report_error(SemanticError::Redefinition {
                        name: *name,
                        first_def: existing_entry.definition_span,
                        second_def: span,
                    });
                    continue;
                }

                let safe_type_ref = self.get_safe_type_ref();
                let entry = SymbolEntry {
                    name: *name,
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
                debug!("Adding variable '{}' to scope {}", name.as_str(), self.symbol_table.current_scope().get());
                self.symbol_table.add_symbol(*name, entry);
            }
        }
    }

    fn extract_function_info(&self, declarator: &Declarator) -> (Option<Symbol>, Vec<FunctionParameter>) {
        match declarator {
            Declarator::Function(base, params) => {
                let name = self.extract_identifier(base);
                debug!("Extracting function info: name={:?}, params={}",
                    name.as_ref().map(|s| s.as_str()), params.len());
                
                let func_params: Vec<FunctionParameter> = params.iter().enumerate().filter_map(|(i, param)| {
                    debug!("Processing param {}: declarator={:?}", i, param.declarator);
                    if let Some(decl) = &param.declarator {
                        let param_name = self.extract_identifier(decl);
                        debug!("  Extracted param name: {:?}", param_name.as_ref().map(|s| s.as_str()));
                        param_name.map(|name| FunctionParameter {
                            param_type: TypeRef::new(1).unwrap(),
                            name: Some(name),
                        })
                    } else {
                        debug!("  No declarator for param {}", i);
                        None
                    }
                }).collect();
                debug!("Final function params: {}", func_params.len());
                (name, func_params)
            }
            _ => {
                debug!("Not a function declarator: {:?}", std::mem::discriminant(declarator));
                (self.extract_identifier(declarator), Vec::new())
            }
        }
    }

    fn extract_identifier(&self, declarator: &Declarator) -> Option<Symbol> {
        match declarator {
            Declarator::Identifier(name, _, _) => {
                debug!("Found identifier: {}", name.as_str());
                Some(*name)
            },
            Declarator::Pointer(_, Some(base)) => {
                debug!("Pointer to base: recursing");
                self.extract_identifier(base)
            },
            Declarator::Array(base, _) => {
                debug!("Array of base: recursing");
                self.extract_identifier(base)
            },
            Declarator::Function(base, _) => {
                debug!("Function returning base: recursing");
                self.extract_identifier(base)
            },
            Declarator::Abstract => {
                debug!("Abstract declarator: no identifier");
                None
            },
            other => {
                debug!("Other declarator type: {:?}", std::mem::discriminant(other));
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
                debug!("No children for discriminant: {:?}", std::mem::discriminant(&node.kind));
                Vec::new()
            }
        };
        
        debug!("get_child_nodes for node {} returned {} children", node_ref.get(), children.len());
        children
    }

    fn get_child_nodes_from_kind(&self, node_kind: &NodeKind) -> Vec<NodeRef> {
        match node_kind {
            NodeKind::TranslationUnit(nodes) => nodes.clone(),
            NodeKind::FunctionDef(func_def) => vec![func_def.body],
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
            _ => Vec::new(),
        }
    }

    fn resolve_types(&mut self) {
        // Check if we have a root node to start traversal from
        let Some(root_node) = self.ast.get_root_node() else {
            debug!("No root node found, skipping type resolution");
            return;
        };
        
        // Get the root node reference for stack-based traversal
        let root_node_ref = self.ast.root.unwrap();

        debug!("Starting type resolution from root node: {}", root_node_ref.get());

        // Type resolution using stack-based traversal starting from root
        let mut stack = vec![root_node_ref];
        let mut nodes_processed = 0;

        while let Some(node_ref) = stack.pop() {
            nodes_processed += 1;
            if nodes_processed % 50 == 0 {
                debug!("Type resolution: processed {} nodes, stack has {} items", nodes_processed, stack.len());
            }

            let node = self.ast.get_node(node_ref);

            match &node.kind {
                NodeKind::Ident(name, resolved_symbol) => {
                    debug!("Resolving identifier: {}", name.as_str());
                    if let Some((symbol_ref, _)) = self.symbol_table.lookup_symbol(*name) {
                        debug!("Found symbol {} in scope", name.as_str());
                        resolved_symbol.set(Some(symbol_ref));
                        // Mark symbol as referenced
                        let symbol_entry = self.symbol_table.get_symbol_entry_mut(symbol_ref);
                        symbol_entry.is_referenced = true;
                    } else {
                        debug!("Undeclared identifier: {}", name.as_str());
                        self.diag.report_error(SemanticError::UndeclaredIdentifier {
                            name: *name,
                            location: node.span,
                        });
                    }
                }
                _ => {}
            }

            // Add children to stack
            let children = self.get_child_nodes(node_ref);
            for child in children {
                stack.push(child);
            }
        }
        
        debug!("Type resolution complete");
    }
}

// Re-export diagnostic types for convenience
pub use crate::diagnostic::*;
