use std::collections::HashMap;
use std::num::NonZeroU32;

use crate::ast::*;
use crate::diagnostic::*;

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
        new_scope_id
    }

    pub fn pop_scope(&mut self) -> Option<ScopeId> {
        let current_scope = &self.scopes[self.current_scope_id.get() as usize - 1];
        if let Some(parent) = current_scope.parent {
            self.current_scope_id = parent;
            Some(parent)
        } else {
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

    pub fn lookup_symbol_in_scope(&self, name: Symbol, scope_id: ScopeId) -> Option<SymbolEntryRef> {
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

/// Symbol collection phase - builds symbol table
pub struct SymbolCollector<'ast, 'diag> {
    ast: &'ast Ast,
    diag: &'diag mut DiagnosticEngine,
    symbol_table: SymbolTable,
    current_scope_id: ScopeId,
    function_scope: Option<ScopeId>,
}

/// Type resolution phase - resolves type references
pub struct TypeResolver<'ast, 'diag> {
    ast: &'ast Ast,
    diag: &'diag mut DiagnosticEngine,
    symbol_table: &'ast SymbolTable,
}

/// Semantic validation phase - checks semantic correctness
pub struct SemanticValidator<'ast, 'diag> {
    ast: &'ast Ast,
    diag: &'diag mut DiagnosticEngine,
    symbol_table: &'ast SymbolTable,
}

/// AST annotation phase - adds resolved types to AST
pub struct AstAnnotator<'ast, 'diag> {
    ast: &'ast mut Ast,
    diag: &'diag mut DiagnosticEngine,
    symbol_table: &'ast SymbolTable,
}

/// Main semantic analyzer - orchestrates all phases
pub struct SemanticAnalyzer<'arena, 'src> {
    ast: &'arena mut Ast,
    diag: &'src mut DiagnosticEngine,
    pub symbol_table: SymbolTable,
}

impl<'arena, 'src> SemanticAnalyzer<'arena, 'src> {
    pub fn new(ast: &'arena mut Ast, diag: &'src mut DiagnosticEngine) -> Self {
        SemanticAnalyzer {
            ast,
            diag,
            symbol_table: SymbolTable::new(),
        }
    }

    pub fn analyze(&mut self) -> SemanticOutput {
        // Multi-pass analysis algorithm as specified in the design document

        // 1. Symbol Collection Pass
        let symbol_table = self.collect_symbols();

        // 2. Type Resolution Pass
        self.resolve_types(&symbol_table);

        // 3. Semantic Validation Pass
        self.validate_semantics(&symbol_table);

        // 4. Annotation Pass
        self.annotate_ast(&symbol_table);

        SemanticOutput {
            errors: std::mem::take(&mut self.diag.errors),
            warnings: std::mem::take(&mut self.diag.warnings),
        }
    }

    fn collect_symbols(&mut self) -> SymbolTable {
        let mut collector = SymbolCollector {
            ast: self.ast,
            diag: self.diag,
            symbol_table: SymbolTable::new(),
            current_scope_id: ScopeId::GLOBAL,
            function_scope: None,
        };
        collector.collect_symbols_impl();
        collector.symbol_table
    }

    fn resolve_types(&mut self, symbol_table: &SymbolTable) {
        let mut resolver = TypeResolver {
            ast: self.ast,
            diag: self.diag,
            symbol_table,
        };
        resolver.resolve_types_impl();
    }

    fn validate_semantics(&mut self, symbol_table: &SymbolTable) {
        let mut validator = SemanticValidator {
            ast: self.ast,
            diag: self.diag,
            symbol_table,
        };
        validator.validate_semantics_impl();
    }

    fn annotate_ast(&mut self, symbol_table: &SymbolTable) {
        let mut annotator = AstAnnotator {
            ast: self.ast,
            diag: self.diag,
            symbol_table,
        };
        annotator.annotate_ast_impl();
    }
}

impl<'ast, 'diag> SymbolCollector<'ast, 'diag> {
    pub fn collect_symbols_impl(&mut self) {
        if self.ast.nodes.is_empty() {
            return;
        }

        // Use a stack-based traversal to avoid recursion depth issues
        let mut stack = vec![NodeRef::new(1).unwrap()];

        while let Some(node_ref) = stack.pop() {
            let node = self.ast.get_node(node_ref);

            match &node.kind {
                NodeKind::Declaration(decl) => {
                    self.collect_declaration_symbols(decl, node.span);
                }
                NodeKind::FunctionDef(func_def) => {
                    self.collect_function_symbols(func_def, node.span);
                }
                _ => {}
            }

            // Push children in reverse order for correct traversal
            match &node.kind {
                NodeKind::TranslationUnit(nodes) => {
                    for &child_ref in nodes.iter().rev() {
                        stack.push(child_ref);
                    }
                }
                NodeKind::Declaration(_) => {} // No children to traverse
                NodeKind::FunctionDef(func_def) => {
                    stack.push(func_def.body);
                }
                NodeKind::CompoundStatement(nodes) => {
                    for &child_ref in nodes.iter().rev() {
                        stack.push(child_ref);
                    }
                }
                NodeKind::If(if_stmt) => {
                    if let Some(else_branch) = if_stmt.else_branch {
                        stack.push(else_branch);
                    }
                    stack.push(if_stmt.then_branch);
                    stack.push(if_stmt.condition);
                }
                NodeKind::While(while_stmt) => {
                    stack.push(while_stmt.body);
                    stack.push(while_stmt.condition);
                }
                NodeKind::For(for_stmt) => {
                    stack.push(for_stmt.body);
                    if let Some(increment) = for_stmt.increment {
                        stack.push(increment);
                    }
                    if let Some(condition) = for_stmt.condition {
                        stack.push(condition);
                    }
                    if let Some(init) = for_stmt.init {
                        stack.push(init);
                    }
                }
                NodeKind::BinaryOp(_, left, right) => {
                    stack.push(*right);
                    stack.push(*left);
                }
                NodeKind::Assignment(_, lhs, rhs) => {
                    stack.push(*rhs);
                    stack.push(*lhs);
                }
                NodeKind::FunctionCall(func, args) => {
                    for &arg in args.iter().rev() {
                        stack.push(arg);
                    }
                    stack.push(*func);
                }
                _ => {} // Other node types have no children
            }
        }
    }

    fn collect_declaration_symbols(&mut self, decl: &DeclarationData, span: SourceSpan) {
        for init_declarator in &decl.init_declarators {
            if let Declarator::Identifier(name, _, _) = &init_declarator.declarator {
                // Check for redeclaration
                if let Some((existing_entry_ref, _)) = self.symbol_table.lookup_symbol(*name) {
                    let existing_entry = self.symbol_table.get_symbol_entry(existing_entry_ref);
                    if existing_entry.scope_id == self.symbol_table.current_scope().get() {
                        // Redeclaration in same scope
                        self.diag.report_error(SemanticError::Redefinition {
                            name: *name,
                            first_def: existing_entry.definition_span,
                            second_def: span,
                        });
                        continue;
                    }
                }

                let entry = SymbolEntry {
                    name: *name,
                    kind: SymbolKind::Variable {
                        is_global: self.symbol_table.current_scope().get() == 1,
                        is_static: false, // TODO: determine from specifiers
                        is_extern: false, // TODO: determine from specifiers
                        initializer: init_declarator.initializer.as_ref().map(|_| NodeRef::new(1).unwrap()), // TODO
                    },
                    type_info: TypeRef::new(1).unwrap(), // TODO: resolve type
                    storage_class: None, // TODO
                    scope_id: self.symbol_table.current_scope().get(),
                    definition_span: span,
                    is_defined: true,
                    is_referenced: false,
                    is_completed: true,
                };
                self.symbol_table.add_symbol(*name, entry);
            }
        }
    }

    fn collect_function_symbols(&mut self, func_def: &FunctionDefData, span: SourceSpan) {
        if let Declarator::Identifier(name, _, _) = &func_def.declarator {
            // Check for redeclaration
            if let Some((existing_entry_ref, _)) = self.symbol_table.lookup_symbol(*name) {
                let existing_entry = self.symbol_table.get_symbol_entry(existing_entry_ref);
                if existing_entry.scope_id == self.symbol_table.current_scope().get() {
                    // Redeclaration in same scope
                    self.diag.report_error(SemanticError::Redefinition {
                        name: *name,
                        first_def: existing_entry.definition_span,
                        second_def: span,
                    });
                    return;
                }
            }

            // Enter function scope for the function body
            let function_scope = self.symbol_table.push_scope(ScopeKind::Function);
            self.function_scope = Some(function_scope);

            let entry = SymbolEntry {
                name: *name,
                kind: SymbolKind::Function {
                    is_definition: true,
                    is_inline: false, // TODO
                    is_variadic: false, // TODO
                    parameters: Vec::new(), // TODO
                },
                type_info: TypeRef::new(1).unwrap(), // TODO
                storage_class: None,
                scope_id: self.symbol_table.current_scope().get(),
                definition_span: span,
                is_defined: true,
                is_referenced: false,
                is_completed: true,
            };
            self.symbol_table.add_symbol(*name, entry);

            // Process function body - simplified traversal
            if self.ast.nodes.len() > func_def.body.get() as usize {
                let body_node = self.ast.get_node(func_def.body);
                if let NodeKind::CompoundStatement(nodes) = &body_node.kind {
                    // Enter block scope for compound statements
                    let _block_scope = self.symbol_table.push_scope(ScopeKind::Block);
                    for &child_ref in nodes {
                        let child_node = self.ast.get_node(child_ref);
                        match &child_node.kind {
                            NodeKind::Declaration(decl) => {
                                self.collect_declaration_symbols(decl, child_node.span);
                            }
                            _ => {}
                        }
                    }
                    self.symbol_table.pop_scope();
                }
            }

            // Exit function scope
            self.symbol_table.pop_scope();
            self.function_scope = None;
        }
    }
}

impl<'ast, 'diag> TypeResolver<'ast, 'diag> {
    pub fn resolve_types_impl(&mut self) {
        if self.ast.nodes.is_empty() {
            return;
        }

        // Use a stack-based traversal to avoid recursion depth issues
        // Start with the first node (index 0 corresponds to NodeRef(1))
        if self.ast.nodes.is_empty() {
            return;
        }
        let mut stack = vec![NodeRef::new(1).unwrap()];

        while let Some(node_ref) = stack.pop() {
            let node = self.ast.get_node(node_ref);

            match &node.kind {
                NodeKind::Ident(name, resolved_symbol) => {
                    // Resolve identifier to symbol
                    if let Some((symbol_ref, _)) = self.symbol_table.lookup_symbol(*name) {
                        resolved_symbol.set(Some(symbol_ref));
                        // Mark symbol as referenced - we need mutable access to symbol table
                        // This is a limitation of the current design - we need to modify the symbol table
                        // but TypeResolver only has immutable access
                        // For now, we'll skip marking as referenced
                    } else {
                        // Undeclared identifier
                        self.diag.report_error(SemanticError::UndeclaredIdentifier {
                            name: *name,
                            location: node.span,
                        });
                    }
                }
                _ => {}
            }

            // Push children in reverse order for correct traversal
            match &node.kind {
                NodeKind::TranslationUnit(nodes) => {
                    for &child_ref in nodes.iter().rev() {
                        stack.push(child_ref);
                    }
                }
                NodeKind::Declaration(_) => {} // No children to traverse
                NodeKind::FunctionDef(func_def) => {
                    stack.push(func_def.body);
                }
                NodeKind::CompoundStatement(nodes) => {
                    for &child_ref in nodes.iter().rev() {
                        stack.push(child_ref);
                    }
                }
                NodeKind::If(if_stmt) => {
                    if let Some(else_branch) = if_stmt.else_branch {
                        stack.push(else_branch);
                    }
                    stack.push(if_stmt.then_branch);
                    stack.push(if_stmt.condition);
                }
                NodeKind::While(while_stmt) => {
                    stack.push(while_stmt.body);
                    stack.push(while_stmt.condition);
                }
                NodeKind::For(for_stmt) => {
                    stack.push(for_stmt.body);
                    if let Some(increment) = for_stmt.increment {
                        stack.push(increment);
                    }
                    if let Some(condition) = for_stmt.condition {
                        stack.push(condition);
                    }
                    if let Some(init) = for_stmt.init {
                        stack.push(init);
                    }
                }
                NodeKind::BinaryOp(_, left, right) => {
                    stack.push(*right);
                    stack.push(*left);
                }
                NodeKind::Assignment(_, lhs, rhs) => {
                    stack.push(*rhs);
                    stack.push(*lhs);
                }
                NodeKind::FunctionCall(func, args) => {
                    for &arg in args.iter().rev() {
                        stack.push(arg);
                    }
                    stack.push(*func);
                }
                _ => {} // Other node types have no children
            }
        }
    }
}

impl<'ast, 'diag> SemanticValidator<'ast, 'diag> {
    pub fn validate_semantics_impl(&mut self) {
        if self.ast.nodes.is_empty() {
            return;
        }

        // Use a stack-based traversal to avoid recursion depth issues
        let mut stack = vec![NodeRef::new(1).unwrap()];

        while let Some(node_ref) = stack.pop() {
            let node = self.ast.get_node(node_ref);

            match &node.kind {
                NodeKind::BinaryOp(op, left, right) => {
                    self.validate_binary_op(*op, *left, *right, node.span);
                }
                NodeKind::Assignment(op, lhs, rhs) => {
                    self.validate_assignment(*op, *lhs, *rhs, node.span);
                }
                NodeKind::FunctionCall(func, args) => {
                    self.validate_function_call(*func, args, node.span);
                }
                _ => {}
            }

            // Push children in reverse order for correct traversal
            match &node.kind {
                NodeKind::TranslationUnit(nodes) => {
                    for &child_ref in nodes.iter().rev() {
                        stack.push(child_ref);
                    }
                }
                NodeKind::Declaration(_) => {} // No children to traverse
                NodeKind::FunctionDef(func_def) => {
                    stack.push(func_def.body);
                }
                NodeKind::CompoundStatement(nodes) => {
                    for &child_ref in nodes.iter().rev() {
                        stack.push(child_ref);
                    }
                }
                NodeKind::If(if_stmt) => {
                    if let Some(else_branch) = if_stmt.else_branch {
                        stack.push(else_branch);
                    }
                    stack.push(if_stmt.then_branch);
                    stack.push(if_stmt.condition);
                }
                NodeKind::While(while_stmt) => {
                    stack.push(while_stmt.body);
                    stack.push(while_stmt.condition);
                }
                NodeKind::For(for_stmt) => {
                    stack.push(for_stmt.body);
                    if let Some(increment) = for_stmt.increment {
                        stack.push(increment);
                    }
                    if let Some(condition) = for_stmt.condition {
                        stack.push(condition);
                    }
                    if let Some(init) = for_stmt.init {
                        stack.push(init);
                    }
                }
                NodeKind::BinaryOp(_, left, right) => {
                    stack.push(*right);
                    stack.push(*left);
                }
                NodeKind::Assignment(_, lhs, rhs) => {
                    stack.push(*rhs);
                    stack.push(*lhs);
                }
                NodeKind::FunctionCall(func, args) => {
                    for &arg in args.iter().rev() {
                        stack.push(arg);
                    }
                    stack.push(*func);
                }
                _ => {} // Other node types have no children
            }
        }
    }

    fn validate_binary_op(&mut self, _op: BinaryOp, _left: NodeRef, _right: NodeRef, _span: SourceSpan) {
        // TODO: Type check binary operations
    }

    fn validate_assignment(&mut self, _op: BinaryOp, _lhs: NodeRef, _rhs: NodeRef, _span: SourceSpan) {
        // TODO: Validate assignment compatibility
    }

    fn validate_function_call(&mut self, _func: NodeRef, _args: &[NodeRef], _span: SourceSpan) {
        // TODO: Validate function call arguments
    }
}

impl<'ast, 'diag> AstAnnotator<'ast, 'diag> {
    pub fn annotate_ast_impl(&mut self) {
        if self.ast.nodes.is_empty() {
            return;
        }

        // Use a stack-based traversal to avoid recursion depth issues
        let mut stack = vec![NodeRef::new(1).unwrap()];

        while let Some(node_ref) = stack.pop() {
            let node = self.ast.get_node(node_ref);

            match &node.kind {
                NodeKind::Ident(_name, resolved_symbol) => {
                    // Already resolved in type resolution pass
                    if let Some(symbol_ref) = resolved_symbol.get() {
                        let symbol = self.symbol_table.get_symbol_entry(symbol_ref);
                        node.resolved_type.set(Some(symbol.type_info));
                    }
                }
                NodeKind::LiteralInt(_value) => {
                    // Annotate with integer type - need to get mutable access to AST
                    // This is a problem - we need to restructure this
                    // For now, skip type annotation that requires mutable AST access
                }
                NodeKind::LiteralFloat(_value) => {
                    // Annotate with float type - need to get mutable access to AST
                    // This is a problem - we need to restructure this
                    // For now, skip type annotation that requires mutable AST access
                }
                NodeKind::BinaryOp(_op, left, right) => {
                    let left_node = self.ast.get_node(*left);
                    let right_node = self.ast.get_node(*right);

                    // Basic type propagation for arithmetic operations
                    if let (Some(left_type), Some(_right_type)) = (left_node.resolved_type.get(), right_node.resolved_type.get()) {
                        // TODO: Implement proper type promotion rules
                        // For now, just propagate left type
                        node.resolved_type.set(Some(left_type));
                    }
                }
                _ => {}
            }

            // Push children in reverse order for correct traversal
            match &node.kind {
                NodeKind::TranslationUnit(nodes) => {
                    for &child_ref in nodes.iter().rev() {
                        stack.push(child_ref);
                    }
                }
                NodeKind::Declaration(_) => {} // No children to traverse
                NodeKind::FunctionDef(func_def) => {
                    stack.push(func_def.body);
                }
                NodeKind::CompoundStatement(nodes) => {
                    for &child_ref in nodes.iter().rev() {
                        stack.push(child_ref);
                    }
                }
                NodeKind::If(if_stmt) => {
                    if let Some(else_branch) = if_stmt.else_branch {
                        stack.push(else_branch);
                    }
                    stack.push(if_stmt.then_branch);
                    stack.push(if_stmt.condition);
                }
                NodeKind::While(while_stmt) => {
                    stack.push(while_stmt.body);
                    stack.push(while_stmt.condition);
                }
                NodeKind::For(for_stmt) => {
                    stack.push(for_stmt.body);
                    if let Some(increment) = for_stmt.increment {
                        stack.push(increment);
                    }
                    if let Some(condition) = for_stmt.condition {
                        stack.push(condition);
                    }
                    if let Some(init) = for_stmt.init {
                        stack.push(init);
                    }
                }
                NodeKind::BinaryOp(_, left, right) => {
                    stack.push(*right);
                    stack.push(*left);
                }
                NodeKind::Assignment(_, lhs, rhs) => {
                    stack.push(*rhs);
                    stack.push(*lhs);
                }
                NodeKind::FunctionCall(func, args) => {
                    for &arg in args.iter().rev() {
                        stack.push(arg);
                    }
                    stack.push(*func);
                }
                _ => {} // Other node types have no children
            }
        }
    }
}





// Re-export diagnostic types for convenience
pub use crate::diagnostic::*;