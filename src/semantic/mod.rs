use crate::common::{SourceLocation, SourceSpan};
use crate::parser::ast::{Designator, ForInit, Function, Initializer, Expr, Program, Stmt, Type, TypedExpr, TypedStmt, TypedFunctionDecl, TypedTranslationUnit, TypedDesignator, TypedInitializer, TypedDeclarator, TypedForInit};
use crate::semantic::error::SemanticError;
use std::collections::HashMap;

pub mod error;

/// Represents a symbol in the symbol table.
#[derive(Debug, Clone)]
#[allow(dead_code)]
struct Symbol {
    ty: Type,
    is_function: bool,
    defined_at: String, // For better error messages
}

/// A scoped symbol table using a stack of hash maps for nested scopes.
#[derive(Debug, Clone)]
pub struct SymbolTable {
    scopes: Vec<HashMap<String, Symbol>>,
}

impl SymbolTable {
    /// Creates a new symbol table with a global scope.
    fn new() -> Self {
        SymbolTable {
            scopes: vec![HashMap::new()],
        }
    }

    /// Pushes a new scope onto the stack.
    fn push_scope(&mut self) {
        self.scopes.push(HashMap::new());
    }

    /// Pops the top scope from the stack.
    fn pop_scope(&mut self) {
        if self.scopes.len() > 1 {
            self.scopes.pop();
        }
    }

    /// Inserts a symbol into the current (top) scope.
    fn insert(&mut self, name: String, symbol: Symbol) {
        if let Some(scope) = self.scopes.last_mut() {
            scope.insert(name, symbol);
        }
    }

    /// Looks up a symbol starting from the current scope and moving outwards.
    fn lookup(&self, name: &str) -> Option<&Symbol> {
        for scope in self.scopes.iter().rev() {
            if let Some(symbol) = scope.get(name) {
                return Some(symbol);
            }
        }
        None
    }

    /// Checks if a symbol exists in any scope.
    fn contains_key(&self, name: &str) -> bool {
        self.lookup(name).is_some()
    }
}

/// A semantic analyzer that checks for semantic errors in the AST.
pub struct SemanticAnalyzer {
    symbol_table: SymbolTable,
    pub enum_constants: HashMap<String, i64>,
    current_function: Option<String>,
    errors: Vec<(SemanticError, String, SourceSpan)>, // (error, file, span)
}

impl Default for SemanticAnalyzer {
    fn default() -> Self {
        Self::new()
    }
}

impl SemanticAnalyzer {
    /// Creates a new `SemanticAnalyzer`.
    pub fn new() -> Self {
        SemanticAnalyzer {
            symbol_table: SymbolTable::new(),
            enum_constants: HashMap::new(),
            current_function: None,
            errors: Vec::new(),
        }
    }

    /// Creates a new `SemanticAnalyzer` with built-in functions.
    pub fn with_builtins() -> Self {
        let mut analyzer = Self::new();
        analyzer.add_builtin_functions();
        analyzer
    }

    /// Adds built-in functions to the symbol table.
    fn add_builtin_functions(&mut self) {
        // Add common C built-in functions that might be called
        let builtins = vec![
            ("printf", Type::Int),
            ("malloc", Type::Pointer(Box::new(Type::Void))),
            ("free", Type::Void),
            ("scanf", Type::Int),
            ("strcmp", Type::Int),
            ("memcpy", Type::Pointer(Box::new(Type::Void))),
        ];

        for (name, return_type) in builtins {
            self.symbol_table.insert(
                name.to_string(),
                Symbol {
                    ty: return_type,
                    is_function: true,
                    defined_at: "built-in".to_string(),
                },
            );
        }
    }

    /// Analyzes a program for semantic errors and returns a typed translation unit.
    ///
    /// # Arguments
    ///
    /// * `program` - The program AST to analyze.
    /// * `filename` - The source filename for error reporting.
    ///
    /// # Returns
    ///
    /// A `Result` which is `Ok` with the typed translation unit if no semantic errors were found, or `Err` with a vector of errors.
    pub fn analyze(
        mut self,
        program: Program,
        filename: &str,
    ) -> Result<TypedTranslationUnit, Vec<(SemanticError, String, SourceSpan)>> {
        // First pass: collect all function definitions and global declarations
        self.collect_symbols(&program, filename);

        // Second pass: check all expressions and statements for semantic errors and build typed AST
        let typed_program = self.check_program(program, filename);

        if self.errors.is_empty() {
            Ok(typed_program)
        } else {
            Err(self.errors)
        }
    }

    /// First pass: collect all symbols (functions and global variables).
    fn collect_symbols(&mut self, program: &Program, filename: &str) {
        for global in &program.globals {
            match global {
                Stmt::FunctionDeclaration(ty, name, _params, _) => {
                    if let Some(existing) = self.symbol_table.lookup(name) {
                        if existing.is_function {
                            self.errors.push((
                                SemanticError::FunctionRedeclaration(name.clone()),
                                filename.to_string(),
                                SourceSpan::new(
                                    crate::file::FileId(0),
                                    SourceLocation::new(crate::file::FileId(0), 0, 0),
                                    SourceLocation::new(crate::file::FileId(0), 0, 0),
                                ),
                            ));
                        }
                    } else {
                        self.symbol_table.insert(
                            name.clone(),
                            Symbol {
                                ty: ty.clone(),
                                is_function: true,
                                defined_at: filename.to_string(),
                            },
                        );
                    }
                }
                Stmt::Declaration(ty, declarators) => {
                    if let Type::Enum(_name, members) = ty {
                        if !members.is_empty() {
                            let mut next_value = 0;
                            for (name, value, span) in members {
                                let val = if let Some(expr) = value {
                                    if let Expr::Number(num) = **expr {
                                        num
                                    } else {
                                        self.errors.push((
                                            SemanticError::InvalidEnumInitializer(name.clone()),
                                            filename.to_string(),
                                            span.clone(),
                                        ));
                                        -1 // Dummy value
                                    }
                                } else {
                                    next_value
                                };

                                if self.enum_constants.contains_key(name) {
                                    self.errors.push((
                                        SemanticError::VariableRedeclaration(name.clone()),
                                        filename.to_string(),
                                        span.clone(),
                                    ));
                                } else {
                                    self.enum_constants.insert(name.clone(), val);
                                }
                                next_value = val + 1;
                            }
                        }
                    }

                    for declarator in declarators {
                        // Global variables can be redeclared (tentative definitions)
                        // Only check for conflicts with functions
                        if let Some(existing) = self.symbol_table.lookup(&declarator.name) {
                            if existing.is_function {
                                self.errors.push((
                                    SemanticError::VariableRedeclaration(declarator.name.clone()),
                                    filename.to_string(),
                                    SourceSpan::new(
                                        crate::file::FileId(0),
                                        SourceLocation::new(crate::file::FileId(0), 0, 0),
                                        SourceLocation::new(crate::file::FileId(0), 0, 0),
                                    ),
                                ));
                            }
                        } else {
                            self.symbol_table.insert(
                                declarator.name.clone(),
                                Symbol {
                                    ty: declarator.ty.clone(),
                                    is_function: false,
                                    defined_at: filename.to_string(),
                                },
                            );
                        }
                    }
                }
                _ => {}
            }
        }

        // Collect function definitions
        for function in &program.functions {
            if let Some(existing) = self.symbol_table.lookup(&function.name) {
                if existing.is_function {
                    self.errors.push((
                        SemanticError::FunctionRedeclaration(function.name.clone()),
                        filename.to_string(),
                        SourceSpan::new(
                            crate::file::FileId(0),
                            SourceLocation::new(crate::file::FileId(0), 0, 0),
                            SourceLocation::new(crate::file::FileId(0), 0, 0),
                        ),
                    ));
                }
            } else {
                self.symbol_table.insert(
                    function.name.clone(),
                    Symbol {
                        ty: function.return_type.clone(),
                        is_function: true,
                        defined_at: filename.to_string(),
                    },
                );
            }
        }
    }

    /// Second pass: check all statements and expressions for semantic correctness and build typed AST.
    fn check_program(&mut self, program: Program, filename: &str) -> TypedTranslationUnit {
        let mut typed_functions = Vec::new();
        for function in program.functions {
            self.current_function = Some(function.name.clone());
            typed_functions.push(self.check_function(function, filename));
        }

        let mut typed_globals = Vec::new();
        for global in program.globals {
            typed_globals.push(self.check_statement(global, filename));
        }

        TypedTranslationUnit {
            globals: typed_globals,
            functions: typed_functions,
        }
    }

    /// Checks a function for semantic errors and returns a typed function declaration.
    fn check_function(&mut self, function: crate::parser::ast::Function, filename: &str) -> TypedFunctionDecl {
        // Push function scope
        self.symbol_table.push_scope();

        // Check parameters for redeclaration
        let mut param_names = std::collections::HashSet::new();
        for param in &function.params {
            if !param_names.insert(param.name.clone()) {
                self.errors.push((
                    SemanticError::VariableRedeclaration(param.name.clone()),
                    filename.to_string(),
                    SourceSpan::new(
                        crate::file::FileId(0),
                        SourceLocation::new(crate::file::FileId(0), 0, 0),
                        SourceLocation::new(crate::file::FileId(0), 0, 0),
                    ),
                ));
            }
            // Add parameters to local symbol table
            self.symbol_table.insert(
                param.name.clone(),
                Symbol {
                    ty: param.ty.clone(),
                    is_function: false,
                    defined_at: format!("{} (parameter)", filename),
                },
            );
        }

        // Check function body and build typed statements
        let mut typed_body = Vec::new();
        for stmt in function.body {
            typed_body.push(self.check_statement(stmt, filename));
        }

        // Pop function scope
        self.symbol_table.pop_scope();
        self.current_function = None;

        TypedFunctionDecl {
            return_type: function.return_type,
            name: function.name,
            params: function.params,
            body: typed_body,
            is_inline: function.is_inline,
            is_variadic: function.is_variadic,
        }
    }

    /// Checks a statement for semantic errors and returns a typed statement.
    fn check_statement(&mut self, stmt: Stmt, filename: &str) -> TypedStmt {
        match stmt {
            Stmt::Declaration(ty, declarators) => {
                if let Type::Enum(_name, members) = &ty {
                    // Only process enum constants for local enums (inside functions)
                    // Global enums are already processed in collect_symbols
                    if self.current_function.is_some() && !members.is_empty() {
                        let mut next_value = 0;
                        for (name, value, span) in members {
                            let val = if let Some(expr) = value {
                                if let Expr::Number(num) = **expr {
                                    num
                                } else {
                                    self.errors.push((
                                        SemanticError::InvalidEnumInitializer(name.clone()),
                                        filename.to_string(),
                                        span.clone(),
                                    ));
                                    -1 // Dummy value
                                }
                            } else {
                                next_value
                            };

                            if self.enum_constants.contains_key(name) {
                                self.errors.push((
                                    SemanticError::VariableRedeclaration(name.clone()),
                                    filename.to_string(),
                                    span.clone(),
                                ));
                            } else {
                                self.enum_constants.insert(name.clone(), val);
                            }
                            next_value = val + 1;
                        }
                    }
                }

                let mut typed_declarators = Vec::new();
                for declarator in declarators {
                    // Check for redeclaration only in local scope
                    if self.current_function.is_some() {
                        if let Some(existing) = self.symbol_table.lookup(&declarator.name) {
                            if !existing.is_function {
                                self.errors.push((
                                    SemanticError::VariableRedeclaration(declarator.name.clone()),
                                    filename.to_string(),
                                    SourceSpan::new(
                                        crate::file::FileId(0),
                                        SourceLocation::new(crate::file::FileId(0), 0, 0),
                                        SourceLocation::new(crate::file::FileId(0), 0, 0),
                                    ),
                                ));
                            }
                        }
                    }

                    // Insert symbol if not already present
                    if self.symbol_table.lookup(&declarator.name).is_none() {
                        self.symbol_table.insert(
                            declarator.name.clone(),
                            Symbol {
                                ty: declarator.ty.clone(),
                                is_function: false,
                                defined_at: filename.to_string(),
                            },
                        );
                    }

                    // Check initializer expression
                    let typed_initializer = declarator.initializer.map(|init| self.convert_initializer_to_typed(init, filename));

                    typed_declarators.push(TypedDeclarator {
                        ty: declarator.ty,
                        name: declarator.name,
                        initializer: typed_initializer,
                    });
                }
                TypedStmt::Declaration(ty, typed_declarators)
            }
            Stmt::Expr(expr) => {
                let typed_expr = self.check_expression(expr, filename);
                TypedStmt::Expr(typed_expr)
            }
            Stmt::Return(expr) => {
                let typed_expr = self.check_expression(expr, filename);
                TypedStmt::Return(typed_expr)
            }
            Stmt::If(cond, then, otherwise) => {
                let typed_cond = self.check_expression(*cond, filename);
                let typed_then = Box::new(self.check_statement(*then, filename));
                let typed_otherwise = otherwise.map(|o| Box::new(self.check_statement(*o, filename)));
                TypedStmt::If(typed_cond, typed_then, typed_otherwise)
            }
            Stmt::While(cond, body) => {
                let typed_cond = self.check_expression(*cond, filename);
                let typed_body = Box::new(self.check_statement(*body, filename));
                TypedStmt::While(typed_cond, typed_body)
            }
            Stmt::For(init, cond, inc, body) => {
                let typed_init = init.map(|i| match i {
                    ForInit::Declaration(ty, name, initializer) => {
                        if let Some(existing) = self.symbol_table.lookup(&name) {
                            if !existing.is_function {
                                self.errors.push((
                                    SemanticError::FunctionRedeclaration(name.clone()),
                                    filename.to_string(),
                                    SourceSpan::new(
                                        crate::file::FileId(0),
                                        SourceLocation::new(crate::file::FileId(0), 0, 0),
                                        SourceLocation::new(crate::file::FileId(0), 0, 0),
                                    ),
                                ));
                            }
                        } else {
                            self.symbol_table.insert(
                                name.clone(),
                                Symbol {
                                    ty: ty.clone(),
                                    is_function: false,
                                    defined_at: filename.to_string(),
                                },
                            );
                        }
                        let typed_initializer = initializer.map(|init| self.convert_initializer_to_typed(init, filename));
                        TypedForInit::Declaration(ty, name, typed_initializer)
                    }
                    ForInit::Expr(expr) => {
                        let typed_expr = self.check_expression(expr, filename);
                        TypedForInit::Expr(typed_expr)
                    }
                });

                let typed_cond = cond.map(|c| self.check_expression(*c, filename));
                let typed_inc = inc.map(|i| self.check_expression(*i, filename));
                let typed_body = Box::new(self.check_statement(*body, filename));

                TypedStmt::For(typed_init, typed_cond, typed_inc, typed_body)
            }
            Stmt::Block(stmts) => {
                self.symbol_table.push_scope();
                let typed_stmts = stmts.into_iter().map(|s| self.check_statement(s, filename)).collect();
                self.symbol_table.pop_scope();
                TypedStmt::Block(typed_stmts)
            }
            Stmt::Switch(expr, body) => {
                let typed_expr = self.check_expression(*expr, filename);
                let typed_body = Box::new(self.check_statement(*body, filename));
                TypedStmt::Switch(typed_expr, typed_body)
            }
            Stmt::Case(expr, body) => {
                let typed_expr = self.check_expression(*expr, filename);
                let typed_body = Box::new(self.check_statement(*body, filename));
                TypedStmt::Case(typed_expr, typed_body)
            }
            Stmt::Default(body) => {
                let typed_body = Box::new(self.check_statement(*body, filename));
                TypedStmt::Default(typed_body)
            }
            Stmt::Label(label, body) => {
                let typed_body = Box::new(self.check_statement(*body, filename));
                TypedStmt::Label(label, typed_body)
            }
            Stmt::Goto(label) => TypedStmt::Goto(label),
            Stmt::FunctionDeclaration(ty, name, params, is_variadic) => {
                TypedStmt::FunctionDeclaration(ty, name, params, is_variadic)
            }
            Stmt::Break => TypedStmt::Break,
            Stmt::Continue => TypedStmt::Continue,
            Stmt::DoWhile(body, cond) => {
                let typed_body = Box::new(self.check_statement(*body, filename));
                let typed_cond = self.check_expression(*cond, filename);
                TypedStmt::DoWhile(typed_body, typed_cond)
            }
            Stmt::Empty => TypedStmt::Empty,
        }
    }

    /// Checks an expression for semantic errors and returns a typed expression.
    fn check_expression(&mut self, expr: Expr, filename: &str) -> TypedExpr {
        // For now, we'll use a dummy type (Int) for all expressions. In a full implementation,
        // this would perform proper type checking and inference.
        let dummy_ty = Type::Int;

        match expr {
            Expr::Variable(name, location) => {
                if !self.symbol_table.contains_key(&name) && !self.enum_constants.contains_key(&name)
                {
                    self.errors.push((
                        SemanticError::UndefinedVariable(name.clone()),
                        filename.to_string(),
                        location.clone(),
                    ));
                }
                TypedExpr::Variable(name, location, dummy_ty)
            }
            Expr::Call(name, args, location) => {
                // Check if function exists
                if !self.symbol_table.contains_key(&name) {
                    self.errors.push((
                        SemanticError::UndefinedFunction(name.clone()),
                        filename.to_string(),
                        location.clone(),
                    ));
                }

                // Check arguments
                let typed_args: Vec<TypedExpr> = args.into_iter().map(|arg| self.check_expression(arg, filename)).collect();

                TypedExpr::Call(name, typed_args, location, dummy_ty)
            }
            Expr::Assign(lhs, rhs) => {
                let typed_lhs = self.check_expression(*lhs, filename);
                let typed_rhs = self.check_expression(*rhs, filename);
                TypedExpr::Assign(Box::new(typed_lhs), Box::new(typed_rhs), dummy_ty)
            }
            Expr::AssignAdd(lhs, rhs) => {
                let typed_lhs = self.check_expression(*lhs, filename);
                let typed_rhs = self.check_expression(*rhs, filename);
                TypedExpr::AssignAdd(Box::new(typed_lhs), Box::new(typed_rhs), dummy_ty)
            }
            Expr::AssignSub(lhs, rhs) => {
                let typed_lhs = self.check_expression(*lhs, filename);
                let typed_rhs = self.check_expression(*rhs, filename);
                TypedExpr::AssignSub(Box::new(typed_lhs), Box::new(typed_rhs), dummy_ty)
            }
            Expr::AssignMul(lhs, rhs) => {
                let typed_lhs = self.check_expression(*lhs, filename);
                let typed_rhs = self.check_expression(*rhs, filename);
                TypedExpr::AssignMul(Box::new(typed_lhs), Box::new(typed_rhs), dummy_ty)
            }
            Expr::AssignDiv(lhs, rhs) => {
                let typed_lhs = self.check_expression(*lhs, filename);
                let typed_rhs = self.check_expression(*rhs, filename);
                TypedExpr::AssignDiv(Box::new(typed_lhs), Box::new(typed_rhs), dummy_ty)
            }
            Expr::AssignMod(lhs, rhs) => {
                let typed_lhs = self.check_expression(*lhs, filename);
                let typed_rhs = self.check_expression(*rhs, filename);
                TypedExpr::AssignMod(Box::new(typed_lhs), Box::new(typed_rhs), dummy_ty)
            }
            Expr::AssignLeftShift(lhs, rhs) => {
                let typed_lhs = self.check_expression(*lhs, filename);
                let typed_rhs = self.check_expression(*rhs, filename);
                TypedExpr::AssignLeftShift(Box::new(typed_lhs), Box::new(typed_rhs), dummy_ty)
            }
            Expr::AssignRightShift(lhs, rhs) => {
                let typed_lhs = self.check_expression(*lhs, filename);
                let typed_rhs = self.check_expression(*rhs, filename);
                TypedExpr::AssignRightShift(Box::new(typed_lhs), Box::new(typed_rhs), dummy_ty)
            }
            Expr::AssignBitwiseAnd(lhs, rhs) => {
                let typed_lhs = self.check_expression(*lhs, filename);
                let typed_rhs = self.check_expression(*rhs, filename);
                TypedExpr::AssignBitwiseAnd(Box::new(typed_lhs), Box::new(typed_rhs), dummy_ty)
            }
            Expr::AssignBitwiseXor(lhs, rhs) => {
                let typed_lhs = self.check_expression(*lhs, filename);
                let typed_rhs = self.check_expression(*rhs, filename);
                TypedExpr::AssignBitwiseXor(Box::new(typed_lhs), Box::new(typed_rhs), dummy_ty)
            }
            Expr::AssignBitwiseOr(lhs, rhs) => {
                let typed_lhs = self.check_expression(*lhs, filename);
                let typed_rhs = self.check_expression(*rhs, filename);
                TypedExpr::AssignBitwiseOr(Box::new(typed_lhs), Box::new(typed_rhs), dummy_ty)
            }
            Expr::Add(lhs, rhs) => {
                let typed_lhs = self.check_expression(*lhs, filename);
                let typed_rhs = self.check_expression(*rhs, filename);
                TypedExpr::Add(Box::new(typed_lhs), Box::new(typed_rhs), dummy_ty)
            }
            Expr::Sub(lhs, rhs) => {
                let typed_lhs = self.check_expression(*lhs, filename);
                let typed_rhs = self.check_expression(*rhs, filename);
                TypedExpr::Sub(Box::new(typed_lhs), Box::new(typed_rhs), dummy_ty)
            }
            Expr::Mul(lhs, rhs) => {
                let typed_lhs = self.check_expression(*lhs, filename);
                let typed_rhs = self.check_expression(*rhs, filename);
                TypedExpr::Mul(Box::new(typed_lhs), Box::new(typed_rhs), dummy_ty)
            }
            Expr::Div(lhs, rhs) => {
                let typed_lhs = self.check_expression(*lhs, filename);
                let typed_rhs = self.check_expression(*rhs, filename);
                TypedExpr::Div(Box::new(typed_lhs), Box::new(typed_rhs), dummy_ty)
            }
            Expr::Mod(lhs, rhs) => {
                let typed_lhs = self.check_expression(*lhs, filename);
                let typed_rhs = self.check_expression(*rhs, filename);
                TypedExpr::Mod(Box::new(typed_lhs), Box::new(typed_rhs), dummy_ty)
            }
            Expr::Equal(lhs, rhs) => {
                let typed_lhs = self.check_expression(*lhs, filename);
                let typed_rhs = self.check_expression(*rhs, filename);
                TypedExpr::Equal(Box::new(typed_lhs), Box::new(typed_rhs), dummy_ty)
            }
            Expr::NotEqual(lhs, rhs) => {
                let typed_lhs = self.check_expression(*lhs, filename);
                let typed_rhs = self.check_expression(*rhs, filename);
                TypedExpr::NotEqual(Box::new(typed_lhs), Box::new(typed_rhs), dummy_ty)
            }
            Expr::LessThan(lhs, rhs) => {
                let typed_lhs = self.check_expression(*lhs, filename);
                let typed_rhs = self.check_expression(*rhs, filename);
                TypedExpr::LessThan(Box::new(typed_lhs), Box::new(typed_rhs), dummy_ty)
            }
            Expr::GreaterThan(lhs, rhs) => {
                let typed_lhs = self.check_expression(*lhs, filename);
                let typed_rhs = self.check_expression(*rhs, filename);
                TypedExpr::GreaterThan(Box::new(typed_lhs), Box::new(typed_rhs), dummy_ty)
            }
            Expr::LessThanOrEqual(lhs, rhs) => {
                let typed_lhs = self.check_expression(*lhs, filename);
                let typed_rhs = self.check_expression(*rhs, filename);
                TypedExpr::LessThanOrEqual(Box::new(typed_lhs), Box::new(typed_rhs), dummy_ty)
            }
            Expr::GreaterThanOrEqual(lhs, rhs) => {
                let typed_lhs = self.check_expression(*lhs, filename);
                let typed_rhs = self.check_expression(*rhs, filename);
                TypedExpr::GreaterThanOrEqual(Box::new(typed_lhs), Box::new(typed_rhs), dummy_ty)
            }
            Expr::LogicalAnd(lhs, rhs) => {
                let typed_lhs = self.check_expression(*lhs, filename);
                let typed_rhs = self.check_expression(*rhs, filename);
                TypedExpr::LogicalAnd(Box::new(typed_lhs), Box::new(typed_rhs), dummy_ty)
            }
            Expr::LogicalOr(lhs, rhs) => {
                let typed_lhs = self.check_expression(*lhs, filename);
                let typed_rhs = self.check_expression(*rhs, filename);
                TypedExpr::LogicalOr(Box::new(typed_lhs), Box::new(typed_rhs), dummy_ty)
            }
            Expr::BitwiseOr(lhs, rhs) => {
                let typed_lhs = self.check_expression(*lhs, filename);
                let typed_rhs = self.check_expression(*rhs, filename);
                TypedExpr::BitwiseOr(Box::new(typed_lhs), Box::new(typed_rhs), dummy_ty)
            }
            Expr::BitwiseXor(lhs, rhs) => {
                let typed_lhs = self.check_expression(*lhs, filename);
                let typed_rhs = self.check_expression(*rhs, filename);
                TypedExpr::BitwiseXor(Box::new(typed_lhs), Box::new(typed_rhs), dummy_ty)
            }
            Expr::BitwiseAnd(lhs, rhs) => {
                let typed_lhs = self.check_expression(*lhs, filename);
                let typed_rhs = self.check_expression(*rhs, filename);
                TypedExpr::BitwiseAnd(Box::new(typed_lhs), Box::new(typed_rhs), dummy_ty)
            }
            Expr::LeftShift(lhs, rhs) => {
                let typed_lhs = self.check_expression(*lhs, filename);
                let typed_rhs = self.check_expression(*rhs, filename);
                TypedExpr::LeftShift(Box::new(typed_lhs), Box::new(typed_rhs), dummy_ty)
            }
            Expr::RightShift(lhs, rhs) => {
                let typed_lhs = self.check_expression(*lhs, filename);
                let typed_rhs = self.check_expression(*rhs, filename);
                TypedExpr::RightShift(Box::new(typed_lhs), Box::new(typed_rhs), dummy_ty)
            }
            Expr::Comma(lhs, rhs) => {
                let typed_lhs = self.check_expression(*lhs, filename);
                let typed_rhs = self.check_expression(*rhs, filename);
                TypedExpr::Comma(Box::new(typed_lhs), Box::new(typed_rhs), dummy_ty)
            }
            Expr::Neg(expr) => {
                let typed_expr = self.check_expression(*expr, filename);
                TypedExpr::Neg(Box::new(typed_expr), dummy_ty)
            }
            Expr::LogicalNot(expr) => {
                let typed_expr = self.check_expression(*expr, filename);
                TypedExpr::LogicalNot(Box::new(typed_expr), dummy_ty)
            }
            Expr::BitwiseNot(expr) => {
                let typed_expr = self.check_expression(*expr, filename);
                TypedExpr::BitwiseNot(Box::new(typed_expr), dummy_ty)
            }
            Expr::Sizeof(expr) => {
                let typed_expr = self.check_expression(*expr, filename);
                TypedExpr::Sizeof(Box::new(typed_expr), dummy_ty)
            }
            Expr::Deref(expr) => {
                let typed_expr = self.check_expression(*expr, filename);
                TypedExpr::Deref(Box::new(typed_expr), dummy_ty)
            }
            Expr::AddressOf(expr) => {
                let typed_expr = self.check_expression(*expr, filename);
                TypedExpr::AddressOf(Box::new(typed_expr), dummy_ty)
            }
            Expr::SizeofType(ty) => {
                TypedExpr::SizeofType(ty, dummy_ty)
            }
            Expr::Ternary(cond, then_expr, else_expr) => {
                let typed_cond = self.check_expression(*cond, filename);
                let typed_then = self.check_expression(*then_expr, filename);
                let typed_else = self.check_expression(*else_expr, filename);
                TypedExpr::Ternary(Box::new(typed_cond), Box::new(typed_then), Box::new(typed_else), dummy_ty)
            }
            Expr::Member(expr, member) => {
                let typed_expr = self.check_expression(*expr, filename);
                TypedExpr::Member(Box::new(typed_expr), member, dummy_ty)
            }
            Expr::PointerMember(expr, member) => {
                let typed_expr = self.check_expression(*expr, filename);
                TypedExpr::PointerMember(Box::new(typed_expr), member, dummy_ty)
            }
            Expr::InitializerList(list) => {
                let typed_list = list.into_iter().map(|(designators, initializer)| {
                    let typed_designators = designators.into_iter().map(|d| match d {
                        Designator::Index(expr) => TypedDesignator::Index(Box::new(self.check_expression(*expr, filename))),
                        Designator::Member(name) => TypedDesignator::Member(name),
                    }).collect();
                    let typed_initializer = self.convert_initializer_to_typed(*initializer, filename);
                    (typed_designators, Box::new(typed_initializer))
                }).collect();
                TypedExpr::InitializerList(typed_list, dummy_ty)
            }
            Expr::ExplicitCast(ty, expr) => {
                let typed_expr = self.check_expression(*expr, filename);
                TypedExpr::ExplicitCast(Box::new(*ty.clone()), Box::new(typed_expr), *ty.clone())
            }
            Expr::ImplicitCast(ty, expr) => {
                let typed_expr = self.check_expression(*expr, filename);
                TypedExpr::ImplicitCast(Box::new(*ty.clone()), Box::new(typed_expr), *ty.clone())
            }
            Expr::CompoundLiteral(ty, initializer) => {
                let typed_initializer = self.convert_initializer_to_typed(*initializer, filename);
                TypedExpr::CompoundLiteral(Box::new(*ty.clone()), Box::new(typed_initializer), *ty.clone())
            }
            // Literals don't need checking
            Expr::Number(n) => TypedExpr::Number(n, dummy_ty),
            Expr::String(s) => TypedExpr::String(s, dummy_ty),
            Expr::Char(c) => TypedExpr::Char(c, dummy_ty),
            Expr::PreIncrement(expr) => {
                let typed_expr = self.check_expression(*expr, filename);
                TypedExpr::PreIncrement(Box::new(typed_expr), dummy_ty)
            }
            Expr::PreDecrement(expr) => {
                let typed_expr = self.check_expression(*expr, filename);
                TypedExpr::PreDecrement(Box::new(typed_expr), dummy_ty)
            }
            Expr::PostIncrement(expr) => {
                let typed_expr = self.check_expression(*expr, filename);
                TypedExpr::PostIncrement(Box::new(typed_expr), dummy_ty)
            }
            Expr::PostDecrement(expr) => {
                let typed_expr = self.check_expression(*expr, filename);
                TypedExpr::PostDecrement(Box::new(typed_expr), dummy_ty)
            }
        }
    }

    fn check_initializer(&mut self, initializer: &Initializer, filename: &str) {
        match initializer {
            Initializer::Expr(expr) => {
                self.check_expression((**expr).clone(), filename);
            }
            Initializer::List(list) => {
                for (_, initializer) in list {
                    self.check_initializer(initializer, filename);
                }
            }
        }
    }

    fn check_typed_expression(&mut self, expr: TypedExpr, filename: &str) {
        // For now, just check for errors in the expression
        // This is a placeholder - in a full implementation, this would perform additional checks
        match expr {
            TypedExpr::Variable(name, location, _) => {
                if !self.symbol_table.contains_key(&name) && !self.enum_constants.contains_key(&name) {
                    self.errors.push((
                        SemanticError::UndefinedVariable(name.clone()),
                        filename.to_string(),
                        location.clone(),
                    ));
                }
            }
            TypedExpr::Call(name, args, location, _) => {
                if !self.symbol_table.contains_key(&name) {
                    self.errors.push((
                        SemanticError::UndefinedFunction(name.clone()),
                        filename.to_string(),
                        location.clone(),
                    ));
                }
                for arg in args {
                    self.check_typed_expression(arg, filename);
                }
            }
            // Add other cases as needed
            _ => {
                // For other expressions, recursively check subexpressions
                // This is simplified - a full implementation would handle all cases
            }
        }
    }

    fn check_typed_initializer(&mut self, initializer: &TypedInitializer, filename: &str) {
        match initializer {
            TypedInitializer::Expr(expr) => {
                self.check_typed_expression((**expr).clone(), filename);
            }
            TypedInitializer::List(list) => {
                for (_, initializer) in list {
                    self.check_typed_initializer(initializer, filename);
                }
            }
        }
    }

    fn convert_initializer_to_typed(&mut self, initializer: Initializer, filename: &str) -> TypedInitializer {
        match initializer {
            Initializer::Expr(expr) => {
                let typed_expr = self.check_expression(*expr, filename);
                TypedInitializer::Expr(Box::new(typed_expr))
            }
            Initializer::List(list) => {
                let typed_list = list.into_iter().map(|(designators, initializer)| {
                    let typed_designators = designators.into_iter().map(|d| match d {
                        Designator::Index(expr) => TypedDesignator::Index(Box::new(self.check_expression(*expr, filename))),
                        Designator::Member(name) => TypedDesignator::Member(name),
                    }).collect();
                    let typed_initializer = self.convert_initializer_to_typed(*initializer, filename);
                    (typed_designators, Box::new(typed_initializer))
                }).collect();
                TypedInitializer::List(typed_list)
            }
        }
    }

    fn check_type(&mut self, ty: &Type, filename: &str) {
        match ty {
            Type::Pointer(base_ty) => {
                self.check_type(base_ty, filename);
            }
            Type::Array(base_ty, _) => {
                self.check_type(base_ty, filename);
            }
            Type::Struct(_, members) => {
                for member in members {
                    self.check_type(&member.ty, filename);
                }
            }
            Type::Union(_, members) => {
                for member in members {
                    self.check_type(&member.ty, filename);
                }
            }
            _ => {
                // Primitive types don't need checking
            }
        }
    }
}

/// Analyzes a translation unit and produces a typed translation unit with resolved types.
pub fn analyze_translation_unit(unit: Program) -> TypedTranslationUnit {
    let mut symtab = SymbolTable::new();

    // Collect global symbols
    for global in &unit.globals {
        match global {
            Stmt::Declaration(ty, declarators) => {
                for declarator in declarators {
                    symtab.insert(
                        declarator.name.clone(),
                        Symbol {
                            ty: declarator.ty.clone(),
                            is_function: false,
                            defined_at: "global".to_string(),
                        },
                    );
                }
            }
            Stmt::FunctionDeclaration(ty, name, _, _) => {
                symtab.insert(
                    name.clone(),
                    Symbol {
                        ty: ty.clone(),
                        is_function: true,
                        defined_at: "global".to_string(),
                    },
                );
            }
            _ => {}
        }
    }

    // Collect function symbols
    for function in &unit.functions {
        symtab.insert(
            function.name.clone(),
            Symbol {
                ty: function.return_type.clone(),
                is_function: true,
                defined_at: "global".to_string(),
            },
        );
    }

    // Analyze functions
    let typed_functions = unit
        .functions
        .into_iter()
        .map(|f| analyze_function(f, &mut symtab))
        .collect();

    // Analyze global statements
    let typed_globals = unit
        .globals
        .into_iter()
        .map(|s| analyze_stmt(s, &mut symtab))
        .collect();

    TypedTranslationUnit {
        globals: typed_globals,
        functions: typed_functions,
    }
}

/// Converts an initializer to a typed initializer using the analyze functions.
fn convert_initializer_to_typed_analyze(initializer: Initializer, symtab: &SymbolTable) -> TypedInitializer {
    match initializer {
        Initializer::Expr(expr) => {
            let typed_expr = analyze_expr(*expr, symtab);
            TypedInitializer::Expr(Box::new(typed_expr))
        }
        Initializer::List(list) => {
            let typed_list = list.into_iter().map(|(designators, initializer)| {
                let typed_designators = designators.into_iter().map(|d| match d {
                    Designator::Index(expr) => TypedDesignator::Index(Box::new(analyze_expr(*expr, symtab))),
                    Designator::Member(name) => TypedDesignator::Member(name),
                }).collect();
                let typed_initializer = convert_initializer_to_typed_analyze(*initializer, symtab);
                (typed_designators, Box::new(typed_initializer))
            }).collect();
            TypedInitializer::List(typed_list)
        }
    }
}

/// Analyzes a function and produces a typed function declaration.
pub fn analyze_function(func: Function, symtab: &mut SymbolTable) -> TypedFunctionDecl {
    // Push function scope
    symtab.push_scope();

    // Add parameters to symbol table
    for param in &func.params {
        symtab.insert(
            param.name.clone(),
            Symbol {
                ty: param.ty.clone(),
                is_function: false,
                defined_at: "parameter".to_string(),
            },
        );
    }

    // Analyze function body
    let typed_body = func
        .body
        .into_iter()
        .map(|stmt| analyze_stmt(stmt, symtab))
        .collect();

    // Pop function scope
    symtab.pop_scope();

    TypedFunctionDecl {
        return_type: func.return_type,
        name: func.name,
        params: func.params,
        body: typed_body,
        is_inline: func.is_inline,
        is_variadic: func.is_variadic,
    }
}

/// Analyzes a statement and produces a typed statement.
pub fn analyze_stmt(stmt: Stmt, symtab: &mut SymbolTable) -> TypedStmt {
    match stmt {
        Stmt::Declaration(ty, declarators) => {
            // Add declarators to symbol table
            let mut typed_declarators = Vec::new();
            for declarator in declarators {
                symtab.insert(
                    declarator.name.clone(),
                    Symbol {
                        ty: declarator.ty.clone(),
                        is_function: false,
                        defined_at: "local".to_string(),
                    },
                );
                let typed_initializer = declarator.initializer.map(|init| convert_initializer_to_typed_analyze(init, symtab));
                typed_declarators.push(TypedDeclarator {
                    ty: declarator.ty,
                    name: declarator.name,
                    initializer: typed_initializer,
                });
            }
            TypedStmt::Declaration(ty, typed_declarators)
        }
        Stmt::Expr(expr) => {
            let typed_expr = analyze_expr(expr, symtab);
            TypedStmt::Expr(typed_expr)
        }
        Stmt::Return(expr) => {
            let typed_expr = analyze_expr(expr, symtab);
            TypedStmt::Return(typed_expr)
        }
        Stmt::If(cond, then, otherwise) => {
            let typed_cond = analyze_expr(*cond, symtab);
            let typed_then = Box::new(analyze_stmt(*then, symtab));
            let typed_otherwise = otherwise.map(|o| Box::new(analyze_stmt(*o, symtab)));
            TypedStmt::If(typed_cond, typed_then, typed_otherwise)
        }
        Stmt::While(cond, body) => {
            let typed_cond = analyze_expr(*cond, symtab);
            let typed_body = Box::new(analyze_stmt(*body, symtab));
            TypedStmt::While(typed_cond, typed_body)
        }
        Stmt::For(init, cond, inc, body) => {
            let typed_init = init.map(|i| match i {
                ForInit::Declaration(ty, name, initializer) => {
                    symtab.insert(
                        name.clone(),
                        Symbol {
                            ty: ty.clone(),
                            is_function: false,
                            defined_at: "for".to_string(),
                        },
                    );
                    let typed_initializer = initializer.map(|init| convert_initializer_to_typed_analyze(init, symtab));
                    TypedForInit::Declaration(ty, name, typed_initializer)
                }
                ForInit::Expr(expr) => TypedForInit::Expr(analyze_expr(expr, symtab)),
            });

            let typed_cond = cond.map(|c| analyze_expr(*c, symtab));
            let typed_inc = inc.map(|i| analyze_expr(*i, symtab));
            let typed_body = Box::new(analyze_stmt(*body, symtab));

            TypedStmt::For(typed_init, typed_cond, typed_inc, typed_body)
        }
        Stmt::Block(stmts) => {
            symtab.push_scope();
            let typed_stmts = stmts
                .into_iter()
                .map(|s| analyze_stmt(s, symtab))
                .collect();
            symtab.pop_scope();
            TypedStmt::Block(typed_stmts)
        }
        Stmt::Switch(expr, body) => {
            let typed_expr = analyze_expr(*expr, symtab);
            let typed_body = Box::new(analyze_stmt(*body, symtab));
            TypedStmt::Switch(typed_expr, typed_body)
        }
        Stmt::Case(expr, body) => {
            let typed_expr = analyze_expr(*expr, symtab);
            let typed_body = Box::new(analyze_stmt(*body, symtab));
            TypedStmt::Case(typed_expr, typed_body)
        }
        Stmt::Default(body) => {
            let typed_body = Box::new(analyze_stmt(*body, symtab));
            TypedStmt::Default(typed_body)
        }
        Stmt::Label(label, body) => {
            let typed_body = Box::new(analyze_stmt(*body, symtab));
            TypedStmt::Label(label, typed_body)
        }
        Stmt::Goto(label) => TypedStmt::Goto(label),
        Stmt::FunctionDeclaration(ty, name, params, is_variadic) => {
            TypedStmt::FunctionDeclaration(ty, name, params, is_variadic)
        }
        Stmt::Break => TypedStmt::Break,
        Stmt::Continue => TypedStmt::Continue,
        Stmt::DoWhile(body, cond) => {
            let typed_body = Box::new(analyze_stmt(*body, symtab));
            let typed_cond = analyze_expr(*cond, symtab);
            TypedStmt::DoWhile(typed_body, typed_cond)
        }
        Stmt::Empty => TypedStmt::Empty,
    }
}

/// Performs integer promotions on a type.
fn integer_promote(ty: &Type) -> Type {
    match ty {
        Type::Bool | Type::Char | Type::UnsignedChar | Type::Short | Type::UnsignedShort => Type::Int,
        _ => ty.clone(),
    }
}

/// Applies usual arithmetic conversions to two types.
fn apply_usual_arithmetic_conversions(lhs_ty: &Type, rhs_ty: &Type) -> (Type, Type) {
    // If both types are the same, no conversion needed
    if lhs_ty == rhs_ty {
        return (lhs_ty.clone(), rhs_ty.clone());
    }

    // If one is long double, convert both to long double
    // But we don't have long double, so skip

    // If one is double, convert both to double
    if *lhs_ty == Type::Double || *rhs_ty == Type::Double {
        return (Type::Double, Type::Double);
    }

    // If one is float, convert both to float
    if *lhs_ty == Type::Float || *rhs_ty == Type::Float {
        return (Type::Float, Type::Float);
    }

    // Both are integer types, apply integer conversion rules
    let lhs_rank = lhs_ty.get_arithmetic_rank();
    let rhs_rank = rhs_ty.get_arithmetic_rank();

    if lhs_rank > rhs_rank {
        (lhs_ty.clone(), lhs_ty.clone())
    } else if rhs_rank > lhs_rank {
        (rhs_ty.clone(), rhs_ty.clone())
    } else {
        // Same rank, check signedness
        match (lhs_ty, rhs_ty) {
            (Type::UnsignedLongLong, _) => (Type::UnsignedLongLong, Type::UnsignedLongLong),
            (_, Type::UnsignedLongLong) => (Type::UnsignedLongLong, Type::UnsignedLongLong),
            (Type::LongLong, _) => (Type::LongLong, Type::LongLong),
            (_, Type::LongLong) => (Type::LongLong, Type::LongLong),
            (Type::UnsignedLong, _) => (Type::UnsignedLong, Type::UnsignedLong),
            (_, Type::UnsignedLong) => (Type::UnsignedLong, Type::UnsignedLong),
            (Type::Long, _) => (Type::Long, Type::Long),
            (_, Type::Long) => (Type::Long, Type::Long),
            (Type::UnsignedInt, _) => (Type::UnsignedInt, Type::UnsignedInt),
            (_, Type::UnsignedInt) => (Type::UnsignedInt, Type::UnsignedInt),
            _ => (Type::Int, Type::Int),
        }
    }
}

/// Analyzes an expression and produces a typed expression with resolved types.
pub fn analyze_expr(expr: Expr, symtab: &SymbolTable) -> TypedExpr {
    match expr {
        Expr::Variable(name, span) => {
            // Look up variable type in symbol table
            let ty = symtab
                .lookup(&name)
                .map(|s| s.ty.clone())
                .unwrap_or(Type::Int); // Fallback to int if not found
            // Apply integer promotions for variables
            let promoted_ty = integer_promote(&ty);
            TypedExpr::Variable(name, span, promoted_ty)
        }
        Expr::Number(n) => TypedExpr::Number(n, Type::Int),
        Expr::String(s) => TypedExpr::String(s, Type::Pointer(Box::new(Type::Char))),
        Expr::Char(c) => TypedExpr::Char(c, Type::Char),
        Expr::Call(name, args, span) => {
            // Look up function return type
            let return_ty = symtab
                .lookup(&name)
                .map(|s| s.ty.clone())
                .unwrap_or(Type::Int);
            let typed_args = args
                .into_iter()
                .map(|arg| analyze_expr(arg, symtab))
                .collect::<Vec<_>>();
            TypedExpr::Call(name, typed_args, span, return_ty)
        }
        Expr::Assign(lhs, rhs) => {
            let lhs_typed = analyze_expr(*lhs, symtab);
            let rhs_typed = analyze_expr(*rhs, symtab);
            // Insert implicit cast if types don't match
            let cast_rhs = if lhs_typed.ty() == rhs_typed.ty() {
                rhs_typed
            } else {
                TypedExpr::ImplicitCast(Box::new(lhs_typed.ty().clone()), Box::new(rhs_typed), lhs_typed.ty().clone())
            };
            TypedExpr::Assign(Box::new(lhs_typed.clone()), Box::new(cast_rhs), lhs_typed.ty().clone())
        }
        // Handle compound assignments similarly
        Expr::AssignAdd(lhs, rhs) => {
            let lhs_typed = analyze_expr(*lhs, symtab);
            let rhs_typed = analyze_expr(*rhs, symtab);
            // Apply usual arithmetic conversions for compound assignments
            let (lhs_conv_ty, rhs_conv_ty) = apply_usual_arithmetic_conversions(lhs_typed.ty(), rhs_typed.ty());
            let rhs_cast = if *rhs_typed.ty() != rhs_conv_ty {
                TypedExpr::ImplicitCast(Box::new(rhs_conv_ty.clone()), Box::new(rhs_typed), rhs_conv_ty.clone())
            } else {
                rhs_typed
            };
            TypedExpr::AssignAdd(Box::new(lhs_typed.clone()), Box::new(rhs_cast), lhs_typed.ty().clone())
        }
        Expr::AssignSub(lhs, rhs) => {
            let lhs_typed = analyze_expr(*lhs, symtab);
            let rhs_typed = analyze_expr(*rhs, symtab);
            let (lhs_conv_ty, rhs_conv_ty) = apply_usual_arithmetic_conversions(lhs_typed.ty(), rhs_typed.ty());
            let rhs_cast = if *rhs_typed.ty() != rhs_conv_ty {
                TypedExpr::ImplicitCast(Box::new(rhs_conv_ty.clone()), Box::new(rhs_typed), rhs_conv_ty.clone())
            } else {
                rhs_typed
            };
            TypedExpr::AssignSub(Box::new(lhs_typed.clone()), Box::new(rhs_cast), lhs_typed.ty().clone())
        }
        Expr::AssignMul(lhs, rhs) => {
            let lhs_typed = analyze_expr(*lhs, symtab);
            let rhs_typed = analyze_expr(*rhs, symtab);
            let (lhs_conv_ty, rhs_conv_ty) = apply_usual_arithmetic_conversions(lhs_typed.ty(), rhs_typed.ty());
            let rhs_cast = if *rhs_typed.ty() != rhs_conv_ty {
                TypedExpr::ImplicitCast(Box::new(rhs_conv_ty.clone()), Box::new(rhs_typed), rhs_conv_ty.clone())
            } else {
                rhs_typed
            };
            TypedExpr::AssignMul(Box::new(lhs_typed.clone()), Box::new(rhs_cast), lhs_typed.ty().clone())
        }
        Expr::AssignDiv(lhs, rhs) => {
            let lhs_typed = analyze_expr(*lhs, symtab);
            let rhs_typed = analyze_expr(*rhs, symtab);
            let (lhs_conv_ty, rhs_conv_ty) = apply_usual_arithmetic_conversions(lhs_typed.ty(), rhs_typed.ty());
            let rhs_cast = if *rhs_typed.ty() != rhs_conv_ty {
                TypedExpr::ImplicitCast(Box::new(rhs_conv_ty.clone()), Box::new(rhs_typed), rhs_conv_ty.clone())
            } else {
                rhs_typed
            };
            TypedExpr::AssignDiv(Box::new(lhs_typed.clone()), Box::new(rhs_cast), lhs_typed.ty().clone())
        }
        Expr::AssignMod(lhs, rhs) => {
            let lhs_typed = analyze_expr(*lhs, symtab);
            let rhs_typed = analyze_expr(*rhs, symtab);
            let (lhs_conv_ty, rhs_conv_ty) = apply_usual_arithmetic_conversions(lhs_typed.ty(), rhs_typed.ty());
            let rhs_cast = if *rhs_typed.ty() != rhs_conv_ty {
                TypedExpr::ImplicitCast(Box::new(rhs_conv_ty.clone()), Box::new(rhs_typed), rhs_conv_ty.clone())
            } else {
                rhs_typed
            };
            TypedExpr::AssignMod(Box::new(lhs_typed.clone()), Box::new(rhs_cast), lhs_typed.ty().clone())
        }
        Expr::AssignLeftShift(lhs, rhs) => {
            let lhs_typed = analyze_expr(*lhs, symtab);
            let rhs_typed = analyze_expr(*rhs, symtab);
            TypedExpr::AssignLeftShift(Box::new(lhs_typed.clone()), Box::new(rhs_typed), lhs_typed.ty().clone())
        }
        Expr::AssignRightShift(lhs, rhs) => {
            let lhs_typed = analyze_expr(*lhs, symtab);
            let rhs_typed = analyze_expr(*rhs, symtab);
            TypedExpr::AssignRightShift(Box::new(lhs_typed.clone()), Box::new(rhs_typed), lhs_typed.ty().clone())
        }
        Expr::AssignBitwiseAnd(lhs, rhs) => {
            let lhs_typed = analyze_expr(*lhs, symtab);
            let rhs_typed = analyze_expr(*rhs, symtab);
            TypedExpr::AssignBitwiseAnd(Box::new(lhs_typed.clone()), Box::new(rhs_typed), lhs_typed.ty().clone())
        }
        Expr::AssignBitwiseXor(lhs, rhs) => {
            let lhs_typed = analyze_expr(*lhs, symtab);
            let rhs_typed = analyze_expr(*rhs, symtab);
            TypedExpr::AssignBitwiseXor(Box::new(lhs_typed.clone()), Box::new(rhs_typed), lhs_typed.ty().clone())
        }
        Expr::AssignBitwiseOr(lhs, rhs) => {
            let lhs_typed = analyze_expr(*lhs, symtab);
            let rhs_typed = analyze_expr(*rhs, symtab);
            TypedExpr::AssignBitwiseOr(Box::new(lhs_typed.clone()), Box::new(rhs_typed), lhs_typed.ty().clone())
        }
        // Binary arithmetic operations
        Expr::Add(lhs, rhs) => {
            let lhs_typed = analyze_expr(*lhs, symtab);
            let rhs_typed = analyze_expr(*rhs, symtab);
            let (lhs_conv_ty, rhs_conv_ty) = apply_usual_arithmetic_conversions(lhs_typed.ty(), rhs_typed.ty());
            let lhs_cast = if *lhs_typed.ty() != lhs_conv_ty {
                TypedExpr::ImplicitCast(Box::new(lhs_conv_ty.clone()), Box::new(lhs_typed), lhs_conv_ty.clone())
            } else {
                lhs_typed
            };
            let rhs_cast = if *rhs_typed.ty() != rhs_conv_ty {
                TypedExpr::ImplicitCast(Box::new(rhs_conv_ty.clone()), Box::new(rhs_typed), rhs_conv_ty.clone())
            } else {
                rhs_typed
            };
            let result_ty = match (&lhs_conv_ty, &rhs_conv_ty) {
                (Type::Pointer(_), Type::Int) => lhs_conv_ty.clone(),
                (Type::Int, Type::Pointer(_)) => rhs_conv_ty.clone(),
                _ => lhs_conv_ty.clone(),
            };
            TypedExpr::Add(Box::new(lhs_cast), Box::new(rhs_cast), result_ty)
        }
        Expr::Sub(lhs, rhs) => {
            let lhs_typed = analyze_expr(*lhs, symtab);
            let rhs_typed = analyze_expr(*rhs, symtab);
            let (lhs_conv_ty, rhs_conv_ty) = apply_usual_arithmetic_conversions(lhs_typed.ty(), rhs_typed.ty());
            let lhs_cast = if *lhs_typed.ty() != lhs_conv_ty {
                TypedExpr::ImplicitCast(Box::new(lhs_conv_ty.clone()), Box::new(lhs_typed), lhs_conv_ty.clone())
            } else {
                lhs_typed
            };
            let rhs_cast = if *rhs_typed.ty() != rhs_conv_ty {
                TypedExpr::ImplicitCast(Box::new(rhs_conv_ty.clone()), Box::new(rhs_typed), rhs_conv_ty.clone())
            } else {
                rhs_typed
            };
            let result_ty = match (&lhs_conv_ty, &rhs_conv_ty) {
                (Type::Pointer(_), Type::Int) => lhs_conv_ty.clone(),
                (Type::Pointer(_), Type::Pointer(_)) => Type::Int, // ptrdiff_t, but use int
                _ => lhs_conv_ty.clone(),
            };
            TypedExpr::Sub(Box::new(lhs_cast), Box::new(rhs_cast), result_ty)
        }
        Expr::Mul(lhs, rhs) => {
            let lhs_typed = analyze_expr(*lhs, symtab);
            let rhs_typed = analyze_expr(*rhs, symtab);
            let (lhs_conv_ty, rhs_conv_ty) = apply_usual_arithmetic_conversions(lhs_typed.ty(), rhs_typed.ty());
            let lhs_cast = if *lhs_typed.ty() != lhs_conv_ty {
                TypedExpr::ImplicitCast(Box::new(lhs_conv_ty.clone()), Box::new(lhs_typed), lhs_conv_ty.clone())
            } else {
                lhs_typed
            };
            let rhs_cast = if *rhs_typed.ty() != rhs_conv_ty {
                TypedExpr::ImplicitCast(Box::new(rhs_conv_ty.clone()), Box::new(rhs_typed), rhs_conv_ty.clone())
            } else {
                rhs_typed
            };
            TypedExpr::Mul(Box::new(lhs_cast), Box::new(rhs_cast), lhs_conv_ty.clone())
        }
        Expr::Div(lhs, rhs) => {
            let lhs_typed = analyze_expr(*lhs, symtab);
            let rhs_typed = analyze_expr(*rhs, symtab);
            let (lhs_conv_ty, rhs_conv_ty) = apply_usual_arithmetic_conversions(lhs_typed.ty(), rhs_typed.ty());
            let lhs_cast = if *lhs_typed.ty() != lhs_conv_ty {
                TypedExpr::ImplicitCast(Box::new(lhs_conv_ty.clone()), Box::new(lhs_typed), lhs_conv_ty.clone())
            } else {
                lhs_typed
            };
            let rhs_cast = if *rhs_typed.ty() != rhs_conv_ty {
                TypedExpr::ImplicitCast(Box::new(rhs_conv_ty.clone()), Box::new(rhs_typed), rhs_conv_ty.clone())
            } else {
                rhs_typed
            };
            TypedExpr::Div(Box::new(lhs_cast), Box::new(rhs_cast), lhs_conv_ty.clone())
        }
        Expr::Mod(lhs, rhs) => {
            let lhs_typed = analyze_expr(*lhs, symtab);
            let rhs_typed = analyze_expr(*rhs, symtab);
            let (lhs_conv_ty, rhs_conv_ty) = apply_usual_arithmetic_conversions(lhs_typed.ty(), rhs_typed.ty());
            let lhs_cast = if *lhs_typed.ty() != lhs_conv_ty {
                TypedExpr::ImplicitCast(Box::new(lhs_conv_ty.clone()), Box::new(lhs_typed), lhs_conv_ty.clone())
            } else {
                lhs_typed
            };
            let rhs_cast = if *rhs_typed.ty() != rhs_conv_ty {
                TypedExpr::ImplicitCast(Box::new(rhs_conv_ty.clone()), Box::new(rhs_typed), rhs_conv_ty.clone())
            } else {
                rhs_typed
            };
            TypedExpr::Mod(Box::new(lhs_cast), Box::new(rhs_cast), lhs_conv_ty.clone())
        }
        // Comparison operations return int
        Expr::Equal(lhs, rhs) => {
            let lhs_typed = analyze_expr(*lhs, symtab);
            let rhs_typed = analyze_expr(*rhs, symtab);
            TypedExpr::Equal(Box::new(lhs_typed), Box::new(rhs_typed), Type::Int)
        }
        Expr::NotEqual(lhs, rhs) => {
            let lhs_typed = analyze_expr(*lhs, symtab);
            let rhs_typed = analyze_expr(*rhs, symtab);
            TypedExpr::NotEqual(Box::new(lhs_typed), Box::new(rhs_typed), Type::Int)
        }
        Expr::LessThan(lhs, rhs) => {
            let lhs_typed = analyze_expr(*lhs, symtab);
            let rhs_typed = analyze_expr(*rhs, symtab);
            TypedExpr::LessThan(Box::new(lhs_typed), Box::new(rhs_typed), Type::Int)
        }
        Expr::GreaterThan(lhs, rhs) => {
            let lhs_typed = analyze_expr(*lhs, symtab);
            let rhs_typed = analyze_expr(*rhs, symtab);
            TypedExpr::GreaterThan(Box::new(lhs_typed), Box::new(rhs_typed), Type::Int)
        }
        Expr::LessThanOrEqual(lhs, rhs) => {
            let lhs_typed = analyze_expr(*lhs, symtab);
            let rhs_typed = analyze_expr(*rhs, symtab);
            TypedExpr::LessThanOrEqual(Box::new(lhs_typed), Box::new(rhs_typed), Type::Int)
        }
        Expr::GreaterThanOrEqual(lhs, rhs) => {
            let lhs_typed = analyze_expr(*lhs, symtab);
            let rhs_typed = analyze_expr(*rhs, symtab);
            TypedExpr::GreaterThanOrEqual(Box::new(lhs_typed), Box::new(rhs_typed), Type::Int)
        }
        // Logical operations return int
        Expr::LogicalAnd(lhs, rhs) => {
            let lhs_typed = analyze_expr(*lhs, symtab);
            let rhs_typed = analyze_expr(*rhs, symtab);
            TypedExpr::LogicalAnd(Box::new(lhs_typed), Box::new(rhs_typed), Type::Int)
        }
        Expr::LogicalOr(lhs, rhs) => {
            let lhs_typed = analyze_expr(*lhs, symtab);
            let rhs_typed = analyze_expr(*rhs, symtab);
            TypedExpr::LogicalOr(Box::new(lhs_typed), Box::new(rhs_typed), Type::Int)
        }
        // Bitwise operations
        Expr::BitwiseOr(lhs, rhs) => {
            let lhs_typed = analyze_expr(*lhs, symtab);
            let rhs_typed = analyze_expr(*rhs, symtab);
            TypedExpr::BitwiseOr(Box::new(lhs_typed), Box::new(rhs_typed), Type::Int)
        }
        Expr::BitwiseXor(lhs, rhs) => {
            let lhs_typed = analyze_expr(*lhs, symtab);
            let rhs_typed = analyze_expr(*rhs, symtab);
            TypedExpr::BitwiseXor(Box::new(lhs_typed), Box::new(rhs_typed), Type::Int)
        }
        Expr::BitwiseAnd(lhs, rhs) => {
            let lhs_typed = analyze_expr(*lhs, symtab);
            let rhs_typed = analyze_expr(*rhs, symtab);
            TypedExpr::BitwiseAnd(Box::new(lhs_typed), Box::new(rhs_typed), Type::Int)
        }
        Expr::LeftShift(lhs, rhs) => {
            let lhs_typed = analyze_expr(*lhs, symtab);
            let rhs_typed = analyze_expr(*rhs, symtab);
            TypedExpr::LeftShift(Box::new(lhs_typed.clone()), Box::new(rhs_typed), lhs_typed.ty().clone())
        }
        Expr::RightShift(lhs, rhs) => {
            let lhs_typed = analyze_expr(*lhs, symtab);
            let rhs_typed = analyze_expr(*rhs, symtab);
            TypedExpr::RightShift(Box::new(lhs_typed.clone()), Box::new(rhs_typed), lhs_typed.ty().clone())
        }
        Expr::Comma(lhs, rhs) => {
            let lhs_typed = analyze_expr(*lhs, symtab);
            let rhs_typed = analyze_expr(*rhs, symtab);
            TypedExpr::Comma(Box::new(lhs_typed), Box::new(rhs_typed.clone()), rhs_typed.ty().clone())
        }
        // Unary operations
        Expr::Neg(expr) => {
            let typed = analyze_expr(*expr, symtab);
            TypedExpr::Neg(Box::new(typed.clone()), typed.ty().clone())
        }
        Expr::LogicalNot(expr) => {
            let typed = analyze_expr(*expr, symtab);
            TypedExpr::LogicalNot(Box::new(typed), Type::Int)
        }
        Expr::BitwiseNot(expr) => {
            let typed = analyze_expr(*expr, symtab);
            TypedExpr::BitwiseNot(Box::new(typed.clone()), typed.ty().clone())
        }
        Expr::Sizeof(expr) => {
            let _typed = analyze_expr(*expr, symtab);
            TypedExpr::Sizeof(Box::new(_typed), Type::Int) // size_t, but use int
        }
        Expr::Deref(expr) => {
            let typed = analyze_expr(*expr, symtab);
            let result_ty = match typed.ty() {
                Type::Pointer(base_ty) => base_ty.clone(),
                _ => Box::new(Type::Int), // Fallback
            };
            TypedExpr::Deref(Box::new(typed), *result_ty)
        }
        Expr::AddressOf(expr) => {
            let typed = analyze_expr(*expr, symtab);
            TypedExpr::AddressOf(Box::new(typed.clone()), Type::Pointer(Box::new(typed.ty().clone())))
        }
        Expr::SizeofType(ty) => TypedExpr::SizeofType(ty, Type::Int),
        Expr::Ternary(cond, then_expr, else_expr) => {
            let cond_typed = analyze_expr(*cond, symtab);
            let then_typed = analyze_expr(*then_expr, symtab);
            let else_typed = analyze_expr(*else_expr, symtab);
            let result_ty = if then_typed.ty() == else_typed.ty() {
                then_typed.ty().clone()
            } else {
                Type::Int // Fallback
            };
            TypedExpr::Ternary(Box::new(cond_typed), Box::new(then_typed), Box::new(else_typed), result_ty)
        }
        Expr::Member(expr, member) => {
            let typed = analyze_expr(*expr, symtab);
            // For now, assume member access returns int
            TypedExpr::Member(Box::new(typed), member, Type::Int)
        }
        Expr::PointerMember(expr, member) => {
            let typed = analyze_expr(*expr, symtab);
            // For now, assume member access returns int
            TypedExpr::PointerMember(Box::new(typed), member, Type::Int)
        }
        Expr::InitializerList(list) => {
            let typed_list = list
                .into_iter()
                .map(|(designators, initializer)| {
                    let typed_designators = designators.into_iter().map(|d| match d {
                        Designator::Index(expr) => TypedDesignator::Index(Box::new(analyze_expr(*expr, symtab))),
                        Designator::Member(name) => TypedDesignator::Member(name),
                    }).collect();
                    let typed_initializer = convert_initializer_to_typed_analyze(*initializer, symtab);
                    (typed_designators, Box::new(typed_initializer))
                })
                .collect();
            TypedExpr::InitializerList(typed_list, Type::Int) // Fallback
        }
        Expr::ExplicitCast(ty, expr) => {
            let typed_expr = analyze_expr(*expr, symtab);
            // Validate cast if needed
            TypedExpr::ExplicitCast(Box::new(*ty.clone()), Box::new(typed_expr), *ty.clone())
        }
        Expr::ImplicitCast(ty, expr) => {
            let typed_expr = analyze_expr(*expr, symtab);
            TypedExpr::ImplicitCast(Box::new(*ty.clone()), Box::new(typed_expr), *ty.clone())
        }
        Expr::CompoundLiteral(ty, initializer) => {
            let typed_initializer = convert_initializer_to_typed_analyze(*initializer, symtab);
            TypedExpr::CompoundLiteral(Box::new(*ty.clone()), Box::new(typed_initializer), *ty.clone())
        }
        Expr::PreIncrement(expr) => {
            let typed = analyze_expr(*expr, symtab);
            TypedExpr::PreIncrement(Box::new(typed.clone()), typed.ty().clone())
        }
        Expr::PreDecrement(expr) => {
            let typed = analyze_expr(*expr, symtab);
            TypedExpr::PreDecrement(Box::new(typed.clone()), typed.ty().clone())
        }
        Expr::PostIncrement(expr) => {
            let typed = analyze_expr(*expr, symtab);
            TypedExpr::PostIncrement(Box::new(typed.clone()), typed.ty().clone())
        }
        Expr::PostDecrement(expr) => {
            let typed = analyze_expr(*expr, symtab);
            TypedExpr::PostDecrement(Box::new(typed.clone()), typed.ty().clone())
        }
    }
}
