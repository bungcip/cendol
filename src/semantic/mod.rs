use crate::common::{SourceLocation, SourceSpan};
use crate::parser::ast::{
    BinOp, Designator, Expr, ForInit, Initializer, TranslationUnit, Stmt, Type, TypedDeclarator,
    TypedDesignator, TypedExpr, TypedForInit, TypedFunctionDecl, TypedInitializer, TypedStmt,
    TypedTranslationUnit,
};
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
        program: TranslationUnit,
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
    fn collect_symbols(&mut self, program: &TranslationUnit, filename: &str) {
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
                    if let Type::Enum(_name, members) = ty
                        && !members.is_empty()
                    {
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
    fn check_program(&mut self, program: TranslationUnit, filename: &str) -> TypedTranslationUnit {
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
    fn check_function(
        &mut self,
        function: crate::parser::ast::Function,
        filename: &str,
    ) -> TypedFunctionDecl {
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
                    if self.current_function.is_some()
                        && let Some(existing) = self.symbol_table.lookup(&declarator.name)
                        && !existing.is_function
                    {
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
                    let typed_initializer = declarator
                        .initializer
                        .map(|init| self.convert_initializer_to_typed(init, filename));

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
                let typed_otherwise =
                    otherwise.map(|o| Box::new(self.check_statement(*o, filename)));
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
                        let typed_initializer = initializer
                            .map(|init| self.convert_initializer_to_typed(init, filename));
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

                TypedStmt::For(
                    Box::new(typed_init),
                    Box::new(typed_cond),
                    Box::new(typed_inc),
                    typed_body,
                )
            }
            Stmt::Block(stmts) => {
                self.symbol_table.push_scope();
                let typed_stmts = stmts
                    .into_iter()
                    .map(|s| self.check_statement(s, filename))
                    .collect();
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

    /// Checks a binary expression for semantic errors and returns a typed expression.
    fn check_binary_expression(
        &mut self,
        op: BinOp,
        lhs: &Expr,
        rhs: &Expr,
        filename: &str,
    ) -> TypedExpr {
        let lhs_typed = self.check_expression(lhs.clone(), filename);
        let rhs_typed = self.check_expression(rhs.clone(), filename);

        match op {
            BinOp::Assign => {
                if lhs_typed.ty() != rhs_typed.ty() {
                    let is_lhs_numeric = matches!(
                        lhs_typed.ty(),
                        Type::Int
                            | Type::Char
                            | Type::Short
                            | Type::Long
                            | Type::LongLong
                            | Type::Enum(_, _)
                    );
                    let is_rhs_numeric = matches!(
                        rhs_typed.ty(),
                        Type::Int
                            | Type::Char
                            | Type::Short
                            | Type::Long
                            | Type::LongLong
                            | Type::Enum(_, _)
                    );

                    if !is_lhs_numeric || !is_rhs_numeric {
                        self.errors.push((
                            SemanticError::TypeMismatch,
                            filename.to_string(),
                            SourceSpan::new(
                                crate::file::FileId(0),
                                SourceLocation::new(crate::file::FileId(0), 0, 0),
                                SourceLocation::new(crate::file::FileId(0), 0, 0),
                            ),
                        ));
                    }
                }

                let cast_rhs = if lhs_typed.ty() == rhs_typed.ty() {
                    rhs_typed
                } else {
                    TypedExpr::ImplicitCast(
                        Box::new(lhs_typed.ty().clone()),
                        Box::new(rhs_typed),
                        lhs_typed.ty().clone(),
                    )
                };
                TypedExpr::Assign(
                    Box::new(lhs_typed.clone()),
                    Box::new(cast_rhs),
                    lhs_typed.ty().clone(),
                )
            }
            BinOp::AssignAdd => {
                let (_lhs_conv_ty, rhs_conv_ty) =
                    self.apply_usual_arithmetic_conversions(lhs_typed.ty(), rhs_typed.ty());
                let rhs_cast = if *rhs_typed.ty() != rhs_conv_ty {
                    TypedExpr::ImplicitCast(
                        Box::new(rhs_conv_ty.clone()),
                        Box::new(rhs_typed),
                        rhs_conv_ty.clone(),
                    )
                } else {
                    rhs_typed
                };
                TypedExpr::AssignAdd(
                    Box::new(lhs_typed.clone()),
                    Box::new(rhs_cast),
                    lhs_typed.ty().clone(),
                )
            }
            BinOp::AssignSub => {
                let (_lhs_conv_ty, rhs_conv_ty) =
                    self.apply_usual_arithmetic_conversions(lhs_typed.ty(), rhs_typed.ty());
                let rhs_cast = if *rhs_typed.ty() != rhs_conv_ty {
                    TypedExpr::ImplicitCast(
                        Box::new(rhs_conv_ty.clone()),
                        Box::new(rhs_typed),
                        rhs_conv_ty.clone(),
                    )
                } else {
                    rhs_typed
                };
                TypedExpr::AssignSub(
                    Box::new(lhs_typed.clone()),
                    Box::new(rhs_cast),
                    lhs_typed.ty().clone(),
                )
            }
            BinOp::AssignMul => {
                let (_lhs_conv_ty, rhs_conv_ty) =
                    self.apply_usual_arithmetic_conversions(lhs_typed.ty(), rhs_typed.ty());
                let rhs_cast = if *rhs_typed.ty() != rhs_conv_ty {
                    TypedExpr::ImplicitCast(
                        Box::new(rhs_conv_ty.clone()),
                        Box::new(rhs_typed),
                        rhs_conv_ty.clone(),
                    )
                } else {
                    rhs_typed
                };
                TypedExpr::AssignMul(
                    Box::new(lhs_typed.clone()),
                    Box::new(rhs_cast),
                    lhs_typed.ty().clone(),
                )
            }
            BinOp::AssignDiv => {
                let (_lhs_conv_ty, rhs_conv_ty) =
                    self.apply_usual_arithmetic_conversions(lhs_typed.ty(), rhs_typed.ty());
                let rhs_cast = if *rhs_typed.ty() != rhs_conv_ty {
                    TypedExpr::ImplicitCast(
                        Box::new(rhs_conv_ty.clone()),
                        Box::new(rhs_typed),
                        rhs_conv_ty.clone(),
                    )
                } else {
                    rhs_typed
                };
                TypedExpr::AssignDiv(
                    Box::new(lhs_typed.clone()),
                    Box::new(rhs_cast),
                    lhs_typed.ty().clone(),
                )
            }
            BinOp::AssignMod => {
                let (_lhs_conv_ty, rhs_conv_ty) =
                    self.apply_usual_arithmetic_conversions(lhs_typed.ty(), rhs_typed.ty());
                let rhs_cast = if *rhs_typed.ty() != rhs_conv_ty {
                    TypedExpr::ImplicitCast(
                        Box::new(rhs_conv_ty.clone()),
                        Box::new(rhs_typed),
                        rhs_conv_ty.clone(),
                    )
                } else {
                    rhs_typed
                };
                TypedExpr::AssignMod(
                    Box::new(lhs_typed.clone()),
                    Box::new(rhs_cast),
                    lhs_typed.ty().clone(),
                )
            }
            BinOp::AssignLeftShift => TypedExpr::AssignLeftShift(
                Box::new(lhs_typed.clone()),
                Box::new(rhs_typed),
                lhs_typed.ty().clone(),
            ),
            BinOp::AssignRightShift => TypedExpr::AssignRightShift(
                Box::new(lhs_typed.clone()),
                Box::new(rhs_typed),
                lhs_typed.ty().clone(),
            ),
            BinOp::AssignBitwiseAnd => TypedExpr::AssignBitwiseAnd(
                Box::new(lhs_typed.clone()),
                Box::new(rhs_typed),
                lhs_typed.ty().clone(),
            ),
            BinOp::AssignBitwiseXor => TypedExpr::AssignBitwiseXor(
                Box::new(lhs_typed.clone()),
                Box::new(rhs_typed),
                lhs_typed.ty().clone(),
            ),
            BinOp::AssignBitwiseOr => TypedExpr::AssignBitwiseOr(
                Box::new(lhs_typed.clone()),
                Box::new(rhs_typed),
                lhs_typed.ty().clone(),
            ),
            BinOp::Add => {
                let (lhs_conv_ty, rhs_conv_ty) =
                    self.apply_usual_arithmetic_conversions(lhs_typed.ty(), rhs_typed.ty());
                let lhs_cast = if *lhs_typed.ty() != lhs_conv_ty {
                    TypedExpr::ImplicitCast(
                        Box::new(lhs_conv_ty.clone()),
                        Box::new(lhs_typed),
                        lhs_conv_ty.clone(),
                    )
                } else {
                    lhs_typed
                };
                let rhs_cast = if *rhs_typed.ty() != rhs_conv_ty {
                    TypedExpr::ImplicitCast(
                        Box::new(rhs_conv_ty.clone()),
                        Box::new(rhs_typed),
                        rhs_conv_ty.clone(),
                    )
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
            BinOp::Sub => {
                let (lhs_conv_ty, rhs_conv_ty) =
                    self.apply_usual_arithmetic_conversions(lhs_typed.ty(), rhs_typed.ty());
                let lhs_cast = if *lhs_typed.ty() != lhs_conv_ty {
                    TypedExpr::ImplicitCast(
                        Box::new(lhs_conv_ty.clone()),
                        Box::new(lhs_typed),
                        lhs_conv_ty.clone(),
                    )
                } else {
                    lhs_typed
                };
                let rhs_cast = if *rhs_typed.ty() != rhs_conv_ty {
                    TypedExpr::ImplicitCast(
                        Box::new(rhs_conv_ty.clone()),
                        Box::new(rhs_typed),
                        rhs_conv_ty.clone(),
                    )
                } else {
                    rhs_typed
                };
                let result_ty = match (&lhs_conv_ty, &rhs_conv_ty) {
                    (Type::Pointer(_), Type::Int) => lhs_conv_ty.clone(),
                    (Type::Pointer(_), Type::Pointer(_)) => Type::Int,
                    _ => lhs_conv_ty.clone(),
                };
                TypedExpr::Sub(Box::new(lhs_cast), Box::new(rhs_cast), result_ty)
            }
            BinOp::Mul => {
                let (lhs_conv_ty, rhs_conv_ty) =
                    self.apply_usual_arithmetic_conversions(lhs_typed.ty(), rhs_typed.ty());
                let lhs_cast = if *lhs_typed.ty() != lhs_conv_ty {
                    TypedExpr::ImplicitCast(
                        Box::new(lhs_conv_ty.clone()),
                        Box::new(lhs_typed),
                        lhs_conv_ty.clone(),
                    )
                } else {
                    lhs_typed
                };
                let rhs_cast = if *rhs_typed.ty() != rhs_conv_ty {
                    TypedExpr::ImplicitCast(
                        Box::new(rhs_conv_ty.clone()),
                        Box::new(rhs_typed),
                        rhs_conv_ty.clone(),
                    )
                } else {
                    rhs_typed
                };
                TypedExpr::Mul(Box::new(lhs_cast), Box::new(rhs_cast), lhs_conv_ty.clone())
            }
            BinOp::Div => {
                let (lhs_conv_ty, rhs_conv_ty) =
                    self.apply_usual_arithmetic_conversions(lhs_typed.ty(), rhs_typed.ty());
                let lhs_cast = if *lhs_typed.ty() != lhs_conv_ty {
                    TypedExpr::ImplicitCast(
                        Box::new(lhs_conv_ty.clone()),
                        Box::new(lhs_typed),
                        lhs_conv_ty.clone(),
                    )
                } else {
                    lhs_typed
                };
                let rhs_cast = if *rhs_typed.ty() != rhs_conv_ty {
                    TypedExpr::ImplicitCast(
                        Box::new(rhs_conv_ty.clone()),
                        Box::new(rhs_typed),
                        rhs_conv_ty.clone(),
                    )
                } else {
                    rhs_typed
                };
                TypedExpr::Div(Box::new(lhs_cast), Box::new(rhs_cast), lhs_conv_ty.clone())
            }
            BinOp::Mod => {
                let (lhs_conv_ty, rhs_conv_ty) =
                    self.apply_usual_arithmetic_conversions(lhs_typed.ty(), rhs_typed.ty());
                let lhs_cast = if *lhs_typed.ty() != lhs_conv_ty {
                    TypedExpr::ImplicitCast(
                        Box::new(lhs_conv_ty.clone()),
                        Box::new(lhs_typed),
                        lhs_conv_ty.clone(),
                    )
                } else {
                    lhs_typed
                };
                let rhs_cast = if *rhs_typed.ty() != rhs_conv_ty {
                    TypedExpr::ImplicitCast(
                        Box::new(rhs_conv_ty.clone()),
                        Box::new(rhs_typed),
                        rhs_conv_ty.clone(),
                    )
                } else {
                    rhs_typed
                };
                TypedExpr::Mod(Box::new(lhs_cast), Box::new(rhs_cast), lhs_conv_ty.clone())
            }
            BinOp::Equal => TypedExpr::Equal(Box::new(lhs_typed), Box::new(rhs_typed), Type::Int),
            BinOp::NotEqual => {
                TypedExpr::NotEqual(Box::new(lhs_typed), Box::new(rhs_typed), Type::Int)
            }
            BinOp::LessThan => {
                TypedExpr::LessThan(Box::new(lhs_typed), Box::new(rhs_typed), Type::Int)
            }
            BinOp::GreaterThan => {
                TypedExpr::GreaterThan(Box::new(lhs_typed), Box::new(rhs_typed), Type::Int)
            }
            BinOp::LessThanOrEqual => {
                TypedExpr::LessThanOrEqual(Box::new(lhs_typed), Box::new(rhs_typed), Type::Int)
            }
            BinOp::GreaterThanOrEqual => {
                TypedExpr::GreaterThanOrEqual(Box::new(lhs_typed), Box::new(rhs_typed), Type::Int)
            }
            BinOp::LogicalAnd => {
                TypedExpr::LogicalAnd(Box::new(lhs_typed), Box::new(rhs_typed), Type::Int)
            }
            BinOp::LogicalOr => {
                TypedExpr::LogicalOr(Box::new(lhs_typed), Box::new(rhs_typed), Type::Int)
            }
            BinOp::BitwiseOr => {
                TypedExpr::BitwiseOr(Box::new(lhs_typed), Box::new(rhs_typed), Type::Int)
            }
            BinOp::BitwiseXor => {
                TypedExpr::BitwiseXor(Box::new(lhs_typed), Box::new(rhs_typed), Type::Int)
            }
            BinOp::BitwiseAnd => {
                TypedExpr::BitwiseAnd(Box::new(lhs_typed), Box::new(rhs_typed), Type::Int)
            }
            BinOp::LeftShift => TypedExpr::LeftShift(
                Box::new(lhs_typed.clone()),
                Box::new(rhs_typed),
                lhs_typed.ty().clone(),
            ),
            BinOp::RightShift => TypedExpr::RightShift(
                Box::new(lhs_typed.clone()),
                Box::new(rhs_typed),
                lhs_typed.ty().clone(),
            ),
            BinOp::Comma => TypedExpr::Comma(
                Box::new(lhs_typed),
                Box::new(rhs_typed.clone()),
                rhs_typed.ty().clone(),
            ),
        }
    }

    /// Checks an expression for semantic errors and returns a typed expression.
    fn check_expression(&mut self, expr: Expr, filename: &str) -> TypedExpr {
        if let Some((op, lhs, rhs)) = expr.get_binary_expr() {
            return self.check_binary_expression(op, lhs, rhs, filename);
        }

        match expr {
            Expr::Variable(name, location) => {
                if !self.symbol_table.contains_key(&name)
                    && !self.enum_constants.contains_key(&name)
                {
                    self.errors.push((
                        SemanticError::UndefinedVariable(name.clone()),
                        filename.to_string(),
                        location.clone(),
                    ));
                }
                let ty = self
                    .symbol_table
                    .lookup(&name)
                    .map(|s| s.ty.clone())
                    .unwrap_or(Type::Int);
                let promoted_ty = self.integer_promote(&ty);
                TypedExpr::Variable(name, location, promoted_ty)
            }
            Expr::Number(n) => TypedExpr::Number(n, Type::Int),
            Expr::String(s) => TypedExpr::String(s, Type::Pointer(Box::new(Type::Char))),
            Expr::Char(c) => TypedExpr::Char(c, Type::Char),
            Expr::Call(name, args, location) => {
                if !self.symbol_table.contains_key(&name) {
                    self.errors.push((
                        SemanticError::UndefinedFunction(name.clone()),
                        filename.to_string(),
                        location.clone(),
                    ));
                }
                let return_ty = self
                    .symbol_table
                    .lookup(&name)
                    .map(|s| s.ty.clone())
                    .unwrap_or(Type::Int);
                let typed_args = args
                    .into_iter()
                    .map(|arg| self.check_expression(arg, filename))
                    .collect::<Vec<_>>();
                TypedExpr::Call(name, typed_args, location, return_ty)
            }
            Expr::Neg(expr) => {
                let typed = self.check_expression(*expr, filename);
                TypedExpr::Neg(Box::new(typed.clone()), typed.ty().clone())
            }
            Expr::LogicalNot(expr) => {
                let typed = self.check_expression(*expr, filename);
                TypedExpr::LogicalNot(Box::new(typed), Type::Int)
            }
            Expr::BitwiseNot(expr) => {
                let typed = self.check_expression(*expr, filename);
                TypedExpr::BitwiseNot(Box::new(typed.clone()), typed.ty().clone())
            }
            Expr::Sizeof(expr) => {
                let _typed = self.check_expression(*expr, filename);
                TypedExpr::Sizeof(Box::new(_typed), Type::Int)
            }
            Expr::Deref(expr) => {
                let typed = self.check_expression(*expr, filename);
                let result_ty = match typed.ty().clone() {
                    Type::Pointer(base_ty) => *base_ty,
                    Type::Array(elem_ty, _) => *elem_ty,
                    other_ty => {
                        self.errors.push((
                            SemanticError::NotAPointer(other_ty),
                            filename.to_string(),
                            SourceSpan::new(
                                crate::file::FileId(0),
                                SourceLocation::new(crate::file::FileId(0), 0, 0),
                                SourceLocation::new(crate::file::FileId(0), 0, 0),
                            ),
                        ));
                        Type::Int
                    }
                };
                TypedExpr::Deref(Box::new(typed), result_ty)
            }
            Expr::AddressOf(expr) => {
                let typed = self.check_expression(*expr, filename);
                TypedExpr::AddressOf(
                    Box::new(typed.clone()),
                    Type::Pointer(Box::new(typed.ty().clone())),
                )
            }
            Expr::SizeofType(ty) => TypedExpr::SizeofType(ty, Type::Int),
            Expr::Ternary(cond, then_expr, else_expr) => {
                let cond_typed = self.check_expression(*cond, filename);
                let then_typed = self.check_expression(*then_expr, filename);
                let else_typed = self.check_expression(*else_expr, filename);
                let result_ty = if then_typed.ty() == else_typed.ty() {
                    then_typed.ty().clone()
                } else {
                    Type::Int
                };
                TypedExpr::Ternary(
                    Box::new(cond_typed),
                    Box::new(then_typed),
                    Box::new(else_typed),
                    result_ty,
                )
            }
            Expr::Member(expr, member) => {
                let typed = self.check_expression(*expr, filename);
                TypedExpr::Member(Box::new(typed), member, Type::Int)
            }
            Expr::PointerMember(expr, member) => {
                let typed = self.check_expression(*expr, filename);
                TypedExpr::PointerMember(Box::new(typed), member, Type::Int)
            }
            Expr::InitializerList(list) => {
                let typed_list = list
                    .into_iter()
                    .map(|(designators, initializer)| {
                        let typed_designators = designators
                            .into_iter()
                            .map(|d| match d {
                                Designator::Index(expr) => TypedDesignator::Index(Box::new(
                                    self.check_expression(*expr, filename),
                                )),
                                Designator::Member(name) => TypedDesignator::Member(name),
                            })
                            .collect();
                        let typed_initializer =
                            self.convert_initializer_to_typed(*initializer, filename);
                        (typed_designators, Box::new(typed_initializer))
                    })
                    .collect();
                TypedExpr::InitializerList(typed_list, Type::Int)
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
                TypedExpr::CompoundLiteral(
                    Box::new(*ty.clone()),
                    Box::new(typed_initializer),
                    *ty.clone(),
                )
            }
            Expr::PreIncrement(expr) => {
                let typed = self.check_expression(*expr, filename);
                TypedExpr::PreIncrement(Box::new(typed.clone()), typed.ty().clone())
            }
            Expr::PreDecrement(expr) => {
                let typed = self.check_expression(*expr, filename);
                TypedExpr::PreDecrement(Box::new(typed.clone()), typed.ty().clone())
            }
            Expr::PostIncrement(expr) => {
                let typed = self.check_expression(*expr, filename);
                TypedExpr::PostIncrement(Box::new(typed.clone()), typed.ty().clone())
            }
            Expr::PostDecrement(expr) => {
                let typed = self.check_expression(*expr, filename);
                TypedExpr::PostDecrement(Box::new(typed.clone()), typed.ty().clone())
            }
            _ => todo!("This expression is not supported yet"),
        }
    }

    fn convert_initializer_to_typed(
        &mut self,
        initializer: Initializer,
        filename: &str,
    ) -> TypedInitializer {
        match initializer {
            Initializer::Expr(expr) => {
                let typed_expr = self.check_expression(*expr, filename);
                TypedInitializer::Expr(Box::new(typed_expr))
            }
            Initializer::List(list) => {
                let typed_list = list
                    .into_iter()
                    .map(|(designators, initializer)| {
                        let typed_designators = designators
                            .into_iter()
                            .map(|d| match d {
                                Designator::Index(expr) => TypedDesignator::Index(Box::new(
                                    self.check_expression(*expr, filename),
                                )),
                                Designator::Member(name) => TypedDesignator::Member(name),
                            })
                            .collect();
                        let typed_initializer =
                            self.convert_initializer_to_typed(*initializer, filename);
                        (typed_designators, Box::new(typed_initializer))
                    })
                    .collect();
                TypedInitializer::List(typed_list)
            }
        }
    }

    /// Performs integer promotions on a type.
    fn integer_promote(&self, ty: &Type) -> Type {
        match ty {
            Type::Bool | Type::Char | Type::UnsignedChar | Type::Short | Type::UnsignedShort => {
                Type::Int
            }
            _ => ty.clone(),
        }
    }

    /// Applies usual arithmetic conversions to two types.
    fn apply_usual_arithmetic_conversions(&self, lhs_ty: &Type, rhs_ty: &Type) -> (Type, Type) {
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
}
