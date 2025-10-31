use crate::common::{SourceLocation, SourceSpan};
use crate::parser::ast::{
    AssignOp, BinOp, Designator, Expr, ForInit, Initializer, Stmt, TranslationUnit, Type,
    TypedDeclarator, TypedDesignator, TypedExpr, TypedForInit, TypedFunctionDecl,
    TypedInitializer, TypedStmt, TypedTranslationUnit,
};
use crate::semantic::error::SemanticError;
use std::collections::HashMap;
mod expressions;
use expressions::TypedExpression;
pub mod error;

/// Represents a symbol in the symbol table.
#[derive(Debug, Clone)]
#[allow(dead_code)]
struct Symbol {
    ty: Type,
    is_function: bool,
    span: SourceSpan,
    is_builtin: bool,
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

use std::collections::HashSet;

/// A semantic analyzer that checks for semantic errors in the AST.
pub struct SemanticAnalyzer {
    symbol_table: SymbolTable,
    pub enum_constants: HashMap<String, i64>,
    struct_definitions: HashMap<String, Type>,
    union_definitions: HashMap<String, Type>,
    current_function: Option<String>,
    labels: HashMap<String, SourceSpan>,
    errors: Vec<(SemanticError, String, SourceSpan)>, // (error, file, span)
    warnings: Vec<(SemanticError, String, SourceSpan)>, // (warning, file, span)
    used_builtins: HashSet<String>,
    used_variables: HashSet<String>,
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
            struct_definitions: HashMap::new(),
            union_definitions: HashMap::new(),
            current_function: None,
            labels: HashMap::new(),
            errors: Vec::new(),
            warnings: Vec::new(),
            used_builtins: HashSet::new(),
            used_variables: HashSet::new(),
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
                    span: SourceSpan::default(),
                    is_builtin: true,
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
    ) -> Result<
        (
            TypedTranslationUnit,
            Vec<(SemanticError, String, SourceSpan)>,
            Self,
        ),
        Vec<(SemanticError, String, SourceSpan)>,
    > {
        // First pass: collect all function definitions and global declarations
        self.collect_symbols(&program, filename);

        // Second pass: check all expressions and statements for semantic errors and build typed AST
        let typed_program = self.check_program(program, filename);

        if self.errors.is_empty() {
            Ok((typed_program, self.warnings.clone(), self))
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
                                span: SourceSpan::default(),
                                is_builtin: false,
                            },
                        );
                    }
                }
                Stmt::Declaration(ty, declarators, _is_static) => {
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
                                        *span,
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
                                    *span,
                                ));
                            } else {
                                self.enum_constants.insert(name.clone(), val);
                            }
                            next_value = val + 1;
                        }
                    } else if let Type::Struct(Some(name), members) = ty {
                        if !members.is_empty() {
                            self.struct_definitions
                                .insert(name.clone(), ty.clone());
                        }
                    } else if let Type::Union(Some(name), members) = ty {
                        if !members.is_empty() {
                            self.union_definitions.insert(name.clone(), ty.clone());
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
                                    declarator.span,
                                ));
                            }
                        } else {
                            self.symbol_table.insert(
                                declarator.name.clone(),
                                Symbol {
                                    ty: declarator.ty.clone(),
                                    is_function: false,
                                    span: declarator.span,
                                    is_builtin: false,
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
                        span: SourceSpan::default(),
                        is_builtin: false,
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

        // Add built-in function declarations to the typed AST
        for name in &self.used_builtins {
            if let Some(symbol) = self.symbol_table.lookup(name) {
                typed_globals.push(TypedStmt::FunctionDeclaration(
                    symbol.ty.clone(),
                    name.clone(),
                    vec![], // Built-ins don't have specified params in this context
                    true,   // Assume built-ins can be variadic
                ));
            }
        }

        // Add built-in function declarations to the typed AST if they are used and not declared.
        let declared_functions: std::collections::HashSet<_> = typed_globals
            .iter()
            .filter_map(|stmt| {
                if let TypedStmt::FunctionDeclaration(_, name, _, _) = stmt {
                    Some(name.clone())
                } else {
                    None
                }
            })
            .collect();

        for name in &self.used_builtins {
            if !declared_functions.contains(name) {
                if let Some(symbol) = self.symbol_table.lookup(name) {
                    typed_globals.push(TypedStmt::FunctionDeclaration(
                        symbol.ty.clone(),
                        name.clone(),
                        vec![],
                        true, // Assume variadic
                    ));
                }
            }
        }

        TypedTranslationUnit {
            globals: typed_globals,
            functions: typed_functions,
        }
    }

    /// Collects all labels defined in a function's statements.
    fn collect_labels(&mut self, stmts: &[Stmt], filename: &str) {
        for stmt in stmts {
            match stmt {
                Stmt::Label(name, body, span) => {
                    if self.labels.contains_key(name) {
                        self.errors.push((
                            SemanticError::VariableRedeclaration(name.clone()),
                            filename.to_string(),
                            *span,
                        ));
                    } else {
                        self.labels.insert(name.clone(), *span);
                    }
                    self.collect_labels(&[*body.clone()], filename);
                }
                Stmt::Block(stmts) => {
                    self.collect_labels(stmts, filename);
                }
                Stmt::If(_, then, otherwise) => {
                    self.collect_labels(&[*then.clone()], filename);
                    if let Some(otherwise) = otherwise {
                        self.collect_labels(&[*otherwise.clone()], filename);
                    }
                }
                Stmt::While(_, body) => {
                    self.collect_labels(&[*body.clone()], filename);
                }
                Stmt::For(_, _, _, body) => {
                    self.collect_labels(&[*body.clone()], filename);
                }
                Stmt::DoWhile(body, _) => {
                    self.collect_labels(&[*body.clone()], filename);
                }
                Stmt::Switch(_, body) => {
                    self.collect_labels(&[*body.clone()], filename);
                }
                Stmt::Case(_, body) => {
                    self.collect_labels(&[*body.clone()], filename);
                }
                Stmt::Default(body) => {
                    self.collect_labels(&[*body.clone()], filename);
                }
                _ => {}
            }
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

        // Clear labels for this function
        self.labels.clear();

        // First pass: collect all labels in the function
        self.collect_labels(&function.body, filename);

        // Check parameters for redeclaration
        let mut param_names = std::collections::HashSet::new();
        for param in &function.params {
            if !param_names.insert(param.name.clone()) {
                self.errors.push((
                    SemanticError::VariableRedeclaration(param.name.clone()),
                    filename.to_string(),
                    param.span,
                ));
            }
            // Add parameters to local symbol table
            self.symbol_table.insert(
                param.name.clone(),
                Symbol {
                    ty: param.ty.clone(),
                    is_function: false,
                    span: param.span,
                    is_builtin: false,
                },
            );
        }

        // Check function body and build typed statements
        let mut typed_body = Vec::new();
        for stmt in function.body {
            typed_body.push(self.check_statement(stmt, filename));
        }

        // Check for unused variables
        for (name, symbol) in self.symbol_table.scopes.last().unwrap() {
            if !self.used_variables.contains(name) {
                self.warnings.push((
                    SemanticError::UnusedVariable(name.clone()),
                    filename.to_string(),
                    symbol.span,
                ));
            }
        }

        // Pop function scope
        self.symbol_table.pop_scope();
        self.current_function = None;
        self.used_variables.clear();

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
            Stmt::Declaration(ty, declarators, is_static) => {
                let mut base_ty = ty.clone();
                match &mut base_ty {
                    Type::Struct(Some(name), members) => {
                        if !members.is_empty() {
                            for member in members.iter_mut() {
                                if let Type::Struct(Some(s_name), s_members) = &member.ty {
                                    if s_members.is_empty() {
                                        if let Some(def) = self.struct_definitions.get(s_name) {
                                            member.ty = def.clone();
                                        }
                                    }
                                } else if let Type::Union(Some(u_name), u_members) = &member.ty {
                                    if u_members.is_empty() {
                                        if let Some(def) = self.union_definitions.get(u_name) {
                                            member.ty = def.clone();
                                        }
                                    }
                                }
                            }
                            self.struct_definitions.insert(name.clone(), base_ty.clone());
                        }
                    }
                    Type::Union(Some(name), members) => {
                        if !members.is_empty() {
                            for member in members.iter_mut() {
                                if let Type::Struct(Some(s_name), s_members) = &member.ty {
                                    if s_members.is_empty() {
                                        if let Some(def) = self.struct_definitions.get(s_name) {
                                            member.ty = def.clone();
                                        }
                                    }
                                } else if let Type::Union(Some(u_name), u_members) = &member.ty {
                                    if u_members.is_empty() {
                                        if let Some(def) = self.union_definitions.get(u_name) {
                                            member.ty = def.clone();
                                        }
                                    }
                                }
                            }
                            self.union_definitions.insert(name.clone(), base_ty.clone());
                        }
                    }
                    _ => {}
                }
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
                                        *span,
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
                                    *span,
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
                            declarator.span,
                        ));
                    }

                    // Insert symbol if not already present
                    if self.symbol_table.lookup(&declarator.name).is_none() {
                        self.symbol_table.insert(
                            declarator.name.clone(),
                            Symbol {
                                ty: declarator.ty.clone(),
                                is_function: false,
                                span: declarator.span,
                                is_builtin: false,
                            },
                        );
                    }

                    // Check initializer expression
                    let typed_initializer = declarator
                        .initializer
                        .map(|init| self.convert_initializer_to_typed(init, filename));

                    if (is_static || self.current_function.is_none())
                        && let Some(ref init) = typed_initializer
                        && !is_const_expr(init)
                    {
                        self.errors.push((
                            SemanticError::InvalidStaticInitializer(declarator.name.clone()),
                            filename.to_string(),
                            SourceSpan::new(
                                crate::file::FileId(0),
                                SourceLocation::new(crate::file::FileId(0), 0, 0),
                                SourceLocation::new(crate::file::FileId(0), 0, 0),
                            ),
                        ));
                    }

                    typed_declarators.push(TypedDeclarator {
                        ty: declarator.ty,
                        name: declarator.name,
                        initializer: typed_initializer,
                    });
                }
                TypedStmt::Declaration(base_ty, typed_declarators, is_static)
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
                                    span: SourceSpan::default(),
                                    is_builtin: false,
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
            Stmt::Label(label, body, _) => {
                let typed_body = Box::new(self.check_statement(*body, filename));
                TypedStmt::Label(label, typed_body)
            }
            Stmt::Goto(label, span) => {
                if !self.labels.contains_key(&label) {
                    self.errors.push((
                        SemanticError::UndefinedLabel(label.clone()),
                        filename.to_string(),
                        span,
                    ));
                }
                TypedStmt::Goto(label)
            }
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
            Stmt::StaticAssert(expr, message) => {
                let typed_expr = self.check_expression(*expr, filename);
                if !is_const_expr(&TypedInitializer::Expr(Box::new(typed_expr.clone()))) {
                    self.errors.push((
                        SemanticError::NotAConstantExpression,
                        filename.to_string(),
                        typed_expr.span(),
                    ));
                } else if let TypedExpr::Number(val, _) = typed_expr {
                    if val == 0 {
                        self.errors.push((
                            SemanticError::StaticAssertFailed(message.clone()),
                            filename.to_string(),
                            typed_expr.span(),
                        ));
                    }
                }
                TypedStmt::StaticAssert(Box::new(typed_expr), message)
            }
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
        let mut lhs_typed = self.check_expression(lhs.clone(), filename);
        if let Type::Array(elem_ty, _) = lhs_typed.ty().clone() {
            lhs_typed = lhs_typed.implicit_cast(Type::Pointer(elem_ty));
        }

        let mut rhs_typed = self.check_expression(rhs.clone(), filename);
        if let Type::Array(elem_ty, _) = rhs_typed.ty().clone() {
            rhs_typed = rhs_typed.implicit_cast(Type::Pointer(elem_ty));
        }

        let lhs_ty = lhs_typed.ty().clone();
        let rhs_ty = rhs_typed.ty().clone();

        let (lhs_final, rhs_final, result_ty) = match op {
            BinOp::Add | BinOp::Sub => {
                if lhs_ty.is_pointer() || rhs_ty.is_pointer() {
                    // Pointer arithmetic
                    let result_ty = match (lhs_ty.unwrap_const(), rhs_ty.unwrap_const()) {
                        (Type::Pointer(_), Type::Pointer(_)) if op == BinOp::Sub => Type::Int,
                        (Type::Pointer(..), ty) if ty.get_integer_rank() > 0 => lhs_ty.clone(),
                        (ty, Type::Pointer(..)) if ty.get_integer_rank() > 0 && op == BinOp::Add => {
                            rhs_ty.clone()
                        }
                        _ => {
                            self.errors.push((
                                SemanticError::TypeMismatch,
                                filename.to_string(),
                                SourceSpan::default(), // Consider improving span info
                            ));
                            Type::Int // dummy type
                        }
                    };
                    (lhs_typed, rhs_typed, result_ty)
                } else {
                    // Standard arithmetic
                    let (lhs_conv_ty, rhs_conv_ty) =
                        self.apply_usual_arithmetic_conversions(&lhs_ty, &rhs_ty);
                    let lhs_cast = lhs_typed.implicit_cast(lhs_conv_ty.clone());
                    let rhs_cast = rhs_typed.implicit_cast(rhs_conv_ty.clone());
                    (lhs_cast, rhs_cast, lhs_conv_ty)
                }
            }
            BinOp::Mul | BinOp::Div | BinOp::Mod => {
                let (lhs_conv_ty, rhs_conv_ty) =
                    self.apply_usual_arithmetic_conversions(&lhs_ty, &rhs_ty);
                let (lhs_cast, rhs_cast) = (
                    lhs_typed.implicit_cast(lhs_conv_ty.clone()),
                    rhs_typed.implicit_cast(rhs_conv_ty.clone()),
                );
                (lhs_cast, rhs_cast, lhs_conv_ty)
            }
            BinOp::Equal | BinOp::NotEqual | BinOp::LessThan | BinOp::GreaterThan
            | BinOp::LessThanOrEqual | BinOp::GreaterThanOrEqual => {
                (lhs_typed, rhs_typed, Type::Bool)
            }
            BinOp::LogicalAnd | BinOp::LogicalOr => (lhs_typed, rhs_typed, Type::Bool),
            BinOp::BitwiseOr | BinOp::BitwiseXor | BinOp::BitwiseAnd => {
                (lhs_typed, rhs_typed, Type::Int)
            }
            BinOp::LeftShift | BinOp::RightShift => (lhs_typed, rhs_typed, lhs_ty.clone()),
            BinOp::Comma => (lhs_typed, rhs_typed, rhs_ty.clone()),
        };

        TypedExpression::new(op, lhs_final, rhs_final, result_ty).into()
    }

    fn check_assignment_expression(
        &mut self,
        op: AssignOp,
        lhs: &Expr,
        rhs: &Expr,
        filename: &str,
    ) -> TypedExpr {
        let lhs_typed = self.check_expression(lhs.clone(), filename);
        let rhs_typed = self.check_expression(rhs.clone(), filename);

        if !is_lvalue(&lhs_typed) {
            self.errors.push((
                SemanticError::NotAnLvalue,
                filename.to_string(),
                lhs_typed.span(),
            ));
        }

        if let Type::Const(_) = &lhs_typed.ty() {
            self.errors.push((
                SemanticError::AssignmentToConst,
                filename.to_string(),
                lhs_typed.span(),
            ));
        }

        let rhs_cast = rhs_typed.implicit_cast(lhs_typed.ty().clone());
        let result_ty = lhs_typed.ty().clone();

        match op {
            AssignOp::Assign => TypedExpr::Assign(Box::new(lhs_typed), Box::new(rhs_cast), result_ty),
            AssignOp::Add => {
                TypedExpr::AssignAdd(Box::new(lhs_typed), Box::new(rhs_cast), result_ty)
            }
            AssignOp::Sub => {
                TypedExpr::AssignSub(Box::new(lhs_typed), Box::new(rhs_cast), result_ty)
            }
            AssignOp::Mul => {
                TypedExpr::AssignMul(Box::new(lhs_typed), Box::new(rhs_cast), result_ty)
            }
            AssignOp::Div => {
                TypedExpr::AssignDiv(Box::new(lhs_typed), Box::new(rhs_cast), result_ty)
            }
            AssignOp::Mod => {
                TypedExpr::AssignMod(Box::new(lhs_typed), Box::new(rhs_cast), result_ty)
            }
            AssignOp::LeftShift => {
                TypedExpr::AssignLeftShift(Box::new(lhs_typed), Box::new(rhs_cast), result_ty)
            }
            AssignOp::RightShift => {
                TypedExpr::AssignRightShift(Box::new(lhs_typed), Box::new(rhs_cast), result_ty)
            }
            AssignOp::BitwiseAnd => {
                TypedExpr::AssignBitwiseAnd(Box::new(lhs_typed), Box::new(rhs_cast), result_ty)
            }
            AssignOp::BitwiseXor => {
                TypedExpr::AssignBitwiseXor(Box::new(lhs_typed), Box::new(rhs_cast), result_ty)
            }
            AssignOp::BitwiseOr => {
                TypedExpr::AssignBitwiseOr(Box::new(lhs_typed), Box::new(rhs_cast), result_ty)
            }
        }
    }

    /// Checks an expression for semantic errors and returns a typed expression.
    fn check_expression(&mut self, expr: Expr, filename: &str) -> TypedExpr {
        if let Some((op, lhs, rhs)) = expr.get_binary_expr() {
            return self.check_binary_expression(op, lhs, rhs, filename);
        } else if let Some((op, lhs, rhs)) = expr.get_assign_expr() {
            return self.check_assignment_expression(op, lhs, rhs, filename);
        }

        match expr {
            Expr::Variable(name, location) => {
                self.used_variables.insert(name.clone());
                if !self.symbol_table.contains_key(&name)
                    && !self.enum_constants.contains_key(&name)
                {
                    self.errors.push((
                        SemanticError::UndefinedVariable(name.clone()),
                        filename.to_string(),
                        location,
                    ));
                }
                let ty = self
                    .symbol_table
                    .lookup(&name)
                    .map(|s| s.ty.clone())
                    .unwrap_or(Type::Int);

                let ty = match ty {
                    Type::Struct(Some(s_name), members) if members.is_empty() => {
                        self.struct_definitions.get(&s_name).cloned().unwrap_or(Type::Struct(Some(s_name), vec![]))
                    }
                    Type::Union(Some(u_name), members) if members.is_empty() => {
                        self.union_definitions.get(&u_name).cloned().unwrap_or(Type::Union(Some(u_name), vec![]))
                    }
                    _ => ty,
                };

                let promoted_ty = self.integer_promote(&ty);
                TypedExpr::Variable(name, location, promoted_ty)
            }
            Expr::Number(n) => TypedExpr::Number(n, Type::Int),
            Expr::FloatNumber(n) => TypedExpr::FloatNumber(n, Type::Double),
            Expr::String(s) => TypedExpr::String(s, Type::Pointer(Box::new(Type::Char))),
            Expr::Char(c) => TypedExpr::Char(c, Type::Char),
            Expr::Call(name, args, location) => {
                if let Some(symbol) = self.symbol_table.lookup(&name) {
                    if symbol.is_builtin {
                        self.used_builtins.insert(name.clone());
                    }
                } else {
                    self.errors.push((
                        SemanticError::UndefinedFunction(name.clone()),
                        filename.to_string(),
                        location,
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
                TypedExpr::LogicalNot(Box::new(typed), Type::Bool)
            }
            Expr::BitwiseNot(expr) => {
                let typed = self.check_expression(*expr, filename);
                TypedExpr::BitwiseNot(Box::new(typed.clone()), typed.ty().clone())
            }
            Expr::Sizeof(expr) => {
                let _typed = self.check_expression(*expr, filename);
                TypedExpr::Sizeof(Box::new(_typed), Type::Int)
            }
            Expr::Alignof(expr) => {
                let _typed = self.check_expression(*expr, filename);
                TypedExpr::Alignof(Box::new(_typed), Type::Int)
            }
            Expr::Deref(expr) => {
                let typed = self.check_expression(*expr, filename);
                let result_ty = match typed.ty().unwrap_const().clone() {
                    Type::Pointer(base_ty) => *base_ty,
                    Type::Array(elem_ty, _) => *elem_ty,
                    other_ty => {
                        self.errors.push((
                            SemanticError::NotAPointer(other_ty),
                            filename.to_string(),
                            typed.span(),
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
            Expr::AlignofType(ty) => TypedExpr::AlignofType(ty, Type::Int),
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
                let members = match typed.ty().clone() {
                    Type::Struct(Some(name), members) if members.is_empty() => {
                        if let Some(Type::Struct(_, def)) = self.struct_definitions.get(&name) {
                            Some(def.clone())
                        } else {
                            None
                        }
                    }
                    Type::Union(Some(name), members) if members.is_empty() => {
                        if let Some(Type::Union(_, def)) = self.union_definitions.get(&name) {
                            Some(def.clone())
                        } else {
                            None
                        }
                    }
                    Type::Struct(_, members) => Some(members),
                    Type::Union(_, members) => Some(members),
                    other => {
                        self.errors.push((
                            SemanticError::NotAStructOrUnion(other),
                            filename.to_string(),
                            typed.span(),
                        ));
                        None
                    }
                };

                let member_ty = members
                    .and_then(|m| {
                        m.iter()
                            .find(|p| p.name == member)
                            .map(|p| p.ty.clone())
                    })
                    .unwrap_or_else(|| {
                        self.errors.push((
                            SemanticError::UndefinedMember(member.clone()),
                            filename.to_string(),
                            typed.span(),
                        ));
                        Type::Int
                    });
                TypedExpr::Member(Box::new(typed), member, member_ty)
            }
            Expr::PointerMember(expr, member) => {
                let typed = self.check_expression(*expr, filename);
                let members = match typed.ty().clone() {
                    Type::Pointer(inner) => match *inner {
                        Type::Struct(Some(name), members) if members.is_empty() => {
                           if let Some(Type::Struct(_, def)) = self.struct_definitions.get(&name) {
                                Some(def.clone())
                           } else {
                                 None
                           }
                        }
                        Type::Union(Some(name), members) if members.is_empty() => {
                            if let Some(Type::Union(_, def)) = self.union_definitions.get(&name) {
                                Some(def.clone())
                            } else {
                                None
                            }
                        }
                        Type::Struct(_, members) => Some(members),
                        Type::Union(_, members) => Some(members),
                        other => {
                            self.errors.push((
                                SemanticError::NotAStructOrUnion(other),
                                filename.to_string(),
                                typed.span(),
                            ));
                            None
                        }
                    },
                    other => {
                        self.errors.push((
                            SemanticError::NotAPointer(other),
                            filename.to_string(),
                            typed.span(),
                        ));
                        None
                    }
                };

                let member_ty = members
                    .and_then(|m| {
                        m.iter()
                            .find(|p| p.name == member)
                            .map(|p| p.ty.clone())
                    })
                    .unwrap_or_else(|| {
                        self.errors.push((
                            SemanticError::UndefinedMember(member.clone()),
                            filename.to_string(),
                            typed.span(),
                        ));
                        Type::Int
                    });
                TypedExpr::PointerMember(Box::new(typed), member, member_ty)
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

fn is_const_expr(initializer: &TypedInitializer) -> bool {
    match initializer {
        TypedInitializer::Expr(expr) => match **expr {
            TypedExpr::Number(_, _) => true,
            _ => false,
        },
        TypedInitializer::List(list) => list
            .iter()
            .all(|(_, initializer)| is_const_expr(initializer)),
    }
}

fn is_lvalue(expr: &TypedExpr) -> bool {
    matches!(
        expr,
        TypedExpr::Variable(_, _, _)
            | TypedExpr::Deref(_, _)
            | TypedExpr::Member(_, _, _)
            | TypedExpr::PointerMember(_, _, _)
    )
}
