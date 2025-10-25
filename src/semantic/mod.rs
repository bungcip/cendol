use crate::common::{SourceLocation, SourceSpan};
use crate::parser::ast::{Expr, Program, Stmt, Type};
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

/// A semantic analyzer that checks for semantic errors in the AST.
pub struct SemanticAnalyzer {
    symbol_table: HashMap<String, Symbol>,
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
        let mut analyzer = SemanticAnalyzer {
            symbol_table: HashMap::new(),
            current_function: None,
            errors: Vec::new(),
        };

        // Add built-in functions
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
            ("strlen", Type::Int),
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

    /// Analyzes a program for semantic errors.
    ///
    /// # Arguments
    ///
    /// * `program` - The program AST to analyze.
    /// * `filename` - The source filename for error reporting.
    ///
    /// # Returns
    ///
    /// A `Result` which is `Ok` if no semantic errors were found, or `Err` with a vector of errors.
    pub fn analyze(
        mut self,
        program: Program,
        filename: &str,
    ) -> Result<(), Vec<(SemanticError, String, SourceSpan)>> {
        // First pass: collect all function definitions and global declarations
        self.collect_symbols(&program, filename);

        // Second pass: check all expressions and statements for semantic errors
        self.check_program(program, filename);

        if self.errors.is_empty() {
            Ok(())
        } else {
            Err(self.errors)
        }
    }

    /// First pass: collect all symbols (functions and global variables).
    fn collect_symbols(&mut self, program: &Program, filename: &str) {
        for global in &program.globals {
            match global {
                Stmt::FunctionDeclaration(ty, name, _params, _) => {
                    if let Some(existing) = self.symbol_table.get(name) {
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
                Stmt::Declaration(_, declarators) => {
                    for declarator in declarators {
                        if let Some(existing) = self.symbol_table.get(&declarator.name) {
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
            if let Some(existing) = self.symbol_table.get(&function.name) {
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

    /// Second pass: check all statements and expressions for semantic correctness.
    fn check_program(&mut self, program: Program, filename: &str) {
        for function in program.functions {
            self.current_function = Some(function.name.clone());
            self.check_function(function, filename);
        }
    }

    /// Checks a function for semantic errors.
    fn check_function(&mut self, function: crate::parser::ast::Function, filename: &str) {
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

        // Check function body
        for stmt in function.body {
            self.check_statement(stmt, filename);
        }

        // Remove local symbols (parameters) after checking function
        for param in &function.params {
            self.symbol_table.remove(&param.name);
        }
        self.current_function = None;
    }

    /// Checks a statement for semantic errors.
    fn check_statement(&mut self, stmt: Stmt, filename: &str) {
        match stmt {
            Stmt::Declaration(_, declarators) => {
                for declarator in declarators {
                    // Check for redeclaration in local scope
                    if let Some(existing) = self.symbol_table.get(&declarator.name) {
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
                    } else {
                        self.symbol_table.insert(
                            declarator.name.clone(),
                            Symbol {
                                ty: declarator.ty,
                                is_function: false,
                                defined_at: filename.to_string(),
                            },
                        );
                    }

                    // Check initializer expression
                    if let Some(init_expr) = declarator.initializer {
                        self.check_expression(*init_expr, filename);
                    }
                }
            }
            Stmt::Expr(expr) => {
                self.check_expression(expr, filename);
            }
            Stmt::Return(expr) => {
                self.check_expression(expr, filename);
            }
            Stmt::If(cond, then, otherwise) => {
                self.check_expression(*cond, filename);
                self.check_statement(*then, filename);
                if let Some(otherwise) = otherwise {
                    self.check_statement(*otherwise, filename);
                }
            }
            Stmt::While(cond, body) => {
                self.check_expression(*cond, filename);
                self.check_statement(*body, filename);
            }
            Stmt::For(init, cond, inc, body) => {
                if let Some(init) = init {
                    match init {
                        crate::parser::ast::ForInit::Declaration(ty, name, initializer) => {
                            if let Some(existing) = self.symbol_table.get(&name) {
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
                                        ty,
                                        is_function: false,
                                        defined_at: filename.to_string(),
                                    },
                                );
                            }
                            if let Some(init_expr) = initializer {
                                self.check_expression(*init_expr, filename);
                            }
                        }
                        crate::parser::ast::ForInit::Expr(expr) => {
                            self.check_expression(expr, filename);
                        }
                    }
                }

                if let Some(cond) = cond {
                    self.check_expression(*cond, filename);
                }

                if let Some(inc) = inc {
                    self.check_expression(*inc, filename);
                }

                self.check_statement(*body, filename);
            }
            Stmt::Block(stmts) => {
                for stmt in stmts {
                    self.check_statement(stmt, filename);
                }
            }
            _ => {
                // Other statement types (break, continue, etc.) don't need semantic checking
            }
        }
    }

    /// Checks an expression for semantic errors.
    fn check_expression(&mut self, expr: Expr, filename: &str) {
        match expr {
            Expr::Variable(name, location) => {
                if !self.symbol_table.contains_key(&name) {
                    self.errors.push((
                        SemanticError::UndefinedVariable(name.clone()),
                        filename.to_string(),
                        location,
                    ));
                }
            }
            Expr::Call(name, args, location) => {
                // Check if function exists
                if !self.symbol_table.contains_key(&name) {
                    self.errors.push((
                        SemanticError::UndefinedFunction(name.clone()),
                        filename.to_string(),
                        location,
                    ));
                }

                // Check arguments
                for arg in args {
                    self.check_expression(arg, filename);
                }
            }
            Expr::Assign(_, rhs) => {
                self.check_expression(*rhs, filename);
            }
            Expr::AssignAdd(lhs, rhs)
            | Expr::AssignSub(lhs, rhs)
            | Expr::AssignMul(lhs, rhs)
            | Expr::AssignDiv(lhs, rhs)
            | Expr::AssignMod(lhs, rhs)
            | Expr::AssignLeftShift(lhs, rhs)
            | Expr::AssignRightShift(lhs, rhs)
            | Expr::AssignBitwiseAnd(lhs, rhs)
            | Expr::AssignBitwiseXor(lhs, rhs)
            | Expr::AssignBitwiseOr(lhs, rhs) => {
                self.check_expression(*lhs, filename);
                self.check_expression(*rhs, filename);
            }
            Expr::Add(lhs, rhs)
            | Expr::Sub(lhs, rhs)
            | Expr::Mul(lhs, rhs)
            | Expr::Div(lhs, rhs)
            | Expr::Mod(lhs, rhs) => {
                self.check_expression(*lhs, filename);
                self.check_expression(*rhs, filename);
            }
            Expr::Equal(lhs, rhs)
            | Expr::NotEqual(lhs, rhs)
            | Expr::LessThan(lhs, rhs)
            | Expr::GreaterThan(lhs, rhs)
            | Expr::LessThanOrEqual(lhs, rhs)
            | Expr::GreaterThanOrEqual(lhs, rhs) => {
                self.check_expression(*lhs, filename);
                self.check_expression(*rhs, filename);
            }
            Expr::LogicalAnd(lhs, rhs)
            | Expr::LogicalOr(lhs, rhs)
            | Expr::BitwiseOr(lhs, rhs)
            | Expr::BitwiseXor(lhs, rhs)
            | Expr::BitwiseAnd(lhs, rhs)
            | Expr::LeftShift(lhs, rhs)
            | Expr::RightShift(lhs, rhs) => {
                self.check_expression(*lhs, filename);
                self.check_expression(*rhs, filename);
            }
            Expr::Comma(lhs, rhs) => {
                self.check_expression(*lhs, filename);
                self.check_expression(*rhs, filename);
            }
            Expr::Neg(expr)
            | Expr::LogicalNot(expr)
            | Expr::BitwiseNot(expr)
            | Expr::Sizeof(expr)
            | Expr::Deref(expr)
            | Expr::AddressOf(expr) => {
                self.check_expression(*expr, filename);
            }
            Expr::SizeofType(_) => {
                // No need to check, as it's a type
            }
            Expr::Ternary(cond, then_expr, else_expr) => {
                self.check_expression(*cond, filename);
                self.check_expression(*then_expr, filename);
                self.check_expression(*else_expr, filename);
            }
            Expr::Member(expr, _) => {
                self.check_expression(*expr, filename);
            }
            Expr::PointerMember(expr, _) => {
                self.check_expression(*expr, filename);
            }
            Expr::StructInitializer(exprs) => {
                for expr in exprs {
                    self.check_expression(expr, filename);
                }
            }
            Expr::DesignatedInitializer(_, expr) => {
                self.check_expression(*expr, filename);
            }
            Expr::Cast(_, expr) => {
                self.check_expression(*expr, filename);
            }
            Expr::CompoundLiteral(_, exprs) => {
                for expr in exprs {
                    self.check_expression(expr, filename);
                }
            }
            // Literals don't need checking
            Expr::Number(_) | Expr::String(_) | Expr::Char(_) => {}
            Expr::Increment(expr) | Expr::Decrement(expr) | Expr::PostIncrement(expr) | Expr::PostDecrement(expr) => {
                // These are handled by the parser, but we'll check the expression anyway
                self.check_expression(*expr, filename);
            }
        }
    }
}
