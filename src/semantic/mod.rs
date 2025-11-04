use crate::SourceSpan;
use crate::parser::ast::{
    AssignOp, BinOp, Decl, Designator, Expr, ForInit, FuncDecl, Function, Initializer, Stmt, TranslationUnit, Type, TypeSpec, TypeSpecKind, TypedDeclarator, TypedDesignator, TypedExpr, TypedForInit, TypedFunctionDecl, TypedInitializer, TypedLValue, TypedParameter, TypedStmt, TypedTranslationUnit, VarDecl
};
use crate::parser::string_interner::StringInterner;
use crate::semantic::error::SemanticError;
use std::collections::HashMap;
use thin_vec::ThinVec;
mod expressions;
use expressions::TypedExpression;
use std::collections::hash_map::Entry::Vacant;
use symbol_table::GlobalSymbol as StringId;
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
    scopes: Vec<HashMap<StringId, Symbol>>,
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
    fn insert(&mut self, name: StringId, symbol: Symbol) {
        if let Some(scope) = self.scopes.last_mut() {
            scope.insert(name, symbol);
        }
    }

    /// Looks up a symbol starting from the current scope and moving outwards.
    fn lookup(&self, name: &StringId) -> Option<&Symbol> {
        for scope in self.scopes.iter().rev() {
            if let Some(symbol) = scope.get(name) {
                return Some(symbol);
            }
        }
        None
    }

    /// Checks if a symbol exists in any scope.
    fn contains_key(&self, name: &StringId) -> bool {
        self.lookup(name).is_some()
    }
}

use std::collections::HashSet;

pub struct SemaOutput(
    pub TypedTranslationUnit,
    pub Vec<(SemanticError, SourceSpan)>,
    pub SemanticAnalyzer,
);

/// A semantic analyzer that checks for semantic errors in the AST.
pub struct SemanticAnalyzer {
    symbol_table: SymbolTable,
    pub enum_constants: HashMap<StringId, i64>,
    struct_definitions: HashMap<StringId, Type>,
    union_definitions: HashMap<StringId, Type>,
    current_function: Option<StringId>,
    labels: HashMap<StringId, SourceSpan>,
    errors: Vec<(SemanticError, SourceSpan)>, // (error, file, span)
    warnings: Vec<(SemanticError, SourceSpan)>, // (warning, file, span)
    used_builtins: HashSet<StringId>,
    used_variables: HashSet<StringId>,
    in_loop: bool,
    in_switch: bool,
    case_labels: HashSet<i64>,
    has_default: bool,
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
            in_loop: false,
            in_switch: false,
            case_labels: HashSet::new(),
            has_default: false,
        }
    }

    /// Creates a new `SemanticAnalyzer` with built-in functions.
    pub fn with_builtins() -> Self {
        let mut analyzer = Self::new();
        analyzer.add_builtin_functions();
        analyzer
    }

    fn check_lvalue(&mut self, expr: TypedExpr) -> Result<TypedLValue, SemanticError> {
        match expr {
            TypedExpr::Variable(name, span, ty) => Ok(TypedLValue::Variable(name, span, ty)),
            TypedExpr::Deref(expr, span, ty) => Ok(TypedLValue::Deref(expr, span, ty)),
            TypedExpr::Member(expr, member, span, ty) => {
                Ok(TypedLValue::Member(expr, member, span, ty))
            }
            TypedExpr::String(s, span, ty) => Ok(TypedLValue::String(s, span, ty)),
            _ => Err(SemanticError::NotAnLvalue),
        }
    }

    /// Adds built-in functions to the symbol table.
    fn add_builtin_functions(&mut self) {
        // Add common C built-in functions that might be called
        let builtins = vec![
            ("printf", Type::Int(SourceSpan::default())),
            (
                "malloc",
                Type::Pointer(
                    Box::new(Type::Void(SourceSpan::default())),
                    SourceSpan::default(),
                ),
            ),
            ("free", Type::Void(SourceSpan::default())),
            ("scanf", Type::Int(SourceSpan::default())),
            ("strcmp", Type::Int(SourceSpan::default())),
            (
                "memcpy",
                Type::Pointer(
                    Box::new(Type::Void(SourceSpan::default())),
                    SourceSpan::default(),
                ),
            ),
        ];

        for (name, return_type) in builtins {
            self.symbol_table.insert(
                StringInterner::intern(name),
                Symbol {
                    ty: return_type,
                    is_function: true,
                    span: SourceSpan::default(),
                    is_builtin: true,
                },
            );
        }
    }
    fn err(&mut self, error: SemanticError, span: SourceSpan) {
        self.errors.push((error, span));
    }

    fn find_member_recursively(&self, ty: &Type, member_name: &StringId) -> Option<Type> {
        let resolved_ty = self.resolve_type(ty);
        let members = match &resolved_ty {
            Type::Struct(_, members, _) | Type::Union(_, members, _) => members,
            _ => return None,
        };

        // 1. Search direct members
        if let Some(member) = members.iter().find(|p| p.name == *member_name) {
            return Some(member.ty.clone());
        }

        // 2. Search anonymous members
        let empty_name = StringInterner::intern("");
        for member in members {
            if member.name == empty_name
                && let Type::Struct(_, _, _) | Type::Union(_, _, _) = &member.ty
                    && let Some(found_ty) = self.find_member_recursively(&member.ty, member_name) {
                        return Some(found_ty);
                    }
        }
        None
    }

    fn resolve_type(&self, ty: &Type) -> Type {
        match ty {
            Type::Pointer(base, span) => Type::Pointer(Box::new(self.resolve_type(base)), *span),
            Type::Array(base, size, span) => {
                Type::Array(Box::new(self.resolve_type(base)), *size, *span)
            }
            Type::Const(base, span) => Type::Const(Box::new(self.resolve_type(base)), *span),
            Type::Volatile(base, span) => Type::Volatile(Box::new(self.resolve_type(base)), *span),
            Type::Struct(Some(name), members, _) if members.is_empty() => self
                .struct_definitions
                .get(name)
                .cloned()
                .unwrap_or_else(|| ty.clone()),
            Type::Union(Some(name), members, _) if members.is_empty() => self
                .union_definitions
                .get(name)
                .cloned()
                .unwrap_or_else(|| ty.clone()),
            Type::Struct(name, members, span) => {
                let resolved_members = members
                    .iter()
                    .map(|p| {
                        let mut new_p = p.clone();
                        new_p.ty = self.resolve_type(&p.ty);
                        new_p
                    })
                    .collect();
                Type::Struct(*name, resolved_members, *span)
            }
            Type::Union(name, members, span) => {
                let resolved_members = members
                    .iter()
                    .map(|p| {
                        let mut new_p = p.clone();
                        new_p.ty = self.resolve_type(&p.ty);
                        new_p
                    })
                    .collect();
                Type::Union(*name, resolved_members, *span)
            }
            _ => ty.clone(),
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
    ) -> Result<SemaOutput, Vec<(SemanticError, SourceSpan)>> {
        // First pass: collect all function definitions and global declarations
        self.collect_symbols(&program);

        // Second pass: check all expressions and statements for semantic errors and build typed AST
        let typed_program = self.check_program(program);

        if self.errors.is_empty() {
            Ok(SemaOutput(typed_program, self.warnings.clone(), self))
        } else {
            Err(self.errors)
        }
    }

    /// First pass: collect all symbols (functions and global variables).
    fn collect_symbols(&mut self, program: &TranslationUnit) {
        for global in &program.globals {
            match global {
                Decl::Func(FuncDecl { return_type, name, params, .. }) => {
                    let span = return_type.span();
                    if let Some(existing) = self.symbol_table.lookup(name) {
                        if existing.is_function {
                            self.err(SemanticError::FunctionRedeclaration(*name), span);
                        }
                    } else {
                        let ty = Type::from_type_spec(&return_type, span);
                        self.symbol_table.insert(
                            *name,
                            Symbol {
                                ty,
                                is_function: true,
                                span,
                                is_builtin: false,
                            },
                        );
                    }
                }
                Decl::Var(VarDecl { type_spec, name, init, span }) => {
                    // Convert TypeSpec to Type for processing
                    let converted_ty = Type::from_type_spec(&type_spec, SourceSpan::default());

                    if let Type::Enum(_name, members, _) = &converted_ty
                        && !members.is_empty()
                    {
                        let mut next_value = 0;
                        for (name, value, span) in members {
                            let val = if let Some(expr) = value {
                                if let Expr::Number(num, _) = **expr {
                                    num
                                } else {
                                    self.err(SemanticError::InvalidEnumInitializer(*name), *span);
                                    -1 // Dummy value
                                }
                            } else {
                                next_value
                            };

                            if self.enum_constants.contains_key(name) {
                                self.err(SemanticError::VariableRedeclaration(*name), *span);
                            } else {
                                self.enum_constants.insert(*name, val);
                            }
                            next_value = val + 1;
                        }
                    } else if let Type::Struct(Some(name), members, _) = &converted_ty {
                        if !members.is_empty() || !self.struct_definitions.contains_key(name) {
                            self.struct_definitions.insert(*name, converted_ty);
                        }
                    } else if let Type::Union(Some(name), members, _) = &converted_ty
                        && (!members.is_empty() || !self.union_definitions.contains_key(name))
                    {
                        self.union_definitions.insert(*name, converted_ty);
                    }

                    // Global variables can be redeclared (tentative definitions)
                    // Only check for conflicts with functions
                    if let Some(existing) = self.symbol_table.lookup(name) {
                        if existing.is_function {
                            self.err(
                                SemanticError::VariableRedeclaration(*name),
                                *span,
                            );
                        }
                    } else {
                        self.symbol_table.insert(
                            *name,
                            Symbol {
                                ty: Type::from_type_spec(&type_spec, *span),
                                is_function: false,
                                span: *span,
                                is_builtin: false,
                            },
                        );
                    }
                }
                Decl::Struct(_) | Decl::Union(_) | Decl::Enum(_) | Decl::Typedef(_, _) | Decl::StaticAssert(_, _) => {
                    // Handle struct/union/enum declarations, typedefs, and static asserts
                    // For now, just collect struct/union/enum definitions
                    let converted_ty = match global {
                        Decl::Struct(struct_decl) => {
                            if !struct_decl.fields.is_empty() {
                                Type::Struct(Some(struct_decl.name.unwrap_or(crate::parser::string_interner::StringInterner::empty_id())), ThinVec::new(), struct_decl.span)
                            } else {
                                return;
                            }
                        }
                        Decl::Union(union_decl) => {
                            if !union_decl.fields.is_empty() {
                                Type::Union(Some(union_decl.name.unwrap_or(crate::parser::string_interner::StringInterner::empty_id())), ThinVec::new(), union_decl.span)
                            } else {
                                return;
                            }
                        }
                        Decl::Enum(enum_decl) => {
                            if !enum_decl.members.is_empty() {
                                let mut next_value = 0;
                                for member in &enum_decl.members {
                                    let val = if let Some(ref expr) = member.value {
                                        if let Expr::Number(num, _) = **expr {
                                            num
                                        } else {
                                            self.err(SemanticError::InvalidEnumInitializer(member.name), member.span);
                                            -1 // Dummy value
                                        }
                                    } else {
                                        next_value
                                    };

                                    if self.enum_constants.contains_key(&member.name) {
                                        self.err(SemanticError::VariableRedeclaration(member.name), member.span);
                                    } else {
                                        self.enum_constants.insert(member.name, val);
                                    }
                                    next_value = val + 1;
                                }
                                Type::Enum(Some(enum_decl.name.unwrap_or(crate::parser::string_interner::StringInterner::empty_id())), ThinVec::new(), enum_decl.span)
                            } else {
                                return;
                            }
                        }
                        Decl::Typedef(name, type_spec) => {
                            // Handle typedef - typedefs are handled in the parser, no action needed here
                            return;
                        }
                        Decl::StaticAssert(expr, message) => {
                            // Handle static assert
                            // For global static assert, we can evaluate it here
                            // But for simplicity, we'll skip for now
                            return;
                        }
                        _ => return,
                    };

                    if let Type::Struct(Some(name), _, _) = &converted_ty {
                        self.struct_definitions.insert(name.clone(), converted_ty);
                    } else if let Type::Union(Some(name), _, _) = &converted_ty {
                        self.union_definitions.insert(name.clone(), converted_ty);
                    }
                }
                _ => {}
            }
        }

        // Collect function definitions
        for function in &program.functions {
            let span = function.return_type.span();
            if let Some(existing) = self.symbol_table.lookup(&function.name) {
                if existing.is_function {
                    self.err(SemanticError::FunctionRedeclaration(function.name), span);
                }
            } else {
                let ty = Type::from_type_spec(&function.return_type, span);
                self.symbol_table.insert(
                    function.name,
                    Symbol {
                        ty,
                        is_function: true,
                        span,
                        is_builtin: false,
                    },
                );
            }
        }
    }

    /// Second pass: check all statements and expressions for semantic correctness and build typed AST.
    fn check_program(&mut self, program: TranslationUnit) -> TypedTranslationUnit {
        let mut typed_functions = Vec::new();
        for function in program.functions {
            self.current_function = Some(function.name);
            typed_functions.push(self.check_function(function));
        }

        let mut typed_globals = Vec::new();
        for global in program.globals {
            // Handle global declarations properly
            match global {
                Decl::Var(var_decl) => {
                    // Create a TypedStmt for variable declarations
                    // For now, we'll create a dummy TypedStmt::Empty
                    // In a full implementation, we might need to create a proper TypedStmt variant for declarations
                    typed_globals.push(TypedStmt::Empty);
                }
                Decl::Func(func_decl) => {
                    // Function declarations are handled separately in functions
                    // For now, create a dummy TypedStmt::Empty
                    typed_globals.push(TypedStmt::Empty);
                }
                Decl::FuncDef(func_decl) => {
                    // Function definitions are handled separately in functions
                    // For now, create a dummy TypedStmt::Empty
                    typed_globals.push(TypedStmt::Empty);
                }
                Decl::Struct(_) | Decl::Union(_) | Decl::Enum(_) | Decl::Typedef(_, _) | Decl::StaticAssert(_, _) => {
                    // For now, create a dummy TypedStmt for other declarations
                    typed_globals.push(TypedStmt::Empty);
                }
            }
        }

        // Add built-in function declarations to the typed AST
        for name in &self.used_builtins {
            if let Some(symbol) = self.symbol_table.lookup(name) {
                typed_globals.push(TypedStmt::FunctionDeclaration {
                    ty: symbol.ty.clone(),
                    name: *name,
                    params: ThinVec::new(), // Built-ins don't have specified params in this context
                    is_variadic: true,      // Assume built-ins can be variadic
                    is_inline: false,
                    is_noreturn: false,
                });
            }
        }

        // Add built-in function declarations to the typed AST if they are used and not declared.
        let declared_functions: std::collections::HashSet<_> = typed_globals
            .iter()
            .filter_map(|stmt| {
                if let TypedStmt::FunctionDeclaration { name, .. } = stmt {
                    Some(*name)
                } else {
                    None
                }
            })
            .collect();

        for name in &self.used_builtins {
            if !declared_functions.contains(name)
                && let Some(symbol) = self.symbol_table.lookup(name)
            {
                typed_globals.push(TypedStmt::FunctionDeclaration {
                    ty: symbol.ty.clone(),
                    name: *name,
                    params: ThinVec::new(),
                    is_variadic: true, // Assume variadic
                    is_inline: false,
                    is_noreturn: false,
                });
            }
        }

        TypedTranslationUnit {
            globals: typed_globals.into(),
            functions: typed_functions.into(),
        }
    }

    /// Collects all labels defined in a function's statements.
    fn collect_labels(&mut self, stmts: &[Stmt]) {
        for stmt in stmts {
            match stmt {
                Stmt::Label(name, body, span) => {
                    if self.labels.contains_key(name) {
                        self.err(SemanticError::VariableRedeclaration(*name), *span);
                    } else {
                        self.labels.insert(*name, *span);
                    }
                    self.collect_labels(&[*body.clone()]);
                }
                Stmt::Block(stmts) => {
                    self.collect_labels(stmts);
                }
                Stmt::If(_, then, otherwise) => {
                    self.collect_labels(&[*then.clone()]);
                    if let Some(otherwise) = otherwise {
                        self.collect_labels(&[*otherwise.clone()]);
                    }
                }
                Stmt::While(_, body) => {
                    self.collect_labels(&[*body.clone()]);
                }
                Stmt::For(_, _, _, body) => {
                    self.collect_labels(&[*body.clone()]);
                }
                Stmt::DoWhile(body, _) => {
                    self.collect_labels(&[*body.clone()]);
                }
                Stmt::Switch(_, body) => {
                    self.collect_labels(&[*body.clone()]);
                }
                Stmt::Case(_, body) => {
                    self.collect_labels(&[*body.clone()]);
                }
                Stmt::Default(body) => {
                    self.collect_labels(&[*body.clone()]);
                }
                _ => {}
            }
        }
    }

    /// Checks a function for semantic errors and returns a typed function declaration.
    fn check_function(&mut self, function: Function) -> TypedFunctionDecl {
        // Push function scope
        self.symbol_table.push_scope();

        // Clear labels for this function
        self.labels.clear();

        // First pass: collect all labels in the function
        self.collect_labels(&function.body);

        // Check parameters for redeclaration and convert to TypedParameter
        let mut param_names = std::collections::HashSet::new();
        let mut typed_params = ThinVec::new();
        for param in &function.params {
            if !param_names.insert(param.name) {
                self.err(SemanticError::VariableRedeclaration(param.name), param.span);
            }
            // Convert TypeSpec to Type and create TypedParameter
            let ty = Type::from_type_spec(&param.ty, param.span);
            let typed_param = TypedParameter {
                ty: ty.clone(),
                name: param.name,
                span: param.span,
            };
            typed_params.push(typed_param);
            
            // Add parameters to local symbol table
            self.symbol_table.insert(
                param.name,
                Symbol {
                    ty,
                    is_function: false,
                    span: param.span,
                    is_builtin: false,
                },
            );
        }

        // Check function body and build typed statements
        let mut typed_body = ThinVec::new();
        for stmt in function.body {
            typed_body.push(self.check_statement(stmt));
        }

        // Check for unused variables
        for (name, symbol) in self.symbol_table.scopes.last().unwrap() {
            if !self.used_variables.contains(name) {
                self.warnings
                    .push((SemanticError::UnusedVariable(name.to_string()), symbol.span));
            }
        }

        // Pop function scope
        self.symbol_table.pop_scope();
        self.current_function = None;
        self.used_variables.clear();

        let return_type = Type::from_type_spec(&function.return_type, SourceSpan::default());
        TypedFunctionDecl {
            return_type,
            name: function.name,
            params: typed_params,
            body: typed_body,
            is_inline: function.is_inline,
            is_variadic: function.is_variadic,
            is_noreturn: function.is_noreturn,
        }
    }

    /// Checks a statement for semantic errors and returns a typed statement.
    fn check_statement(&mut self, stmt: Stmt) -> TypedStmt {
        match stmt {
            Stmt::Expr(expr) => {
                let typed_expr = self.check_expression(*expr);
                TypedStmt::Expr(typed_expr)
            }
            Stmt::Return(expr) => {
                let typed_expr = self.check_expression(*expr);
                TypedStmt::Return(typed_expr)
            }
            Stmt::If(cond, then, otherwise) => {
                let typed_cond = self.check_expression(*cond);
                let typed_then = Box::new(self.check_statement(*then));
                let typed_otherwise = otherwise.map(|o| Box::new(self.check_statement(*o)));
                TypedStmt::If(typed_cond, typed_then, typed_otherwise)
            }
            Stmt::While(cond, body) => {
                let prev_in_loop = self.in_loop;
                self.in_loop = true;
                let typed_cond = self.check_expression(*cond);
                let typed_body = Box::new(self.check_statement(*body));
                self.in_loop = prev_in_loop;
                TypedStmt::While(typed_cond, typed_body)
            }
            Stmt::For(init, cond, inc, body) => {
                let typed_init = init.map(|i| match *i {
                    ForInit::Declaration(type_spec, name, initializer) => {
                        if let Some(existing) = self.symbol_table.lookup(&name) {
                            if !existing.is_function {
                                self.err(
                                    SemanticError::FunctionRedeclaration(name),
                                    SourceSpan::default(),
                                );
                            }
                        } else {
                            let ty = Type::from_type_spec(&type_spec, SourceSpan::default());
                            self.symbol_table.insert(
                                name,
                                Symbol {
                                    ty,
                                    is_function: false,
                                    span: SourceSpan::default(),
                                    is_builtin: false,
                                },
                            );
                        }
                        let typed_initializer =
                            initializer.map(|init| self.convert_initializer_to_typed(init));
                        let ty = Type::from_type_spec(&type_spec, SourceSpan::default());
                        TypedForInit::Declaration(ty, name, typed_initializer)
                    }
                    ForInit::Expr(expr) => {
                        let typed_expr = self.check_expression(expr);
                        TypedForInit::Expr(typed_expr)
                    }
                });

                let prev_in_loop = self.in_loop;
                self.in_loop = true;
                let typed_cond = cond.map(|c| self.check_expression(*c));
                let typed_inc = inc.map(|i| self.check_expression(*i));
                let typed_body = Box::new(self.check_statement(*body));
                self.in_loop = prev_in_loop;

                TypedStmt::For(
                    Box::new(typed_init),
                    Box::new(typed_cond),
                    Box::new(typed_inc),
                    typed_body,
                )
            }
            Stmt::Block(stmts) => {
                self.symbol_table.push_scope();
                let typed_stmts = stmts.into_iter().map(|s| self.check_statement(s)).collect();
                self.symbol_table.pop_scope();
                TypedStmt::Block(typed_stmts)
            }
            Stmt::Switch(expr, body) => {
                let prev_in_switch = self.in_switch;
                let prev_case_labels = self.case_labels.clone();
                let prev_has_default = self.has_default;

                self.in_switch = true;
                self.case_labels.clear();
                self.has_default = false;

                let typed_expr = self.check_expression(*expr);
                if typed_expr.ty().get_integer_rank() == 0 {
                    self.err(SemanticError::SwitchConditionNotInteger, typed_expr.span());
                }

                let typed_body = Box::new(self.check_statement(*body));

                self.in_switch = prev_in_switch;
                self.case_labels = prev_case_labels;
                self.has_default = prev_has_default;

                TypedStmt::Switch(typed_expr, typed_body)
            }
            Stmt::Case(expr, body) => {
                let span = (*expr).span();
                if !self.in_switch {
                    self.err(SemanticError::CaseOutsideSwitch, span);
                }
                let typed_expr = self.check_expression(*expr);
                if let TypedExpr::Number(val, _, _) = typed_expr {
                    if !self.case_labels.insert(val) {
                        self.err(SemanticError::DuplicateCaseLabel(val), typed_expr.span());
                    }
                } else {
                    self.err(SemanticError::NotAConstantExpression, typed_expr.span());
                }
                let typed_body = Box::new(self.check_statement(*body));
                TypedStmt::Case(typed_expr, typed_body)
            }
            Stmt::Default(body) => {
                if !self.in_switch {
                    self.err(SemanticError::DefaultOutsideSwitch, (*body).span());
                }
                if self.has_default {
                    self.err(SemanticError::DuplicateDefaultLabel, (*body).span());
                }
                self.has_default = true;
                let typed_body = Box::new(self.check_statement(*body));
                TypedStmt::Default(typed_body)
            }
            Stmt::Label(label, body, _) => {
                let typed_body = Box::new(self.check_statement(*body));
                TypedStmt::Label(label, typed_body)
            }
            Stmt::Goto(label, span) => {
                if !self.labels.contains_key(&label) {
                    self.err(SemanticError::UndefinedLabel(label), span);
                }
                TypedStmt::Goto(label)
            }
            Stmt::Break => {
                if !self.in_switch && !self.in_loop {
                    self.err(
                        SemanticError::BreakOutsideLoopOrSwitch,
                        SourceSpan::default(),
                    );
                }
                TypedStmt::Break
            }
            Stmt::Continue => {
                if !self.in_loop {
                    self.err(SemanticError::ContinueOutsideLoop, SourceSpan::default());
                }
                TypedStmt::Continue
            }
            Stmt::DoWhile(body, cond) => {
                let prev_in_loop = self.in_loop;
                self.in_loop = true;
                let typed_body = Box::new(self.check_statement(*body));
                let typed_cond = self.check_expression(*cond);
                self.in_loop = prev_in_loop;
                TypedStmt::DoWhile(typed_body, typed_cond)
            }
            Stmt::Empty => TypedStmt::Empty,
            Stmt::Declaration(type_spec, declarators, is_typedef) => {
                let ty = Type::from_type_spec(&type_spec, SourceSpan::default());
                let mut typed_declarators = ThinVec::new();
                for declarator in declarators {
                    let typed_initializer = declarator.initializer.as_ref().map(|init| self.convert_initializer_to_typed(init.clone()));
                    typed_declarators.push(TypedDeclarator {
                        ty: ty.clone(),
                        name: declarator.name,
                        initializer: typed_initializer,
                    });
                }
                TypedStmt::Declaration(ty, typed_declarators, is_typedef)
            }
        }
    }

    /// Checks a binary expression for semantic errors and returns a typed expression.
    fn check_binary_expression(&mut self, op: BinOp, lhs: &Expr, rhs: &Expr) -> TypedExpr {
        let mut lhs_typed = self.check_expression(lhs.clone());
        if let Type::Array(elem_ty, _, span) = lhs_typed.ty().clone() {
            lhs_typed = lhs_typed.implicit_cast(Type::Pointer(elem_ty.clone(), span));
        }

        let mut rhs_typed = self.check_expression(rhs.clone());
        if let Type::Array(elem_ty, _, span) = rhs_typed.ty().clone() {
            rhs_typed = rhs_typed.implicit_cast(Type::Pointer(elem_ty.clone(), span));
        }

        let lhs_ty = lhs_typed.ty().clone();
        let rhs_ty = rhs_typed.ty().clone();

        let (lhs_final, rhs_final, result_ty) = match op {
            BinOp::Add | BinOp::Sub => {
                if lhs_ty.is_pointer() || rhs_ty.is_pointer() {
                    // Pointer arithmetic
                    let result_ty = match (lhs_ty.unwrap_const(), rhs_ty.unwrap_const()) {
                        (Type::Pointer(_, span), Type::Pointer(_, _)) if op == BinOp::Sub => {
                            Type::Int(*span)
                        }
                        (Type::Pointer(_, _), ty) if ty.get_integer_rank() > 0 => lhs_ty.clone(),
                        (ty, Type::Pointer(_, _))
                            if ty.get_integer_rank() > 0 && op == BinOp::Add =>
                        {
                            rhs_ty.clone()
                        }
                        _ => {
                            self.err(
                                SemanticError::TypeMismatch,
                                SourceSpan::default(), // Consider improving span info
                            );
                            Type::Int(SourceSpan::default()) // dummy type
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
            BinOp::Equal
            | BinOp::NotEqual
            | BinOp::LessThan
            | BinOp::GreaterThan
            | BinOp::LessThanOrEqual
            | BinOp::GreaterThanOrEqual => {
                (lhs_typed, rhs_typed, Type::Bool(SourceSpan::default()))
            }
            BinOp::LogicalAnd | BinOp::LogicalOr => {
                (lhs_typed, rhs_typed, Type::Bool(SourceSpan::default()))
            }
            BinOp::BitwiseOr | BinOp::BitwiseXor | BinOp::BitwiseAnd => {
                (lhs_typed, rhs_typed, Type::Int(SourceSpan::default()))
            }
            BinOp::LeftShift | BinOp::RightShift => (lhs_typed, rhs_typed, lhs_ty.clone()),
            BinOp::Comma => (lhs_typed, rhs_typed, rhs_ty.clone()),
        };

        TypedExpression::new(op, lhs_final, rhs_final, result_ty).into()
    }

    fn check_assignment_expression(&mut self, op: AssignOp, lhs: &Expr, rhs: &Expr) -> TypedExpr {
        let lhs_typed = self.check_expression(lhs.clone());
        let rhs_typed = self.check_expression(rhs.clone());

        let lhs_lvalue = match self.check_lvalue(lhs_typed.clone()) {
            Ok(lvalue) => lvalue,
            Err(err) => {
                self.err(err, lhs_typed.span());
                // Create a dummy l-value to continue analysis
                TypedLValue::Variable(
                    StringInterner::intern(""),
                    SourceSpan::default(),
                    Type::Int(SourceSpan::default()),
                )
            }
        };

        if let TypedExpr::CompoundLiteral(_, _, _, ty) = &rhs_typed
            && let Type::Array(elem_ty, _, span) = ty {
                let pointer_ty = Type::Pointer(elem_ty.clone(), *span);
                if lhs_lvalue.ty().is_pointer() && lhs_lvalue.ty().is_pointer() {
                    let rhs_cast = rhs_typed.implicit_cast(pointer_ty);
                    return TypedExpr::Assign(
                        Box::new(lhs_lvalue.clone()),
                        Box::new(rhs_cast),
                        SourceSpan::default(),
                        lhs_lvalue.ty().clone(),
                    );
                }
            }

        let lhs_ty = lhs_lvalue.ty().clone();
        let lhs_span = match &lhs_lvalue {
            TypedLValue::Variable(_, span, _) => *span,
            TypedLValue::Deref(expr, _, _) => expr.span(),
            TypedLValue::Member(expr, _, _, _) => expr.span(),
            TypedLValue::String(_, span, _) => *span,
        };

        if !lhs_lvalue.is_modifiable() {
            self.err(SemanticError::AssignmentToConst, lhs_span);
        } else if let Type::Const(_, _) = &lhs_ty.unwrap_volatile() {
            self.err(SemanticError::AssignmentToConst, lhs_span);
        }

        let rhs_cast = rhs_typed.implicit_cast(lhs_ty.clone());
        let result_ty = lhs_ty;

        match op {
            AssignOp::Assign => TypedExpr::Assign(
                Box::new(lhs_lvalue),
                Box::new(rhs_cast),
                SourceSpan::default(),
                result_ty,
            ),
            AssignOp::Add => TypedExpr::AssignAdd(
                Box::new(lhs_lvalue),
                Box::new(rhs_cast),
                SourceSpan::default(),
                result_ty,
            ),
            AssignOp::Sub => TypedExpr::AssignSub(
                Box::new(lhs_lvalue),
                Box::new(rhs_cast),
                SourceSpan::default(),
                result_ty,
            ),
            AssignOp::Mul => TypedExpr::AssignMul(
                Box::new(lhs_lvalue),
                Box::new(rhs_cast),
                SourceSpan::default(),
                result_ty,
            ),
            AssignOp::Div => TypedExpr::AssignDiv(
                Box::new(lhs_lvalue),
                Box::new(rhs_cast),
                SourceSpan::default(),
                result_ty,
            ),
            AssignOp::Mod => TypedExpr::AssignMod(
                Box::new(lhs_lvalue),
                Box::new(rhs_cast),
                SourceSpan::default(),
                result_ty,
            ),
            AssignOp::LeftShift => TypedExpr::AssignLeftShift(
                Box::new(lhs_lvalue),
                Box::new(rhs_cast),
                SourceSpan::default(),
                result_ty,
            ),
            AssignOp::RightShift => TypedExpr::AssignRightShift(
                Box::new(lhs_lvalue),
                Box::new(rhs_cast),
                SourceSpan::default(),
                result_ty,
            ),
            AssignOp::BitwiseAnd => TypedExpr::AssignBitwiseAnd(
                Box::new(lhs_lvalue),
                Box::new(rhs_cast),
                SourceSpan::default(),
                result_ty,
            ),
            AssignOp::BitwiseXor => TypedExpr::AssignBitwiseXor(
                Box::new(lhs_lvalue),
                Box::new(rhs_cast),
                SourceSpan::default(),
                result_ty,
            ),
            AssignOp::BitwiseOr => TypedExpr::AssignBitwiseOr(
                Box::new(lhs_lvalue),
                Box::new(rhs_cast),
                SourceSpan::default(),
                result_ty,
            ),
        }
    }

    /// Checks an expression for semantic errors and returns a typed expression.
    fn check_expression(&mut self, expr: Expr) -> TypedExpr {
        if let Some((op, lhs, rhs)) = expr.get_binary_expr() {
            return self.check_binary_expression(op, lhs, rhs);
        } else if let Some((op, lhs, rhs)) = expr.get_assign_expr() {
            return self.check_assignment_expression(op, lhs, rhs);
        }

        match expr {
            Expr::Variable(name, location) => {
                self.used_variables.insert(name);
                if !self.symbol_table.contains_key(&name)
                    && !self.enum_constants.contains_key(&name)
                {
                    self.err(SemanticError::UndefinedVariable(name), location);
                }
                let ty = self
                    .symbol_table
                    .lookup(&name)
                    .map(|s| s.ty.clone())
                    .unwrap_or(Type::Int(SourceSpan::default()));

                let ty = match ty {
                    Type::Struct(Some(s_name), members, span) if members.is_empty() => self
                        .struct_definitions
                        .get(&s_name)
                        .cloned()
                        .unwrap_or(Type::Struct(Some(s_name), ThinVec::new(), span)),
                    Type::Union(Some(u_name), members, span) if members.is_empty() => self
                        .union_definitions
                        .get(&u_name)
                        .cloned()
                        .unwrap_or(Type::Union(Some(u_name), ThinVec::new(), span)),
                    _ => ty,
                };

                TypedExpr::Variable(name, location, ty)
            }
            Expr::Number(n, span) => TypedExpr::Number(n, span, Type::Int(span)),
            Expr::FloatNumber(n, span) => TypedExpr::FloatNumber(n, span, Type::Double(span)),
            Expr::String(s, span) => {
                TypedExpr::String(s, span, Type::Pointer(Box::new(Type::Char(span)), span))
            }
            Expr::Char(c, span) => TypedExpr::Char(c, span, Type::Char(span)),
            Expr::Call(name, args, location) => {
                if let Some(symbol) = self.symbol_table.lookup(&name) {
                    if symbol.is_builtin {
                        self.used_builtins.insert(name);
                    }
                } else {
                    self.err(SemanticError::UndefinedFunction(name), location);
                }

                let return_ty = self
                    .symbol_table
                    .lookup(&name)
                    .map(|s| s.ty.clone())
                    .unwrap_or(Type::Int(SourceSpan::default()));
                let typed_args = args
                    .into_iter()
                    .map(|arg| self.check_expression(arg))
                    .collect::<ThinVec<_>>();
                TypedExpr::Call(name, typed_args, location, return_ty)
            }
            Expr::Neg(expr) => {
                let typed = self.check_expression(*expr);
                TypedExpr::Neg(
                    Box::new(typed.clone()),
                    SourceSpan::default(),
                    typed.ty().clone(),
                )
            }
            Expr::LogicalNot(expr) => {
                let typed = self.check_expression(*expr);
                TypedExpr::LogicalNot(
                    Box::new(typed),
                    SourceSpan::default(),
                    Type::Bool(SourceSpan::default()),
                )
            }
            Expr::BitwiseNot(expr) => {
                let typed = self.check_expression(*expr);
                TypedExpr::BitwiseNot(
                    Box::new(typed.clone()),
                    SourceSpan::default(),
                    typed.ty().clone(),
                )
            }
            Expr::Sizeof(expr) => {
                let _typed = self.check_expression(*expr);
                TypedExpr::Sizeof(
                    Box::new(_typed),
                    SourceSpan::default(),
                    Type::Int(SourceSpan::default()),
                )
            }
            Expr::Alignof(expr) => {
                let _typed = self.check_expression(*expr);
                TypedExpr::Alignof(
                    Box::new(_typed),
                    SourceSpan::default(),
                    Type::Int(SourceSpan::default()),
                )
            }
            Expr::Deref(expr) => {
                let typed = self.check_expression(*expr);
                let result_ty = match typed.ty().unwrap_const().clone() {
                    Type::Pointer(base_ty, _) => *base_ty,
                    Type::Array(elem_ty, _, _) => *elem_ty,
                    other_ty => {
                        self.err(SemanticError::NotAPointer(other_ty), typed.span());
                        Type::Int(SourceSpan::default())
                    }
                };
                TypedExpr::Deref(Box::new(typed), SourceSpan::default(), result_ty)
            }
            Expr::AddressOf(expr) => {
                let typed_expr = self.check_expression(*expr);
                let lvalue = match self.check_lvalue(typed_expr.clone()) {
                    Ok(lvalue) => lvalue,
                    Err(err) => {
                        self.err(err, typed_expr.span());
                        // Create a dummy l-value to continue analysis
                        TypedLValue::Variable(
                            StringInterner::intern(""),
                            SourceSpan::default(),
                            Type::Int(SourceSpan::default()),
                        )
                    }
                };
                let ty = lvalue.ty().clone();
                TypedExpr::AddressOf(
                    Box::new(lvalue),
                    SourceSpan::default(),
                    Type::Pointer(Box::new(ty), SourceSpan::default()),
                )
            }
            Expr::SizeofType(ty) => {
                let converted_ty = Type::from_type_spec(&ty, SourceSpan::default());
                TypedExpr::SizeofType(converted_ty, SourceSpan::default(), Type::Int(SourceSpan::default()))
            }
            Expr::AlignofType(ty) => {
                let converted_ty = Type::from_type_spec(&ty, SourceSpan::default());
                TypedExpr::AlignofType(converted_ty, SourceSpan::default(), Type::Int(SourceSpan::default()))
            }
            Expr::Ternary(cond, then_expr, else_expr) => {
                let cond_typed = self.check_expression(*cond);
                let then_typed = self.check_expression(*then_expr);
                let else_typed = self.check_expression(*else_expr);
                let result_ty = if then_typed.ty() == else_typed.ty() {
                    then_typed.ty().clone()
                } else {
                    Type::Int(SourceSpan::default())
                };
                TypedExpr::Ternary(
                    Box::new(cond_typed),
                    Box::new(then_typed),
                    Box::new(else_typed),
                    SourceSpan::default(),
                    result_ty,
                )
            }
            Expr::Member(expr, member) => {
                let typed = self.check_expression(*expr);
                let member_ty = self
                    .find_member_recursively(typed.ty(), &member)
                    .unwrap_or_else(|| {
                        self.err(SemanticError::UndefinedMember(member), typed.span());
                        Type::Int(SourceSpan::default()) // Dummy type
                    });
                TypedExpr::Member(Box::new(typed), member, SourceSpan::default(), member_ty)
            }
            Expr::PointerMember(expr, member) => {
                let typed_ptr = self.check_expression(*expr);

                let inner_ty =
                    if let Type::Pointer(inner, _) = typed_ptr.ty().clone().unwrap_const() {
                        inner.clone()
                    } else {
                        self.err(
                            SemanticError::NotAPointer(typed_ptr.ty().clone()),
                            typed_ptr.span(),
                        );
                        return TypedExpr::Number(
                            0,
                            SourceSpan::default(),
                            Type::Int(SourceSpan::default()),
                        );
                    };

                let deref_expr =
                    TypedExpr::Deref(Box::new(typed_ptr), SourceSpan::default(), *inner_ty);

                let member_ty = self
                    .find_member_recursively(deref_expr.ty(), &member)
                    .unwrap_or_else(|| {
                        self.err(SemanticError::UndefinedMember(member), deref_expr.span());
                        Type::Int(SourceSpan::default())
                    });

                TypedExpr::Member(
                    Box::new(deref_expr),
                    member,
                    SourceSpan::default(),
                    member_ty,
                )
            }
            Expr::InitializerList(list) => {
                let typed_list = list
                    .into_iter()
                    .map(|(designators, initializer)| {
                        let typed_designators = designators
                            .into_iter()
                            .map(|d| match d {
                                Designator::Index(expr) => {
                                    TypedDesignator::Index(Box::new(self.check_expression(*expr)))
                                }
                                Designator::Member(name) => TypedDesignator::Member(name),
                            })
                            .collect();
                        let typed_initializer = self.convert_initializer_to_typed(*initializer);
                        (typed_designators, Box::new(typed_initializer))
                    })
                    .collect();
                TypedExpr::InitializerList(
                    typed_list,
                    SourceSpan::default(),
                    Type::Int(SourceSpan::default()),
                )
            }
            Expr::ExplicitCast(ty, expr) => {
                let typed_expr = self.check_expression(*expr);
                let converted_ty = Type::from_type_spec(&ty, SourceSpan::default());
                TypedExpr::ExplicitCast(
                    Box::new(converted_ty.clone()),
                    Box::new(typed_expr),
                    SourceSpan::default(),
                    converted_ty,
                )
            }
            Expr::ImplicitCast(ty, expr) => {
                let typed_expr = self.check_expression(*expr);
                let converted_ty = Type::from_type_spec(&ty, SourceSpan::default());
                TypedExpr::ImplicitCast(
                    Box::new(converted_ty.clone()),
                    Box::new(typed_expr),
                    SourceSpan::default(),
                    converted_ty,
                )
            }
            Expr::CompoundLiteral(ty, initializer) => {
                let typed_initializer = self.convert_initializer_to_typed(*initializer);
                let mut final_ty = Type::from_type_spec(&ty, SourceSpan::default());
                if let Type::Array(elem_ty, 0, span) = &final_ty
                    && let TypedInitializer::List(list) = &typed_initializer
                {
                    final_ty = Type::Array(elem_ty.clone(), list.len(), *span);
                }
                let converted_ty = Box::new(Type::from_type_spec(&ty, SourceSpan::default()));
                let mut typed_expr = TypedExpr::CompoundLiteral(
                    converted_ty,
                    Box::new(typed_initializer),
                    SourceSpan::default(),
                    final_ty.clone(),
                );

                if let Type::Array(elem_ty, _, span) = &final_ty {
                    typed_expr = typed_expr.implicit_cast(Type::Pointer(elem_ty.clone(), *span));
                }

                typed_expr
            }
            Expr::PreIncrement(expr) => {
                let typed_expr = self.check_expression(*expr);
                let lvalue = match self.check_lvalue(typed_expr.clone()) {
                    Ok(lvalue) => lvalue,
                    Err(err) => {
                        self.err(err, typed_expr.span());
                        TypedLValue::Variable(
                            StringInterner::intern(""),
                            SourceSpan::default(),
                            Type::Int(SourceSpan::default()),
                        )
                    }
                };
                if !lvalue.is_modifiable() {
                    self.err(SemanticError::AssignmentToConst, typed_expr.span());
                }
                let ty = lvalue.ty().clone();
                TypedExpr::PreIncrement(Box::new(lvalue), SourceSpan::default(), ty)
            }
            Expr::PreDecrement(expr) => {
                let typed_expr = self.check_expression(*expr);
                let lvalue = match self.check_lvalue(typed_expr.clone()) {
                    Ok(lvalue) => lvalue,
                    Err(err) => {
                        self.err(err, typed_expr.span());
                        TypedLValue::Variable(
                            StringInterner::intern(""),
                            SourceSpan::default(),
                            Type::Int(SourceSpan::default()),
                        )
                    }
                };
                if !lvalue.is_modifiable() {
                    self.err(SemanticError::AssignmentToConst, typed_expr.span());
                }
                let ty = lvalue.ty().clone();
                TypedExpr::PreDecrement(Box::new(lvalue), SourceSpan::default(), ty)
            }
            Expr::PostIncrement(expr) => {
                let typed_expr = self.check_expression(*expr);
                let lvalue = match self.check_lvalue(typed_expr.clone()) {
                    Ok(lvalue) => lvalue,
                    Err(err) => {
                        self.err(err, typed_expr.span());
                        TypedLValue::Variable(
                            StringInterner::intern(""),
                            SourceSpan::default(),
                            Type::Int(SourceSpan::default()),
                        )
                    }
                };
                if !lvalue.is_modifiable() {
                    self.err(SemanticError::AssignmentToConst, typed_expr.span());
                }
                let ty = lvalue.ty().clone();
                TypedExpr::PostIncrement(Box::new(lvalue), SourceSpan::default(), ty)
            }
            Expr::PostDecrement(expr) => {
                let typed_expr = self.check_expression(*expr);
                let lvalue = match self.check_lvalue(typed_expr.clone()) {
                    Ok(lvalue) => lvalue,
                    Err(err) => {
                        self.err(err, typed_expr.span());
                        TypedLValue::Variable(
                            StringInterner::intern(""),
                            SourceSpan::default(),
                            Type::Int(SourceSpan::default()),
                        )
                    }
                };
                if !lvalue.is_modifiable() {
                    self.err(SemanticError::AssignmentToConst, typed_expr.span());
                }
                let ty = lvalue.ty().clone();
                TypedExpr::PostDecrement(Box::new(lvalue), SourceSpan::default(), ty)
            }
            _ => todo!("This expression is not supported yet"),
        }
    }

    fn convert_initializer_to_typed(&mut self, initializer: Initializer) -> TypedInitializer {
        match initializer {
            Initializer::Expr(expr) => {
                let typed_expr = self.check_expression(*expr);
                TypedInitializer::Expr(Box::new(typed_expr))
            }
            Initializer::List(list) => {
                let typed_list = list
                    .into_iter()
                    .map(|(designators, initializer)| {
                        let typed_designators = designators
                            .into_iter()
                            .map(|d| match d {
                                Designator::Index(expr) => {
                                    TypedDesignator::Index(Box::new(self.check_expression(*expr)))
                                }
                                Designator::Member(name) => TypedDesignator::Member(name),
                            })
                            .collect();
                        let typed_initializer = self.convert_initializer_to_typed(*initializer);
                        (typed_designators, Box::new(typed_initializer))
                    })
                    .collect();
                TypedInitializer::List(typed_list)
            }
        }
    }

    /// Performs integer promotions on a type.
    #[allow(dead_code)]
    fn integer_promote(&self, ty: &Type) -> Type {
        match ty {
            Type::Bool(_)
            | Type::Char(_)
            | Type::UnsignedChar(_)
            | Type::Short(_)
            | Type::UnsignedShort(_) => Type::Int(SourceSpan::default()),
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
        if let Type::Double(span) = lhs_ty {
            return (Type::Double(*span), Type::Double(*span));
        }
        if let Type::Double(span) = rhs_ty {
            return (Type::Double(*span), Type::Double(*span));
        }

        // If one is float, convert both to float
        if let Type::Float(span) = lhs_ty {
            return (Type::Float(*span), Type::Float(*span));
        }
        if let Type::Float(span) = rhs_ty {
            return (Type::Float(*span), Type::Float(*span));
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
                (Type::UnsignedLongLong(span), _) => {
                    (Type::UnsignedLongLong(*span), Type::UnsignedLongLong(*span))
                }
                (_, Type::UnsignedLongLong(span)) => {
                    (Type::UnsignedLongLong(*span), Type::UnsignedLongLong(*span))
                }
                (Type::LongLong(span), _) => (Type::LongLong(*span), Type::LongLong(*span)),
                (_, Type::LongLong(span)) => (Type::LongLong(*span), Type::LongLong(*span)),
                (Type::UnsignedLong(span), _) => {
                    (Type::UnsignedLong(*span), Type::UnsignedLong(*span))
                }
                (_, Type::UnsignedLong(span)) => {
                    (Type::UnsignedLong(*span), Type::UnsignedLong(*span))
                }
                (Type::Long(span), _) => (Type::Long(*span), Type::Long(*span)),
                (_, Type::Long(span)) => (Type::Long(*span), Type::Long(*span)),
                (Type::UnsignedInt(span), _) => {
                    (Type::UnsignedInt(*span), Type::UnsignedInt(*span))
                }
                (_, Type::UnsignedInt(span)) => {
                    (Type::UnsignedInt(*span), Type::UnsignedInt(*span))
                }
                _ => (
                    Type::Int(SourceSpan::default()),
                    Type::Int(SourceSpan::default()),
                ),
            }
        }
    }
}

fn is_const_initializer(initializer: &TypedInitializer) -> bool {
    match initializer {
        TypedInitializer::Expr(expr) => is_const_expr(expr),
        TypedInitializer::List(list) => list
            .iter()
            .all(|(_, initializer)| is_const_initializer(initializer)),
    }
}

fn is_const_expr(expr: &TypedExpr) -> bool {
    match expr {
        // Numeric literals are always constant expressions
        TypedExpr::Number(_, _, _) => true,
        // String literals are constant expressions
        TypedExpr::String(_, _, _) => true,
        // Address-of expressions are constant if the operand is a valid constant
        TypedExpr::AddressOf(lvalue, _, _) => match lvalue.as_ref() {
            // Address of a variable or string literal is constant
            TypedLValue::Variable(_, _, _) | TypedLValue::String(_, _, _) => true,
            // Other lvalues (like dereferences) are not constant
            _ => false,
        },
        // For other expression types, we conservatively return false
        // This could be extended to support more complex constant expressions
        _ => false,
    }
}

impl SemanticAnalyzer {
    fn check_initializer(&mut self, initializer: &TypedInitializer, ty: &Type) {
        match initializer {
            TypedInitializer::Expr(expr) => {
                if expr.ty().is_aggregate() && !ty.is_aggregate() {
                    self.err(SemanticError::TypeMismatch, expr.span());
                }
            }
            TypedInitializer::List(list) => {
                let real_ty = self.resolve_type(ty);
                match real_ty {
                    Type::Struct(_, ref _members, _) => {
                        for (designators, init) in list {
                            if designators.is_empty() {
                                // Non-designated initializers will be checked based on order
                            } else {
                                let mut current_ty = real_ty.clone();
                                for designator in designators {
                                    match designator {
                                        TypedDesignator::Member(name) => {
                                            if let Some(member_ty) =
                                                self.find_member_recursively(&current_ty, name)
                                            {
                                                current_ty = member_ty;
                                            } else {
                                                self.err(
                                                    SemanticError::UndefinedMember(*name),
                                                    ty.span(),
                                                );
                                                return;
                                            }
                                        }
                                        _ => {
                                            self.err(SemanticError::TypeMismatch, ty.span());
                                            return;
                                        }
                                    }
                                }
                                self.check_initializer(init, &current_ty);
                            }
                        }
                    }
                    Type::Array(elem_ty, size, _) => {
                        for (designators, init) in list {
                            if designators.is_empty() {
                                self.check_initializer(init, &elem_ty);
                            } else {
                                for designator in designators {
                                    match designator {
                                        TypedDesignator::Index(expr) => {
                                            if let TypedExpr::Number(n, _, _) = **expr {
                                                if size > 0 && n as usize >= size {
                                                    self.err(
                                                        SemanticError::ArrayIndexOutOfBounds,
                                                        expr.span(),
                                                    );
                                                }
                                            } else {
                                                self.err(
                                                    SemanticError::NotAConstantExpression,
                                                    expr.span(),
                                                );
                                            }
                                        }
                                        _ => {
                                            self.err(SemanticError::TypeMismatch, ty.span());
                                        }
                                    }
                                }
                                self.check_initializer(init, &elem_ty);
                            }
                        }
                    }
                    _ => {
                        self.err(SemanticError::TypeMismatch, ty.span());
                    }
                }
            }
        }
    }
}
