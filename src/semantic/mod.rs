use crate::SourceSpan;
use crate::parser::ast::{
    AssignOp, BinOp, Decl, Designator, Expr, ForInit, FuncDecl, Initializer, 
    Stmt, TranslationUnit,
};
use crate::parser::string_interner::StringInterner;
use crate::semantic::error::SemanticError;
use crate::types::{DeclId, TypeId, TypeKeywordMask, TypeKind, TypeQual, TypeSpec, TypeSpecKind};
use crate::parser::ast::Declarator;
use crate::parser::array_expr_interner::ArrayExprListInterner;
use std::collections::HashMap;
use thin_vec::ThinVec;
mod expressions;
use expressions::TypedExpression;
use std::collections::hash_map::Entry::Vacant;
use symbol_table::GlobalSymbol as StringId;
pub mod error;
pub mod typed_ast;
use crate::semantic::typed_ast::{TypedExpr, TypedLValue, TypedStmt, TypedInitializer, TypedDesignator, TypedForInit, TypedTranslationUnit, TypedFunctionDecl, TypedParameter, TypedVarDecl};

/// Converts a TypeSpec to a TypeId by building the corresponding TypeKind and interning it.
pub fn type_spec_to_type_id(type_spec: &TypeSpec, _span: SourceSpan) -> TypeId {
    let mut kind = match &type_spec.kind {
        TypeSpecKind::Builtin(mask) => {
            if mask.bits() == 0 {
                TypeKind::Int
            } else {
                // Determine the primary type based on the mask
                if mask.contains(TypeKeywordMask::VOID) {
                    TypeKind::Void
                } else if mask.contains(TypeKeywordMask::BOOL) {
                    TypeKind::Bool
                } else if mask.contains(TypeKeywordMask::CHAR) {
                    if mask.contains(TypeKeywordMask::UNSIGNED) {
                        TypeKind::UnsignedChar
                    } else {
                        TypeKind::Char
                    }
                } else if mask.contains(TypeKeywordMask::SHORT) {
                    if mask.contains(TypeKeywordMask::UNSIGNED) {
                        TypeKind::UnsignedShort
                    } else {
                        TypeKind::Short
                    }
                } else if mask.contains(TypeKeywordMask::INT) {
                    if mask.contains(TypeKeywordMask::UNSIGNED) {
                        TypeKind::UnsignedInt
                    } else {
                        TypeKind::Int
                    }
                } else if mask.contains(TypeKeywordMask::LONG) {
                    if mask.contains(TypeKeywordMask::LONGLONG) {
                        if mask.contains(TypeKeywordMask::UNSIGNED) {
                            TypeKind::UnsignedLongLong
                        } else {
                            TypeKind::LongLong
                        }
                    } else {
                        if mask.contains(TypeKeywordMask::UNSIGNED) {
                            TypeKind::UnsignedLong
                        } else {
                            TypeKind::Long
                        }
                    }
                } else if mask.contains(TypeKeywordMask::FLOAT) {
                    TypeKind::Float
                } else if mask.contains(TypeKeywordMask::DOUBLE) {
                    TypeKind::Double
                } else {
                    TypeKind::Int // Default fallback
                }
            }
        }
        TypeSpecKind::Struct(decl_id) => {
            // For struct types in TypeSpec, we don't have field information
            // Field information is handled separately via Decl::Struct
            TypeKind::Struct(Some(*decl_id), thin_vec::ThinVec::new())
        },
        TypeSpecKind::Union(decl_id) => {
            // For union types in TypeSpec, we don't have field information
            // Field information is handled separately via Decl::Union
            TypeKind::Union(Some(*decl_id), thin_vec::ThinVec::new())
        },
        TypeSpecKind::Enum(decl_id) => TypeKind::Enum {
            name: Some(*decl_id),
            underlying_type: TypeId::INT,
            variants: thin_vec::ThinVec::new(),
        },
        TypeSpecKind::Typedef(decl_id) => TypeKind::Typedef(*decl_id, TypeId::INT), // Fallback for typedef
    };

    // Apply array sizes
    if let Some(array_expr_list_id) = type_spec.array_exprs {
        let array_exprs = ArrayExprListInterner::get(array_expr_list_id);
        for array_size in array_exprs {
            if let Expr::Number(size, _) = array_size {
                if size > 0 {
                    kind = TypeKind::Array(TypeId::intern(&kind), size as usize);
                } else {
                    kind = TypeKind::Array(TypeId::intern(&kind), 0);
                }
            }
        }
    }

    // Apply pointers
    for _ in 0..type_spec.pointer_depth() {
        kind = TypeKind::Pointer(TypeId::intern(&kind));
    }

    // Apply qualifiers
    let mut flags = kind.flags();
    if type_spec.qualifiers().contains(TypeQual::CONST) {
        flags |= TypeId::FLAG_CONST;
    }
    if type_spec.qualifiers().contains(TypeQual::VOLATILE) {
        flags |= TypeId::FLAG_VOLATILE;
    }
    if type_spec.qualifiers().contains(TypeQual::RESTRICT) {
        flags |= TypeId::FLAG_RESTRICT;
    }
    if type_spec.qualifiers().contains(TypeQual::ATOMIC) {
        flags |= TypeId::FLAG_ATOMIC;
    }

    TypeId::intern_with_flags(&kind, flags)
}


/// Represents a symbol in the symbol table.
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct Symbol {
    pub ty: TypeId,
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
    pub fn lookup(&self, name: &StringId) -> Option<&Symbol> {
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
    pub symbol_table: SymbolTable,
    pub enum_constants: HashMap<StringId, i64>,
    struct_definitions: HashMap<DeclId, TypeId>,
    union_definitions: HashMap<DeclId, TypeId>,
    current_function: Option<StringId>,
    labels: HashMap<StringId, SourceSpan>,
    errors: Vec<(SemanticError, SourceSpan)>, // (error, file, span)
    warnings: Vec<(SemanticError, SourceSpan)>, // (warning, file, span)
    pub used_builtins: HashSet<StringId>,
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

    fn add_enum_variants_to_constants(&mut self, ty: TypeId, span: SourceSpan) {
        if let TypeKind::Enum { variants, .. } = ty.kind() {
            for variant in variants {
                if self.enum_constants.contains_key(&variant.name) {
                    self.err(
                        SemanticError::VariableRedeclaration(variant.name),
                        span,
                    );
                } else {
                    self.enum_constants.insert(variant.name, variant.value);
                }
            }
        }
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
        let builtins = vec![
            (
                "printf",
                TypeId::intern(&TypeKind::Function {
                    return_type: TypeId::INT,
                    params: vec![TypeId::const_pointer_to(TypeId::CHAR)],
                    is_variadic: true,
                }),
            ),
            (
                "malloc",
                TypeId::intern(&TypeKind::Function {
                    return_type: TypeId::VOID_PTR,
                    params: vec![TypeId::INT],
                    is_variadic: false,
                }),
            ),
            (
                "free",
                TypeId::intern(&TypeKind::Function {
                    return_type: TypeId::VOID,
                    params: vec![TypeId::VOID_PTR],
                    is_variadic: false,
                }),
            ),
            (
                "scanf",
                TypeId::intern(&TypeKind::Function {
                    return_type: TypeId::INT,
                    params: vec![TypeId::const_pointer_to(TypeId::CHAR)],
                    is_variadic: true,
                }),
            ),
            (
                "strcmp",
                TypeId::intern(&TypeKind::Function {
                    return_type: TypeId::INT,
                    params: vec![
                        TypeId::const_pointer_to(TypeId::CHAR),
                        TypeId::const_pointer_to(TypeId::CHAR),
                    ],
                    is_variadic: false,
                }),
            ),
            (
                "memcpy",
                TypeId::intern(&TypeKind::Function {
                    return_type: TypeId::VOID_PTR,
                    params: vec![
                        TypeId::pointer_to(TypeId::VOID),
                        TypeId::const_pointer_to(TypeId::VOID),
                        TypeId::INT,
                    ],
                    is_variadic: false,
                }),
            ),
        ];

        for (name, ty) in builtins {
            self.symbol_table.insert(
                StringInterner::intern(name),
                Symbol {
                    ty,
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

    fn find_member_recursively(&self, ty: TypeId, member_name: StringId) -> Option<TypeId> {
        let resolved_ty = self.resolve_type(ty);
        let binding = resolved_ty.kind();
        let members = match &binding {
            crate::types::TypeKind::Struct(_, members)
            | crate::types::TypeKind::Union(_, members) => members,
            _ => return None,
        };

        // 1. Search direct members
        if let Some(member) = members.iter().find(|p| p.name == member_name) {
            return Some(member.ty);
        }

        // 2. Search anonymous members
        let empty_name = StringInterner::intern("");
        for member in members {
            if member.name == empty_name
                && let crate::types::TypeKind::Struct(_, _) | crate::types::TypeKind::Union(_, _) =
                    &member.ty.kind()
                && let Some(found_ty) = self.find_member_recursively(member.ty, member_name)
            {
                return Some(found_ty);
            }
        }
        None
    }

    fn resolve_type(&self, ty: TypeId) -> TypeId {
        // For now, just return the type as-is since TypeId handles canonicalization
        ty
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

        // DEBUG: Print symbol table after semantic analysis
        println!("DEBUG_SEMANTIC: Symbol table after semantic analysis: {:?}", self.symbol_table);

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
                Decl::Func(FuncDecl {
                    return_type,
                    name,
                    params,
                    is_variadic,
                    ..
                }) => {
                    let span = return_type.span();
                    if let Some(existing) = self.symbol_table.lookup(name) {
                        if existing.is_function {
                            self.err(SemanticError::FunctionRedeclaration(*name), span);
                        }
                    } else {
                        let return_ty = type_spec_to_type_id(return_type, span);
                        let param_types = params
                            .iter()
                            .map(|p| type_spec_to_type_id(&p.type_spec, p.span))
                            .collect();
                        let ty = TypeId::intern(&TypeKind::Function {
                            return_type: return_ty,
                            params: param_types,
                            is_variadic: *is_variadic,
                        });
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
                Decl::VarGroup(type_spec, declarators) => {
                    for declarator in declarators {
                        let name = declarator.name.unwrap_or_else(|| StringInterner::intern(""));
                        let ty = self.apply_declarator(type_spec, declarator);
                        let span = declarator.span;

                        if ty.kind().is_enum() {
                            self.add_enum_variants_to_constants(ty, span);
                        } else if let TypeKind::Struct(Some(decl_id), members) = &ty.kind() {
                            if !members.is_empty() || !self.struct_definitions.contains_key(decl_id) {
                                self.struct_definitions.insert(*decl_id, ty);
                            }
                        } else if let TypeKind::Union(Some(decl_id), members) = &ty.kind()
                            && (!members.is_empty() || !self.union_definitions.contains_key(decl_id))
                        {
                            self.union_definitions.insert(*decl_id, ty);
                        }

                        // Global variables can be redeclared (tentative definitions)
                        // Only check for conflicts with functions
                        if let Some(existing) = self.symbol_table.lookup(&name) {
                            if existing.is_function {
                                self.err(SemanticError::VariableRedeclaration(name), span);
                            }
                        } else {
                            self.symbol_table.insert(
                                name,
                                Symbol {
                                    ty,
                                    is_function: false,
                                    span,
                                    is_builtin: false,
                                },
                            );
                        }
                    }
                }
                Decl::Struct(_)
                | Decl::Union(_)
                | Decl::Enum(_)
                | Decl::Typedef{..}
                | Decl::StaticAssert(_, _) => {
                    // Handle struct/union/enum declarations, typedefs, and static asserts
                    // For now, just collect struct/union/enum definitions
                    let converted_ty = match global {
                        Decl::Struct(struct_decl) => {
                            if !struct_decl.fields.is_empty() {
                                let ty = TypeKind::Struct(
                                    struct_decl.id,
                                    ThinVec::new(),
                                );
                                TypeId::intern(&ty)
                            } else {
                                return;
                            }
                        }
                        Decl::Union(union_decl) => {
                            if !union_decl.fields.is_empty() {
                                let ty = TypeKind::Union(
                                    union_decl.id,
                                    ThinVec::new(),
                                );
                                TypeId::intern(&ty)
                            } else {
                                return;
                            }
                        }
                        Decl::Enum(enum_decl) => {
                            if !enum_decl.members.is_empty() {
                                let mut next_value = 0;
                                let mut variants = ThinVec::new();
                                for member in &enum_decl.members {
                                    let val = if let Some(ref expr) = member.value {
                                        if let Expr::Number(num, _) = **expr {
                                            num
                                        } else {
                                            self.err(
                                                SemanticError::InvalidEnumInitializer(member.name),
                                                member.span,
                                            );
                                            -1 // Dummy value
                                        }
                                    } else {
                                        next_value
                                    };
                                    variants.push(crate::types::EnumVariant {
                                        name: member.name,
                                        value: val,
                                    });
                                    next_value = val + 1;
                                }
                                let ty = TypeKind::Enum {
                                    name: enum_decl.id,
                                    underlying_type: TypeId::INT,
                                    variants,
                                };
                                let enum_ty_id = TypeId::intern(&ty);
                                self.add_enum_variants_to_constants(enum_ty_id, enum_decl.span);
                                enum_ty_id
                            } else {
                                return;
                            }
                        }
                        Decl::Typedef { name: _, ty: _, id: _ } => {
                            // Handle typedef - typedefs are handled in the parser, no action needed here
                            return;
                        }
                        Decl::StaticAssert(expr, message) => {
                            // Evaluate static assert - should be a constant expression
                            let typed_expr = self.check_expression(*expr.clone());
                            
                            // Check if it's a constant expression and if it evaluates to non-zero
                            if let TypedExpr::Number(val, _, _) = typed_expr {
                                if val == 0 {
                                    self.err(
                                        SemanticError::StaticAssertFailed(*message),
                                        typed_expr.span(),
                                    );
                                }
                            } else {
                                // For non-constant expressions, we can't evaluate at compile time
                                // This should be a semantic error, but for now we'll report as invalid
                                self.err(
                                    SemanticError::NotAConstantExpression,
                                    typed_expr.span(),
                                );
                            }
                            return;
                        }
                        _ => return,
                    };

                    if let TypeKind::Struct(name, _) = &converted_ty.kind() {
                        if let Some(name_id) = name {
                            self.struct_definitions.insert(name_id.clone(), converted_ty);
                        }
                    } else if let TypeKind::Union(name, _) =
                        &converted_ty.kind()
                    {
                        if let Some(name_id) = name {
                            self.union_definitions.insert(name_id.clone(), converted_ty);
                        }
                    }
                }
                _ => {}
            }
        }
    }

    /// Second pass: check all statements and expressions for semantic correctness and build typed AST.
    fn check_program(&mut self, program: TranslationUnit) -> TypedTranslationUnit {
        let mut typed_globals = ThinVec::new();
        for global in &program.globals {
            match global {
                Decl::Func(func_decl) => {
                    self.current_function = Some(func_decl.name);
                    let typed_func = self.check_function(func_decl.clone());
                    typed_globals.push(typed_ast::TypedGlobalDecl::Function(typed_func));
                }
                Decl::VarGroup(type_spec, declarators) => {
                    let mut typed_vars = ThinVec::new();
                    for declarator in declarators {
                        let name = declarator.name.unwrap();
                        let ty = self.apply_declarator(type_spec, declarator);
                        let typed_init = declarator.init.as_ref().map(|init| {
                            self.convert_initializer_to_typed(Initializer::Expr(init.clone()))
                        });

                        typed_vars.push(TypedVarDecl {
                            name,
                            ty,
                            initializer: typed_init,
                        });
                    }
                    typed_globals.push(typed_ast::TypedGlobalDecl::Variable(typed_vars));
                }
                _ => {}
            }
        }

        TypedTranslationUnit {
            globals: typed_globals,
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
    fn check_function(&mut self, function: FuncDecl) -> TypedFunctionDecl {
        // Push function scope
        self.symbol_table.push_scope();

        // Clear labels for this function
        self.labels.clear();

        // First pass: collect all labels in the function
        if let Some(body) = &function.body {
            self.collect_labels(body);
        }

        // Check parameters for redeclaration and convert to TypedParameter
        let mut param_names = std::collections::HashSet::new();
        let mut typed_params = ThinVec::new();
        for param in &function.params {
            if !param_names.insert(param.name) {
                self.err(SemanticError::VariableRedeclaration(param.name), param.span);
            }
            // Convert TypeSpec to Type and create TypedParameter
            let ty = type_spec_to_type_id(&param.type_spec, param.span);
            let typed_param = TypedParameter {
                ty: ty,
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
        if let Some(body) = &function.body {
            for stmt in body {
                typed_body.push(self.check_statement(stmt.clone()));
            }
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

        let return_type = type_spec_to_type_id(&function.return_type, SourceSpan::default());
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
                            let ty = type_spec_to_type_id(&type_spec, SourceSpan::default());
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
                        let ty = type_spec_to_type_id(&type_spec, SourceSpan::default());
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
            Stmt::Declaration(decl) => {
                match decl {
                    Decl::VarGroup(type_spec, declarators) => {
                        let mut typed_declarators = ThinVec::new();
                        for declarator in declarators {
                            let name = declarator.name.unwrap_or_else(|| StringInterner::intern(""));
                            let full_ty = self.apply_declarator(&type_spec, &declarator);
                            
                            // Check for redeclaration before adding to symbol table
                            if let Some(existing) = self.symbol_table.lookup(&name) {
                                self.err(SemanticError::VariableRedeclaration(name), declarator.span);
                            } else {
                                // Register variable in symbol table with proper type and qualifiers
                                self.symbol_table.insert(
                                    name,
                                    Symbol {
                                        ty: full_ty,
                                        is_function: false,
                                        span: declarator.span,
                                        is_builtin: false,
                                    },
                                );
                            }
                            
                            // Add enum variants to constants if the type is an enum
                            if full_ty.kind().is_enum() {
                                self.add_enum_variants_to_constants(full_ty, declarator.span);
                            }

                            let typed_initializer = declarator
                                .init.as_ref()
                                .as_ref()
                                .map(|init| self.convert_initializer_to_typed(Initializer::Expr((**init).clone())));
                            typed_declarators.push(TypedVarDecl {
                                ty: full_ty,
                                name: name,
                                initializer: typed_initializer,
                            });
                        }
                        TypedStmt::Declaration(typed_declarators)
                    }
                    Decl::StaticAssert(expr, message) => {
                        // Evaluate static assert within function scope
                        let typed_expr = self.check_expression(*expr.clone());
                        if let TypedExpr::Number(val, _, _) = typed_expr {
                            if val == 0 {
                                self.err(
                                    SemanticError::StaticAssertFailed(message),
                                    typed_expr.span(),
                                );
                            }
                        } else {
                            self.err(
                                SemanticError::NotAConstantExpression,
                                typed_expr.span(),
                            );
                        }
                        TypedStmt::Empty // StaticAssert doesn't produce runtime code
                    }
                    _ => TypedStmt::Empty, // Handle other decl types if needed
                }
            }
        }
    }

    /// Checks a binary expression for semantic errors and returns a typed expression.
    fn check_binary_expression(&mut self, op: BinOp, lhs: &Expr, rhs: &Expr) -> TypedExpr {
        let mut lhs_typed = self.check_expression(lhs.clone());
        if let TypeKind::Array(elem_ty, _) = lhs_typed.ty().kind() {
            lhs_typed = lhs_typed.implicit_cast(TypeId::pointer_to(elem_ty));
        }

        let mut rhs_typed = self.check_expression(rhs.clone());
        if let TypeKind::Array(elem_ty, _) = rhs_typed.ty().kind() {
            rhs_typed = rhs_typed.implicit_cast(TypeId::pointer_to(elem_ty));
        }

        let lhs_ty = lhs_typed.ty();
        let rhs_ty = rhs_typed.ty();

        let (lhs_final, rhs_final, result_ty) = match op {
            BinOp::Add | BinOp::Sub => {
                if lhs_ty.is_pointer() || rhs_ty.is_pointer() {
                    // Pointer arithmetic
                    let result_ty = match (lhs_ty.unwrap_const(), rhs_ty.unwrap_const()) {
                        (a, b) if op == BinOp::Sub && a.is_pointer() && b.is_pointer() => {
                            TypeId::INT
                        }
                        (a, ty) if a.is_pointer() && ty.get_integer_rank() > 0 => lhs_ty.clone(),
                        (ty, b)
                            if b.is_pointer() && ty.get_integer_rank() > 0 && op == BinOp::Add =>
                        {
                            rhs_ty.clone()
                        }
                        _ => {
                            self.err(
                                SemanticError::TypeMismatch,
                                SourceSpan::default(), // Consider improving span info
                            );
                            TypeId::INT // dummy type
                        }
                    };
                    (lhs_typed, rhs_typed, result_ty)
                } else {
                    // Standard arithmetic
                    let (lhs_conv_ty, rhs_conv_ty) =
                        self.apply_usual_arithmetic_conversions(lhs_ty, rhs_ty);
                    let lhs_cast = lhs_typed.implicit_cast(lhs_conv_ty.clone());
                    let rhs_cast = rhs_typed.implicit_cast(rhs_conv_ty.clone());
                    (lhs_cast, rhs_cast, lhs_conv_ty)
                }
            }
            BinOp::Mul | BinOp::Div | BinOp::Mod => {
                let (lhs_conv_ty, rhs_conv_ty) =
                    self.apply_usual_arithmetic_conversions(lhs_ty, rhs_ty);
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
            | BinOp::GreaterThanOrEqual => (lhs_typed, rhs_typed, TypeId::intern(&TypeKind::Bool)),
            BinOp::LogicalAnd | BinOp::LogicalOr => {
                (lhs_typed, rhs_typed, TypeId::intern(&TypeKind::Bool))
            }
            BinOp::BitwiseOr | BinOp::BitwiseXor | BinOp::BitwiseAnd => {
                (lhs_typed, rhs_typed, TypeId::intern(&TypeKind::Int))
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
                    TypeId::INT,
                )
            }
        };

        if let TypedExpr::CompoundLiteral(_, _, _, ty) = &rhs_typed
            && let TypeKind::Array(elem_ty, _) = ty.kind()
        {
            let pointer_ty = TypeId::pointer_to(elem_ty);
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
        } else if lhs_ty.unwrap_volatile().is_const() {
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
                    .map(|s| s.ty)
                    .unwrap_or(TypeId::INT);

                TypedExpr::Variable(name, location, ty)
            }
            Expr::Number(n, span) => TypedExpr::Number(n, span, TypeId::intern(&TypeKind::Int)),
            Expr::FloatNumber(n, span) => {
                TypedExpr::FloatNumber(n, span, TypeId::intern(&TypeKind::Double))
            }
            Expr::String(s, span) => {
                TypedExpr::String(s, span, TypeId::pointer_to(TypeId::intern(&TypeKind::Char)))
            }
            Expr::Char(c, span) => TypedExpr::Char(c, span, TypeId::intern(&TypeKind::Char)),
            Expr::Call(name, args, location) => {
                let return_ty = if let Some(symbol) = self.symbol_table.lookup(&name) {
                    if symbol.is_builtin {
                        self.used_builtins.insert(name);
                    }
                    if !symbol.is_function {
                        self.err(SemanticError::NotAFunction(name), location);
                        TypeId::INT // dummy
                    } else if let TypeKind::Function { return_type, .. } = symbol.ty.kind() {
                        return_type
                    } else {
                        TypeId::INT // dummy
                    }
                } else {
                    self.err(SemanticError::UndefinedFunction(name), location);
                    TypeId::INT // dummy
                };

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
                TypedExpr::LogicalNot(Box::new(typed), SourceSpan::default(), TypeId::BOOL)
            }
            Expr::BitwiseNot(expr) => {
                let typed = self.check_expression(*expr);
                TypedExpr::BitwiseNot(Box::new(typed.clone()), SourceSpan::default(), typed.ty())
            }
            Expr::Sizeof(expr) => {
                let _typed = self.check_expression(*expr);
                TypedExpr::Sizeof(Box::new(_typed), SourceSpan::default(), TypeId::INT)
            }
            Expr::Alignof(expr) => {
                let _typed = self.check_expression(*expr);
                TypedExpr::Alignof(Box::new(_typed), SourceSpan::default(), TypeId::INT)
            }
            Expr::Deref(expr) => {
                let typed = self.check_expression(*expr);
                let result_ty = match typed.ty().unwrap_const().kind() {
                    TypeKind::Pointer(base_ty) => base_ty,
                    TypeKind::Array(elem_ty, _) => elem_ty,
                    other_ty => {
                        self.err(SemanticError::NotAPointer(TypeId::intern(&other_ty)), typed.span());
                        TypeId::INT
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
                            TypeId::intern(&TypeKind::Int),
                        )
                    }
                };
                let ty = lvalue.ty();
                TypedExpr::AddressOf(
                    Box::new(lvalue),
                    SourceSpan::default(),
                    TypeId::intern(&TypeKind::Pointer(ty)),
                )
            }
            Expr::SizeofType(ty) => {
                let converted_ty = type_spec_to_type_id(&ty, SourceSpan::default());
                TypedExpr::SizeofType(
                    converted_ty,
                    SourceSpan::default(),
                    TypeId::intern(&TypeKind::Int),
                )
            }
            Expr::AlignofType(ty) => {
                let converted_ty = type_spec_to_type_id(&ty, SourceSpan::default());
                TypedExpr::AlignofType(
                    converted_ty,
                    SourceSpan::default(),
                    TypeId::intern(&TypeKind::Int),
                )
            }
            Expr::Ternary(cond, then_expr, else_expr) => {
                let cond_typed = self.check_expression(*cond);
                let then_typed = self.check_expression(*then_expr);
                let else_typed = self.check_expression(*else_expr);
                let result_ty = if then_typed.ty() == else_typed.ty() {
                    then_typed.ty()
                } else {
                    TypeId::INT
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
                    .find_member_recursively(typed.ty(), member)
                    .unwrap_or_else(|| {
                        self.err(SemanticError::UndefinedMember(member), typed.span());
                        TypeId::INT // Dummy type
                    });
                TypedExpr::Member(
                    Box::new(typed),
                    member,
                    SourceSpan::default(),
                    member_ty,
                )
            }
            Expr::PointerMember(expr, member) => {
                let typed_ptr = self.check_expression(*expr);

                let inner_ty = if let TypeKind::Pointer(inner) =
                    typed_ptr.ty().clone().unwrap_const().kind()
                {
                    inner
                } else {
                    self.err(
                        SemanticError::NotAPointer(typed_ptr.ty().clone()),
                        typed_ptr.span(),
                    );
                    return TypedExpr::Number(
                        0,
                        SourceSpan::default(),
                        TypeId::INT,
                    );
                };

                let deref_expr =
                    TypedExpr::Deref(Box::new(typed_ptr), SourceSpan::default(), inner_ty);

                let member_ty = self
                    .find_member_recursively(deref_expr.ty(), member)
                    .unwrap_or_else(|| {
                        self.err(SemanticError::UndefinedMember(member), deref_expr.span());
                        TypeId::INT
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
                    TypeId::INT,
                )
            }
            Expr::ExplicitCast(ty, expr) => {
                let typed_expr = self.check_expression(*expr);
                let converted_ty = type_spec_to_type_id(&ty, SourceSpan::default());
                TypedExpr::ExplicitCast(
                    converted_ty,
                    Box::new(typed_expr),
                    SourceSpan::default(),
                    converted_ty,
                )
            }
            Expr::ImplicitCast(ty, expr) => {
                let typed_expr = self.check_expression(*expr);
                let converted_ty = type_spec_to_type_id(&ty, SourceSpan::default());
                TypedExpr::ImplicitCast(
                    converted_ty,
                    Box::new(typed_expr),
                    SourceSpan::default(),
                    converted_ty,
                )
            }
            Expr::CompoundLiteral(ty, initializer) => {
                let typed_initializer = self.convert_initializer_to_typed(*initializer);
                let mut final_ty = type_spec_to_type_id(&ty, SourceSpan::default());
                if let TypeKind::Array(elem_ty, 0) = final_ty.kind()
                    && let TypedInitializer::List(list) = &typed_initializer
                {
                    final_ty = TypeId::intern(&TypeKind::Array(elem_ty, list.len()));
                }
                let converted_ty = type_spec_to_type_id(&ty, SourceSpan::default());
                let mut typed_expr = TypedExpr::CompoundLiteral(
                    converted_ty,
                    Box::new(typed_initializer),
                    SourceSpan::default(),
                    final_ty,
                );

                if let TypeKind::Array(elem_ty, _) = final_ty.kind() {
                    typed_expr = typed_expr.implicit_cast(TypeId::intern(&TypeKind::Pointer(elem_ty)));
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
                            TypeId::intern(&TypeKind::Int),
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
                            TypeId::intern(&TypeKind::Int),
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
                            TypeId::intern(&TypeKind::Int),
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
                            TypeId::intern(&TypeKind::Int),
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

    // /// Performs integer promotions on a type.
    // #[allow(dead_code)]
    // fn integer_promote(&self, ty: &Type) -> Type {
    //     match ty {
    //         TypeId::intern(&TypeKind::Bool)(_)
    //         | Type::Char(_)
    //         | Type::UnsignedChar(_)
    //         | Type::Short(_)
    //         | Type::UnsignedShort(_) => TypeId::intern(&TypeKind::Int),
    //         _ => ty.clone(),
    //     }
    // }

    /// Applies usual arithmetic conversions to two types.
    fn apply_usual_arithmetic_conversions(
        &self,
        lhs_ty: TypeId,
        rhs_ty: TypeId,
    ) -> (TypeId, TypeId) {
        // If both types are the same, no conversion needed
        if lhs_ty == rhs_ty {
            return (lhs_ty.clone(), rhs_ty.clone());
        }

        // If one is long double, convert both to long double
        // But we don't have long double, so skip

        // If one is double, convert both to double
        if lhs_ty == TypeId::DOUBLE {
            return (TypeId::DOUBLE, TypeId::DOUBLE);
        }
        if rhs_ty == TypeId::DOUBLE {
            return (TypeId::DOUBLE, TypeId::DOUBLE);
        }

        // If one is float, convert both to float
        if lhs_ty == TypeId::FLOAT {
            return (TypeId::FLOAT, TypeId::FLOAT);
        }
        if rhs_ty == TypeId::FLOAT {
            return (TypeId::FLOAT, TypeId::FLOAT);
        }

        // Both are integer types, apply integer conversion rules
        let lhs_rank = lhs_ty.kind().get_integer_rank();
        let rhs_rank = rhs_ty.kind().get_integer_rank();

        if lhs_rank > rhs_rank {
            (lhs_ty.clone(), lhs_ty.clone())
        } else if rhs_rank > lhs_rank {
            (rhs_ty.clone(), rhs_ty.clone())
        } else {
            // Same rank, check signedness
            match (lhs_ty.kind(), rhs_ty.kind()) {
                (TypeKind::UnsignedLongLong, _) => (
                    TypeId::intern(&TypeKind::UnsignedLongLong),
                    TypeId::intern(&TypeKind::UnsignedLongLong),
                ),
                (_, TypeKind::UnsignedLongLong) => (
                    TypeId::intern(&TypeKind::UnsignedLongLong),
                    TypeId::intern(&TypeKind::UnsignedLongLong),
                ),
                (TypeKind::Long, _) => (
                    TypeId::intern(&TypeKind::Long),
                    TypeId::intern(&TypeKind::Long),
                ),
                (_, TypeKind::Long) => (
                    TypeId::intern(&TypeKind::Long),
                    TypeId::intern(&TypeKind::Long),
                ),
                (TypeKind::UnsignedLong, _) => (
                    TypeId::intern(&TypeKind::UnsignedLong),
                    TypeId::intern(&TypeKind::UnsignedLong),
                ),
                (_, TypeKind::UnsignedLong) => (
                    TypeId::intern(&TypeKind::UnsignedLong),
                    TypeId::intern(&TypeKind::UnsignedLong),
                ),
                (TypeKind::UnsignedInt, _) => (
                    TypeId::intern(&TypeKind::UnsignedInt),
                    TypeId::intern(&TypeKind::UnsignedInt),
                ),
                (_, TypeKind::UnsignedInt) => (
                    TypeId::intern(&TypeKind::UnsignedInt),
                    TypeId::intern(&TypeKind::UnsignedInt),
                ),
                _ => (
                    TypeId::intern(&TypeKind::Int),
                    TypeId::intern(&TypeKind::Int),
                ),
            }
        }
    }

    /// Applies declarator to a TypeSpec to produce a TypeId.
    fn apply_declarator(&self, spec: &TypeSpec, decl: &Declarator) -> TypeId {
        let mut base_ty = type_spec_to_type_id(spec, SourceSpan::default());

        // Apply declarator's pointers
        for _ in 0..decl.pointer_depth {
            base_ty = TypeId::intern(&TypeKind::Pointer(base_ty));
        }

        // Apply declarator's qualifiers to the base type
        let mut flags = base_ty.flags();
        if TypeQual::from_bits_truncate(decl.qualifiers as u8).contains(TypeQual::CONST) {
            flags |= TypeId::FLAG_CONST;
        }
        if TypeQual::from_bits_truncate(decl.qualifiers as u8).contains(TypeQual::VOLATILE) {
            flags |= TypeId::FLAG_VOLATILE;
        }
        if TypeQual::from_bits_truncate(decl.qualifiers as u8).contains(TypeQual::RESTRICT) {
            flags |= TypeId::FLAG_RESTRICT;
        }
        if TypeQual::from_bits_truncate(decl.qualifiers as u8).contains(TypeQual::ATOMIC) {
            flags |= TypeId::FLAG_ATOMIC;
        }
        base_ty = TypeId::intern_with_flags(&base_ty.kind(), flags);

        // Apply declarator's array sizes
        for array_size in &decl.array_sizes {
            if let Expr::Number(size, _) = array_size {
                if *size > 0 {
                    base_ty = TypeId::intern(&TypeKind::Array(base_ty, *size as usize));
                } else {
                    base_ty = TypeId::intern(&TypeKind::Array(base_ty, 0));
                }
            }
        }

        // For function declarators, we might need to handle function types, but for now, just return the base_ty
        // as function types are handled separately in the symbol table.

        base_ty
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
    fn check_initializer(&mut self, initializer: &TypedInitializer, ty: TypeId) {
        match initializer {
            TypedInitializer::Expr(expr) => {
                if expr.ty().is_aggregate() && !ty.is_aggregate() {
                    self.err(SemanticError::TypeMismatch, expr.span());
                }
            }
            TypedInitializer::List(list) => {
                let real_ty = self.resolve_type(ty);
                let real_ty_kind = real_ty.kind();
                match real_ty_kind {
                    TypeKind::Struct(_, ref _members) => {
                        for (designators, init) in list {
                            if designators.is_empty() {
                                // Non-designated initializers will be checked based on order
                            } else {
                                let mut current_offset = 0;
                                let mut current_ty = real_ty;
                                for designator in designators {
                                    match designator {
                                        TypedDesignator::Member(name) => {
                                            if let Some(member_ty) =
                                                self.find_member_recursively(current_ty, *name)
                                            {
                                                current_ty = member_ty;
                                            } else {
                                                self.err(
                                                    SemanticError::UndefinedMember(*name),
                                                    SourceSpan::default(),
                                                );
                                                return;
                                            }
                                        }
                                        _ => {
                                            self.err(
                                                SemanticError::TypeMismatch,
                                                SourceSpan::default(),
                                            );
                                            return;
                                        }
                                    }
                                }
                                self.check_initializer(init, current_ty);
                            }
                        }
                    }
                    TypeKind::Array(elem_ty, size) => {
                        for (designators, init) in list {
                            if designators.is_empty() {
                                self.check_initializer(init, elem_ty);
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
                                            self.err(
                                                SemanticError::TypeMismatch,
                                                SourceSpan::default(),
                                            );
                                        }
                                    }
                                }
                                self.check_initializer(init, elem_ty);
                            }
                        }
                    }
                    _ => {
                        self.err(SemanticError::TypeMismatch, SourceSpan::default());
                    }
                }
            }
        }
    }
}
