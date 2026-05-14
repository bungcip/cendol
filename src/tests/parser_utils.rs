use crate::ast::literal::LitVal;
use crate::ast::{BinaryOp, ParsedBaseType, ParsedBaseTypeRef, UnaryOp};
use crate::ast::{DeclSpec, DeclaratorRef, ParsedAst, ParsedDeclarator, ParsedNodeKind, ParsedNodeRef, TypeSpec};
use crate::driver::CompilerDriver;
use crate::driver::artifact::CompilePhase;
use crate::driver::cli::CompileConfig;
use crate::lang_options::CStandard;
use crate::parser::statements::parse_compound_statement;
use crate::parser::{BindingPower, Lexer, ParseError, Parser, declarations, statements};
use crate::pp::Preprocessor;
use crate::source_manager::FileKind;
use crate::tests::test_utils::setup_sm_and_de;
use serde::Serialize;

/// Resolved AST node kind for testing - replaces NodeRef with actual content
#[derive(Debug, Serialize)]
pub(crate) enum ResolvedNodeKind {
    LiteralInt(i64),
    LiteralFloat(f64),
    LiteralString(String),
    LiteralChar(u64, crate::ast::literal::CharPrefix),
    LiteralNullptr,
    LiteralTrue,
    LiteralFalse,
    Ident(String),
    UnaryOp(UnaryOp, Box<ResolvedNodeKind>),
    BinaryOp(BinaryOp, Box<ResolvedNodeKind>, Box<ResolvedNodeKind>),
    TernaryOp(Box<ResolvedNodeKind>, Box<ResolvedNodeKind>, Box<ResolvedNodeKind>),
    PostIncrement(Box<ResolvedNodeKind>),
    PostDecrement(Box<ResolvedNodeKind>),
    Assignment(BinaryOp, Box<ResolvedNodeKind>, Box<ResolvedNodeKind>),
    FunctionCall(Box<ResolvedNodeKind>, Vec<ResolvedNodeKind>),
    MemberAccess(Box<ResolvedNodeKind>, String, bool),
    IndexAccess(Box<ResolvedNodeKind>, Box<ResolvedNodeKind>),
    Cast(String, Box<ResolvedNodeKind>), // Simplified: just type name
    SizeOfExpr(Box<ResolvedNodeKind>),
    SizeOfType(String),  // Simplified: just type name
    AlignOfType(String), // Simplified: just type name
    AlignOfExpr(Box<ResolvedNodeKind>),
    Declaration {
        specifiers: Vec<String>,
        init_declarators: Vec<ResolvedInitDeclarator>,
    }, // Simplified declaration
    EnumConstant(String, Option<Box<ResolvedNodeKind>>),
    InitializerList(Vec<ResolvedNodeKind>), // For initializer lists like {1, 2, 3}
    ExpressionStatement(Option<Box<ResolvedNodeKind>>), // Expression statement
    CompoundStatement(Vec<ResolvedNodeKind>), // Compound statement { ... }
    GnuStatementExpression(Box<ResolvedNodeKind>, Box<ResolvedNodeKind>), // GNU statement expression ({ ... })
    GenericSelection(Box<ResolvedNodeKind>, Vec<ResolvedGenericAssociation>), // _Generic selection
    Label(String, Box<ResolvedNodeKind>),   // Label statement (label: statement)
    Goto(String),                           // Goto statement
    Return(Option<Box<ResolvedNodeKind>>),  // Return statement
    Break,                                  // Break statement
    Continue,                               // Continue statement
    Switch(Box<ResolvedNodeKind>, Box<ResolvedNodeKind>),
    Case(Box<ResolvedNodeKind>, Box<ResolvedNodeKind>), // Case statement
    CaseRange(Box<ResolvedNodeKind>, Box<ResolvedNodeKind>, Box<ResolvedNodeKind>), // GNU Case range statement
    Default(Box<ResolvedNodeKind>),                     // Default statement
    If(
        Box<ResolvedNodeKind>,
        Box<ResolvedNodeKind>,
        Option<Box<ResolvedNodeKind>>,
    ), // If statement
    While(Box<ResolvedNodeKind>, Box<ResolvedNodeKind>), // While statement
    DoWhile(Box<ResolvedNodeKind>, Box<ResolvedNodeKind>), // Do-while statement
    For(
        Option<Box<ResolvedNodeKind>>,
        Option<Box<ResolvedNodeKind>>,
        Option<Box<ResolvedNodeKind>>,
        Box<ResolvedNodeKind>,
    ), // For statement
    StaticAssert(Box<ResolvedNodeKind>, Option<String>),
    CompoundLiteral(String, Box<ResolvedNodeKind>),
    FunctionDef {
        specifiers: Vec<String>,
        declarator: Box<ResolvedInitDeclarator>,
        body: Box<ResolvedNodeKind>,
    },
    TranslationUnit(Vec<ResolvedNodeKind>),
    Empty, // Empty statement
           // Add more as needed for tests
}

/// Simplified resolved generic association for testing
#[derive(Debug, Serialize)]
pub(crate) struct ResolvedGenericAssociation {
    type_name: Option<String>, // None for 'default:'
    result_expr: ResolvedNodeKind,
}

/// Simplified resolved init declarator for testing
#[derive(Debug, Serialize)]
pub(crate) struct ResolvedInitDeclarator {
    name: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    kind: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    initializer: Option<ResolvedNodeKind>,
}

fn resolve_specs(ast: &ParsedAst, specifiers: &[DeclSpec]) -> Vec<String> {
    specifiers
        .iter()
        .map(|s| match s {
            DeclSpec::TypeSpec(ts) => match ts {
                TypeSpec::Void => "void".to_string(),
                TypeSpec::Bool => "_Bool".to_string(),
                TypeSpec::Char => "char".to_string(),
                TypeSpec::Short => "short".to_string(),
                TypeSpec::Int => "int".to_string(),
                TypeSpec::Long => "long".to_string(),
                TypeSpec::Float => "float".to_string(),
                TypeSpec::Double => "double".to_string(),
                TypeSpec::Signed => "signed".to_string(),
                TypeSpec::Unsigned => "unsigned".to_string(),
                TypeSpec::Complex => "_Complex".to_string(),
                TypeSpec::TypedefName(name) => format!("TypedefName({:?})", name.to_string()),
                TypeSpec::Enum(tag, enumerators, underlying_type) => {
                    let tag_str = tag.map(|t| t.to_string()).unwrap_or_else(|| "".to_string());
                    let mut s = format!("enum {}", tag_str);
                    if let Some(ut) = underlying_type {
                        s.push_str(" : ");
                        s.push_str(&extract_type_kind(ast, ut));
                    }
                    if let Some(enums) = enumerators {
                        let enum_parts: Vec<String> = enums
                            .iter()
                            .map(|&node| match &ast.get_node(node).kind {
                                ParsedNodeKind::EnumConstant(name, Some(value_expr)) => {
                                    let value = resolve_node(ast, *value_expr);
                                    match value {
                                        ResolvedNodeKind::LiteralInt(val) => format!("{} = {}", name, val),
                                        _ => format!("{} = <expr>", name),
                                    }
                                }
                                ParsedNodeKind::EnumConstant(name, None) => name.to_string(),
                                _ => "<invalid>".to_string(),
                            })
                            .collect();
                        s.push_str(&format!(" {{ {} }}", enum_parts.join(", ")));
                    }
                    s
                }
                TypeSpec::Record(is_union, tag, def, _) => {
                    let record_kind = if *is_union { "union" } else { "struct" };
                    let has_body = def.is_some();

                    let mut s = record_kind.to_string();
                    if let Some(tag) = tag {
                        s.push(' ');
                        s.push_str(tag.as_str());
                    }
                    if has_body {
                        s.push_str(" { ... }");
                    }
                    s
                }
                _ => format!("{:?}", ts),
            },
            DeclSpec::StorageClass(sc) => format!("{:?}", sc),
            DeclSpec::TypeQualifier(tq) => format!("TypeQualifier({:?})", tq),
            DeclSpec::FunctionSpec(fs) => format!("{:?}", fs),
            DeclSpec::AlignmentSpec(aspec) => format!("{:?}", aspec),
            DeclSpec::Attribute => "__attribute__".to_string(),
            DeclSpec::AttributePacked => "packed".to_string(),
        })
        .collect()
}

/// Resolve a ParsedNodeRef to a ResolvedNodeKind by recursively following references
pub(crate) fn resolve_node(ast: &ParsedAst, node: ParsedNodeRef) -> ResolvedNodeKind {
    let node = ast.get_node(node);
    match &node.kind {
        ParsedNodeKind::Literal(lit) => match lit.get_val() {
            LitVal::Int { value, .. } => ResolvedNodeKind::LiteralInt(value),
            lit @ LitVal::Float { .. } => ResolvedNodeKind::LiteralFloat(lit.as_f64()),
            LitVal::String { value, .. } => ResolvedNodeKind::LiteralString(value),
            LitVal::Char(c, prefix) => ResolvedNodeKind::LiteralChar(c as u64, prefix),
            LitVal::Nullptr => ResolvedNodeKind::LiteralNullptr,
            LitVal::True => ResolvedNodeKind::LiteralTrue,
            LitVal::False => ResolvedNodeKind::LiteralFalse,
        },
        ParsedNodeKind::Ident(symbol) => ResolvedNodeKind::Ident(symbol.to_string()),
        ParsedNodeKind::UnaryOp(op, operand) => ResolvedNodeKind::UnaryOp(*op, Box::new(resolve_node(ast, *operand))),
        ParsedNodeKind::BinaryOp(op, left, right) => ResolvedNodeKind::BinaryOp(
            *op,
            Box::new(resolve_node(ast, *left)),
            Box::new(resolve_node(ast, *right)),
        ),
        ParsedNodeKind::TernaryOp(cond, then_expr, else_expr) => ResolvedNodeKind::TernaryOp(
            Box::new(resolve_node(ast, *cond)),
            Box::new(resolve_node(ast, *then_expr)),
            Box::new(resolve_node(ast, *else_expr)),
        ),
        ParsedNodeKind::PostIncrement(operand) => {
            ResolvedNodeKind::PostIncrement(Box::new(resolve_node(ast, *operand)))
        }
        ParsedNodeKind::PostDecrement(operand) => {
            ResolvedNodeKind::PostDecrement(Box::new(resolve_node(ast, *operand)))
        }
        ParsedNodeKind::Assignment(op, lhs, rhs) => ResolvedNodeKind::Assignment(
            *op,
            Box::new(resolve_node(ast, *lhs)),
            Box::new(resolve_node(ast, *rhs)),
        ),
        ParsedNodeKind::FunctionCall(func, args) => ResolvedNodeKind::FunctionCall(
            Box::new(resolve_node(ast, *func)),
            args.iter().map(|&arg| resolve_node(ast, arg)).collect(),
        ),
        ParsedNodeKind::BuiltinChooseExpr(c, t, f) => ResolvedNodeKind::FunctionCall(
            Box::new(ResolvedNodeKind::Ident("__builtin_choose_expr".to_string())),
            vec![resolve_node(ast, *c), resolve_node(ast, *t), resolve_node(ast, *f)],
        ),
        ParsedNodeKind::BuiltinComplex(r, i) => ResolvedNodeKind::FunctionCall(
            Box::new(ResolvedNodeKind::Ident("__builtin_complex".to_string())),
            vec![resolve_node(ast, *r), resolve_node(ast, *i)],
        ),
        ParsedNodeKind::BuiltinTypesCompatibleP(boxed) => {
            let (t1, t2) = &**boxed;
            ResolvedNodeKind::FunctionCall(
                Box::new(ResolvedNodeKind::Ident("__builtin_types_compatible_p".to_string())),
                vec![
                    ResolvedNodeKind::Ident(format!("type_{}", t1.base.get())),
                    ResolvedNodeKind::Ident(format!("type_{}", t2.base.get())),
                ],
            )
        }
        ParsedNodeKind::BuiltinVaArg(ty, expr) => ResolvedNodeKind::FunctionCall(
            Box::new(ResolvedNodeKind::Ident("__builtin_va_arg".to_string())),
            vec![
                ResolvedNodeKind::Ident(format!("type_{}", ty.base.get())),
                resolve_node(ast, *expr),
            ],
        ),
        ParsedNodeKind::MemberAccess(object, field, is_arrow) => {
            ResolvedNodeKind::MemberAccess(Box::new(resolve_node(ast, *object)), field.to_string(), *is_arrow)
        }
        ParsedNodeKind::IndexAccess(array, index) => {
            ResolvedNodeKind::IndexAccess(Box::new(resolve_node(ast, *array)), Box::new(resolve_node(ast, *index)))
        }
        ParsedNodeKind::Cast(ty, expr) => {
            // For simplicity, just show a placeholder type name
            ResolvedNodeKind::Cast(
                format!("parsed_type_{}_{}", ty.base.get(), ty.declarator.get()),
                Box::new(resolve_node(ast, *expr)),
            )
        }
        ParsedNodeKind::SizeOfExpr(expr) => ResolvedNodeKind::SizeOfExpr(Box::new(resolve_node(ast, *expr))),
        ParsedNodeKind::SizeOfType(ty) => ResolvedNodeKind::SizeOfType(format!("type_{}", ty.base.get())),
        ParsedNodeKind::AlignOfType(ty) => ResolvedNodeKind::AlignOfType(format!("type_{}", ty.base.get())),
        ParsedNodeKind::AlignOfExpr(expr) => ResolvedNodeKind::AlignOfExpr(Box::new(resolve_node(ast, *expr))),
        ParsedNodeKind::Declaration(decl) => {
            let specifiers = resolve_specs(ast, &decl.specifiers);
            let init_declarators = decl
                .init_declarators
                .iter()
                .map(|init_decl| {
                    let name = extract_declarator_name(ast, init_decl.declarator);
                    let kind_str = extract_declarator_kind(ast, init_decl.declarator);
                    let kind = if kind_str == "identifier" { None } else { Some(kind_str) };
                    let initializer = init_decl
                        .initializer
                        .as_ref()
                        .map(|init| resolve_initializer(ast, *init));
                    ResolvedInitDeclarator {
                        name,
                        kind,
                        initializer,
                    }
                })
                .collect();
            ResolvedNodeKind::Declaration {
                specifiers,
                init_declarators,
            }
        }
        ParsedNodeKind::EnumConstant(name, value_expr) => ResolvedNodeKind::EnumConstant(
            name.to_string(),
            value_expr.map(|expr| Box::new(resolve_node(ast, expr))),
        ),
        ParsedNodeKind::ExpressionStmt(expr) => {
            ResolvedNodeKind::ExpressionStatement(expr.map(|e| Box::new(resolve_node(ast, e))))
        }
        ParsedNodeKind::CompoundStmt(statements) => {
            ResolvedNodeKind::CompoundStatement(statements.iter().map(|&stmt| resolve_node(ast, stmt)).collect())
        }
        ParsedNodeKind::GnuStatementExpr(compound_stmt, result_expr) => ResolvedNodeKind::GnuStatementExpression(
            Box::new(resolve_node(ast, *compound_stmt)),
            Box::new(resolve_node(ast, *result_expr)),
        ),
        ParsedNodeKind::GenericSelection(controlling_expr, associations) => {
            let resolved_controlling = Box::new(resolve_node(ast, *controlling_expr));
            let resolved_associations = associations
                .iter()
                .map(|assoc| {
                    let type_name = assoc.type_name.map(|ty| {
                        // For simplicity, just show a placeholder type name
                        // In a full implementation, we'd resolve the actual type
                        format!("type_{}", ty.base.get())
                    });
                    let result_expr = resolve_node(ast, assoc.result_expr);
                    ResolvedGenericAssociation { type_name, result_expr }
                })
                .collect();
            ResolvedNodeKind::GenericSelection(resolved_controlling, resolved_associations)
        }
        ParsedNodeKind::Label(label, statement) => {
            ResolvedNodeKind::Label(label.to_string(), Box::new(resolve_node(ast, *statement)))
        }
        ParsedNodeKind::Goto(label) => ResolvedNodeKind::Goto(label.to_string()),
        ParsedNodeKind::Return(expr) => ResolvedNodeKind::Return(expr.map(|e| Box::new(resolve_node(ast, e)))),
        ParsedNodeKind::Break => ResolvedNodeKind::Break,
        ParsedNodeKind::Continue => ResolvedNodeKind::Continue,
        ParsedNodeKind::Switch(condition, body) => ResolvedNodeKind::Switch(
            Box::new(resolve_node(ast, *condition)),
            Box::new(resolve_node(ast, *body)),
        ),
        ParsedNodeKind::Case(expr, statement) => ResolvedNodeKind::Case(
            Box::new(resolve_node(ast, *expr)),
            Box::new(resolve_node(ast, *statement)),
        ),
        ParsedNodeKind::CaseRange(start, end, statement) => ResolvedNodeKind::CaseRange(
            Box::new(resolve_node(ast, *start)),
            Box::new(resolve_node(ast, *end)),
            Box::new(resolve_node(ast, *statement)),
        ),
        ParsedNodeKind::Default(statement) => ResolvedNodeKind::Default(Box::new(resolve_node(ast, *statement))),
        ParsedNodeKind::If(if_stmt) => ResolvedNodeKind::If(
            Box::new(resolve_node(ast, if_stmt.condition)),
            Box::new(resolve_node(ast, if_stmt.then_branch)),
            if_stmt.else_branch.map(|br| Box::new(resolve_node(ast, br))),
        ),
        ParsedNodeKind::While(while_stmt) => ResolvedNodeKind::While(
            Box::new(resolve_node(ast, while_stmt.condition)),
            Box::new(resolve_node(ast, while_stmt.body)),
        ),
        ParsedNodeKind::DoWhile(body, condition) => ResolvedNodeKind::DoWhile(
            Box::new(resolve_node(ast, *body)),
            Box::new(resolve_node(ast, *condition)),
        ),
        ParsedNodeKind::For(for_stmt) => ResolvedNodeKind::For(
            for_stmt.init.map(|i| Box::new(resolve_node(ast, i))),
            for_stmt.condition.map(|c| Box::new(resolve_node(ast, c))),
            for_stmt.increment.map(|inc| Box::new(resolve_node(ast, inc))),
            Box::new(resolve_node(ast, for_stmt.body)),
        ),
        ParsedNodeKind::StaticAssert(expr, msg) => {
            let message = msg.map(|m| {
                if let ParsedNodeKind::Literal(lit) = &ast.get_node(m).kind {
                    if let LitVal::String { value, .. } = lit.get_val() {
                        value.clone()
                    } else {
                        "<invalid>".to_string()
                    }
                } else {
                    "<invalid>".to_string()
                }
            });
            ResolvedNodeKind::StaticAssert(Box::new(resolve_node(ast, *expr)), message)
        }
        ParsedNodeKind::CompoundLiteral(ty, init) => {
            // Check if init is an InitializerList, if so use resolve_initializer, otherwise resolve_node
            let init_node = ast.get_node(*init);
            let resolved_init = match init_node.kind {
                ParsedNodeKind::InitializerList(_) => resolve_initializer(ast, *init),
                _ => resolve_node(ast, *init),
            };
            ResolvedNodeKind::CompoundLiteral(
                format!("parsed_type_{}", ty.base.get()), // Simplified type
                Box::new(resolved_init),
            )
        }
        ParsedNodeKind::TranslationUnit(nodes) => {
            ResolvedNodeKind::TranslationUnit(nodes.iter().map(|&n| resolve_node(ast, n)).collect())
        }
        ParsedNodeKind::FunctionDef(def) => {
            let specifiers = resolve_specs(ast, &def.specifiers);
            let name = extract_declarator_name(ast, def.declarator);
            let kind_str = extract_declarator_kind(ast, def.declarator);
            let kind = if kind_str == "identifier" { None } else { Some(kind_str) };

            let resolved_declarator = ResolvedInitDeclarator {
                name,
                kind,
                initializer: None,
            };

            ResolvedNodeKind::FunctionDef {
                specifiers,
                declarator: Box::new(resolved_declarator),
                body: Box::new(resolve_node(ast, def.body)),
            }
        }
        ParsedNodeKind::EmptyStmt | ParsedNodeKind::Dummy => ResolvedNodeKind::Empty,
        // Add more cases as needed for other ParsedNodeKind variants used in tests
        _ => panic!("Unsupported ParsedNodeKind for resolution: {:?}", node.kind),
    }
}

fn extract_declarator_name(ast: &ParsedAst, declarator: DeclaratorRef) -> String {
    let declarator = ast.parsed_types.get_decl(declarator);
    match declarator {
        ParsedDeclarator::Identifier(name) => name.map(|n| n.to_string()).unwrap_or_else(|| "<unnamed>".to_string()),
        ParsedDeclarator::Pointer { inner, .. } => extract_declarator_name(ast, *inner),
        ParsedDeclarator::Array { inner, .. } => extract_declarator_name(ast, *inner),
        ParsedDeclarator::Function { inner, .. } => extract_declarator_name(ast, *inner),
        ParsedDeclarator::BitField { inner, .. } => extract_declarator_name(ast, *inner),
    }
}

fn extract_declarator_kind(ast: &ParsedAst, declarator: DeclaratorRef) -> String {
    let declarator = ast.parsed_types.get_decl(declarator);
    match declarator {
        ParsedDeclarator::Identifier(name) => {
            if name.is_some() {
                "identifier".to_string()
            } else {
                "abstract".to_string()
            }
        }
        ParsedDeclarator::Pointer { inner, .. } => {
            let inner_kind = extract_declarator_kind(ast, *inner);
            if inner_kind == "identifier" || inner_kind == "abstract" {
                "pointer".to_string()
            } else {
                format!("pointer to {}", inner_kind)
            }
        }
        ParsedDeclarator::Array { inner, .. } => {
            let inner_kind = extract_declarator_kind(ast, *inner);
            if inner_kind == "identifier" || inner_kind == "abstract" {
                "array".to_string()
            } else {
                format!("array of {}", inner_kind)
            }
        }
        ParsedDeclarator::Function {
            inner, params, flags, ..
        } => {
            let return_type = extract_declarator_kind(ast, *inner);
            let mut param_str = if params.len == 0 {
                "void".to_string()
            } else {
                ast.parsed_types
                    .get_params(*params)
                    .iter()
                    .map(|param| extract_type_kind(ast, &param.ty))
                    .collect::<Vec<_>>()
                    .join(", ")
            };

            if flags.is_variadic {
                if params.len == 0 {
                    param_str = "...".to_string();
                } else {
                    param_str.push_str(", ...");
                }
            }

            let return_type_str = if return_type == "abstract" || return_type == "identifier" {
                "int".to_string()
            } else {
                return_type
            };
            format!("function({}) -> {}", param_str, return_type_str)
        }
        ParsedDeclarator::BitField { inner, .. } => {
            let inner_kind = extract_declarator_kind(ast, *inner);
            format!("bitfield {}", inner_kind)
        }
    }
}

fn extract_base_kind(ast: &ParsedAst, base: ParsedBaseTypeRef) -> String {
    let base = ast.parsed_types.get_base_type(base);
    match base {
        ParsedBaseType::Builtin(spec) => {
            let s = format!("{:?}", spec);
            let mut result = String::new();
            for (i, c) in s.chars().enumerate() {
                if i > 0 && c.is_uppercase() {
                    result.push(' ');
                }
                result.push(c.to_ascii_lowercase());
            }
            result
        }
        ParsedBaseType::Record { tag, is_union, .. } => {
            let kind = if *is_union { "union" } else { "struct" };
            if let Some(tag) = tag {
                format!("{} {}", kind, tag)
            } else {
                "struct { ... }".to_string()
            }
        }
        ParsedBaseType::Enum {
            tag, underlying_type, ..
        } => {
            let mut s = if let Some(tag) = tag {
                format!("enum {}", tag)
            } else {
                "enum { ... }".to_string()
            };
            if let Some(ut) = underlying_type {
                s.push_str(" : ");
                s.push_str(&extract_type_kind(ast, ut));
            }
            s
        }
        ParsedBaseType::Typedef(name) => name.to_string(),
        ParsedBaseType::Typeof(..) => "typeof(...)".to_string(),
        ParsedBaseType::TypeofExpr(..) => "typeof(...)".to_string(),
        ParsedBaseType::TypeofUnqual(..) => "typeof_unqual(...)".to_string(),
        ParsedBaseType::TypeofUnqualExpr(..) => "typeof_unqual(...)".to_string(),
    }
}

fn extract_type_kind(ast: &ParsedAst, ty: &crate::ast::ParsedType) -> String {
    let base_kind = extract_base_kind(ast, ty.base);
    let decl_kind = extract_declarator_kind(ast, ty.declarator);

    if decl_kind == "identifier" || decl_kind == "abstract" {
        base_kind
    } else if decl_kind == "pointer" {
        format!("{} pointer", base_kind)
    } else if decl_kind == "array" {
        format!("{} array", base_kind)
    } else if decl_kind.starts_with("function") {
        format!("{} {}", base_kind, decl_kind)
    } else {
        // Fallback for complex combinations like "pointer to array"
        format!("{} to {}", decl_kind, base_kind)
    }
}

fn resolve_initializer(ast: &ParsedAst, initializer: ParsedNodeRef) -> ResolvedNodeKind {
    let node = ast.get_node(initializer);
    match &node.kind {
        ParsedNodeKind::InitializerList(designated_inits) => {
            let mut elements = Vec::new();
            for designated in designated_inits {
                // For now, ignore designations and just collect the initializer values
                // In a full implementation, we'd handle [index] and .field designators
                elements.push(resolve_initializer(ast, designated.initializer));
            }
            ResolvedNodeKind::InitializerList(elements)
        }
        _ => resolve_node(ast, initializer),
    }
}

pub(crate) fn setup_source<F, T>(source: &str, parse_fn: F) -> (ParsedAst, T)
where
    F: FnOnce(&mut Parser<'_, '_, '_>) -> T,
{
    let config = CompileConfig::from_virtual_file(source.to_string(), CompilePhase::Parse);
    let (mut sm, mut de) = setup_sm_and_de();
    let source_id = sm.add_buffer(source.as_bytes().to_vec(), "test.c", None, FileKind::Real);

    let mut preprocessor = Preprocessor::new(&mut sm, &mut de, &config.preprocessor);
    preprocessor.start_processing(source_id);
    let mut lexer = Lexer::new(&mut preprocessor, config.lang_options.c_standard);

    let mut ast = ParsedAst::new();
    let result = {
        let mut parser = Parser::new(&mut lexer, &mut ast, &config.lang_options);
        parse_fn(&mut parser)
    };

    assert!(
        de.diagnostics.is_empty(),
        "Expected no diagnostics, but found: {:?}",
        de.diagnostics
    );
    (ast, result)
}

pub(crate) fn setup_expr(source: &str) -> ResolvedNodeKind {
    let (ast, expr_result) = setup_source(source, |parser| parser.parse_expression(BindingPower::MIN));

    let node = expr_result.unwrap();
    resolve_node(&ast, node)
}

pub(crate) fn setup_declaration(source: &str) -> ResolvedNodeKind {
    setup_declaration_with_std(source, CStandard::C11)
}

pub(crate) fn setup_declaration_with_std(source: &str, std: CStandard) -> ResolvedNodeKind {
    match setup_translation_unit_with_std(source, std) {
        ResolvedNodeKind::TranslationUnit(nodes) => nodes
            .into_iter()
            .find(|n| !matches!(n, ResolvedNodeKind::Empty))
            .expect("No declaration found in translation unit"),
        _ => panic!("Expected translation unit"),
    }
}

pub(crate) fn setup_declaration_with_errors(source: &str) -> ParseError {
    let (_, decl_result) = setup_source(source, |p| declarations::parse_decl(p, false));
    match decl_result {
        Ok(_) => panic!("Expected parse error"),
        Err(e) => e,
    }
}

pub(crate) fn setup_statement(source: &str) -> ResolvedNodeKind {
    let (ast, stmt_result) = setup_source(source, statements::parse_statement);

    match stmt_result {
        Ok(node) => resolve_node(&ast, node),
        _ => panic!("Expected statement"),
    }
}

/// Setup a compound statement, useful for testing multi-statement blocks
pub(crate) fn setup_compound(source: &str) -> ResolvedNodeKind {
    let source = format!("{{ {} }}", source);
    let (ast, stmt_result) = setup_source(&source, parse_compound_statement);

    match stmt_result {
        Ok((node, _)) => resolve_node(&ast, node),
        _ => panic!("Expected multi statement block"),
    }
}

pub(crate) fn setup_translation_unit(source: &str) -> ResolvedNodeKind {
    setup_translation_unit_with_std(source, CStandard::C11)
}

pub(crate) fn setup_translation_unit_with_std(source: &str, std: CStandard) -> ResolvedNodeKind {
    let phase = CompilePhase::Parse;
    let mut config = CompileConfig::from_virtual_file(source.to_string(), phase);
    config.lang_options.c_standard = std;
    let mut driver = CompilerDriver::from_config(config);
    let out = driver.run_pipeline(phase).expect("Pipeline failed");
    let first = out.units.values().next().unwrap();
    let ast = first.parsed_ast.clone().unwrap();
    let root = ast.get_root();
    resolve_node(&ast, root)
}
