use crate::ast::parsed::{
    ParsedAst, ParsedDeclSpecifier, ParsedDeclarator, ParsedNodeKind, ParsedNodeRef, ParsedTypeSpecifier,
};
use crate::ast::{BinaryOp, UnaryOp};
use crate::diagnostic::ParseError;
use crate::driver::artifact::CompilePhase;
use crate::parser::statements::parse_compound_statement;
use crate::parser::{Parser, declarations, statements};
use crate::tests::test_utils;
use serde::Serialize;

/// Resolved AST node kind for testing - replaces NodeRef with actual content
#[derive(Debug, Serialize)]
pub(crate) enum ResolvedNodeKind {
    LiteralInt(i64),
    LiteralFloat(f64),
    LiteralString(String),
    LiteralChar(u64),
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
    SizeOfType(String), // Simplified: just type name
    AlignOf(String),    // Simplified: just type name
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
    Switch(Box<ResolvedNodeKind>, Box<ResolvedNodeKind>), // Switch statement
    Case(Box<ResolvedNodeKind>, Box<ResolvedNodeKind>), // Case statement
    CaseRange(Box<ResolvedNodeKind>, Box<ResolvedNodeKind>, Box<ResolvedNodeKind>), // GNU Case range statement
    Default(Box<ResolvedNodeKind>),         // Default statement
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
    StaticAssert(Box<ResolvedNodeKind>, String),
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

fn resolve_specifiers(ast: &ParsedAst, specifiers: &[ParsedDeclSpecifier]) -> Vec<String> {
    specifiers
        .iter()
        .map(|s| match s {
            ParsedDeclSpecifier::TypeSpecifier(ts) => match ts {
                ParsedTypeSpecifier::Void => "void".to_string(),
                ParsedTypeSpecifier::Bool => "_Bool".to_string(),
                ParsedTypeSpecifier::Char => "char".to_string(),
                ParsedTypeSpecifier::Short => "short".to_string(),
                ParsedTypeSpecifier::Int => "int".to_string(),
                ParsedTypeSpecifier::Long => "long".to_string(),
                ParsedTypeSpecifier::Float => "float".to_string(),
                ParsedTypeSpecifier::Double => "double".to_string(),
                ParsedTypeSpecifier::Signed => "signed".to_string(),
                ParsedTypeSpecifier::Unsigned => "unsigned".to_string(),
                ParsedTypeSpecifier::Complex => "_Complex".to_string(),
                ParsedTypeSpecifier::TypedefName(name) => format!("TypedefName({:?})", name.to_string()),
                ParsedTypeSpecifier::Enum(tag, enumerators) => {
                    let tag_str = tag.as_ref().map(|s| s.as_str()).unwrap_or("");
                    if let Some(enums) = enumerators {
                        let enum_parts: Vec<String> = enums
                            .iter()
                            .map(|&node_ref| match &ast.get_node(node_ref).kind {
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
                        format!("enum {} {{ {} }}", tag_str, enum_parts.join(", "))
                    } else {
                        format!("enum {}", tag_str)
                    }
                }
                ParsedTypeSpecifier::Record(is_union, tag, def) => {
                    let record_kind = if *is_union { "union" } else { "struct" };
                    let tag_str = tag.as_ref().map(|s| s.as_str()).unwrap_or("");
                    let has_body = def.as_ref().is_some_and(|d| d.members.is_some());

                    let mut s = record_kind.to_string();
                    if !tag_str.is_empty() {
                        s.push(' ');
                        s.push_str(tag_str);
                    }
                    if has_body {
                        s.push_str(" { ... }");
                    }
                    s
                }
                _ => format!("{:?}", ts),
            },
            ParsedDeclSpecifier::StorageClass(sc) => format!("{:?}", sc),
            ParsedDeclSpecifier::TypeQualifier(tq) => format!("TypeQualifier({:?})", tq),
            ParsedDeclSpecifier::FunctionSpecifier(fs) => format!("{:?}", fs),
            ParsedDeclSpecifier::AlignmentSpecifier(aspec) => format!("{:?}", aspec),
            ParsedDeclSpecifier::Attribute => "__attribute__".to_string(),
        })
        .collect()
}

/// Resolve a ParsedNodeRef to a ResolvedNodeKind by recursively following references
pub(crate) fn resolve_node(ast: &ParsedAst, node_ref: ParsedNodeRef) -> ResolvedNodeKind {
    let node = ast.get_node(node_ref);
    match &node.kind {
        ParsedNodeKind::Literal(literal) => match literal {
            crate::ast::literal::Literal::Int { val, .. } => ResolvedNodeKind::LiteralInt(*val),
            crate::ast::literal::Literal::Float { val, .. } => ResolvedNodeKind::LiteralFloat(*val),
            crate::ast::literal::Literal::String(s) => ResolvedNodeKind::LiteralString(s.to_string()),
            crate::ast::literal::Literal::Char(c) => ResolvedNodeKind::LiteralChar(*c),
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
        ParsedNodeKind::MemberAccess(object, field, is_arrow) => {
            ResolvedNodeKind::MemberAccess(Box::new(resolve_node(ast, *object)), field.to_string(), *is_arrow)
        }
        ParsedNodeKind::IndexAccess(array, index) => {
            ResolvedNodeKind::IndexAccess(Box::new(resolve_node(ast, *array)), Box::new(resolve_node(ast, *index)))
        }
        ParsedNodeKind::Cast(type_ref, expr) => {
            // For simplicity, just show a placeholder type name
            ResolvedNodeKind::Cast(
                format!("parsed_type_{}_{}", type_ref.base.get(), type_ref.declarator.get()),
                Box::new(resolve_node(ast, *expr)),
            )
        }
        ParsedNodeKind::SizeOfExpr(expr) => ResolvedNodeKind::SizeOfExpr(Box::new(resolve_node(ast, *expr))),
        ParsedNodeKind::SizeOfType(type_ref) => ResolvedNodeKind::SizeOfType(format!("type_{}", type_ref.base.get())),
        ParsedNodeKind::AlignOf(type_ref) => ResolvedNodeKind::AlignOf(format!("type_{}", type_ref.base.get())),
        ParsedNodeKind::Declaration(decl) => {
            let specifiers = resolve_specifiers(ast, &decl.specifiers);
            let init_declarators = decl
                .init_declarators
                .iter()
                .map(|init_decl| {
                    let name =
                        extract_declarator_name(&init_decl.declarator).unwrap_or_else(|| "<unnamed>".to_string());
                    let kind_str = extract_declarator_kind(&init_decl.declarator);
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
        ParsedNodeKind::ExpressionStatement(expr) => {
            ResolvedNodeKind::ExpressionStatement(expr.map(|e| Box::new(resolve_node(ast, e))))
        }
        ParsedNodeKind::CompoundStatement(statements) => {
            ResolvedNodeKind::CompoundStatement(statements.iter().map(|&stmt| resolve_node(ast, stmt)).collect())
        }
        ParsedNodeKind::GnuStatementExpression(compound_stmt, result_expr) => ResolvedNodeKind::GnuStatementExpression(
            Box::new(resolve_node(ast, *compound_stmt)),
            Box::new(resolve_node(ast, *result_expr)),
        ),
        ParsedNodeKind::GenericSelection(controlling_expr, associations) => {
            let resolved_controlling = Box::new(resolve_node(ast, *controlling_expr));
            let resolved_associations = associations
                .iter()
                .map(|assoc| {
                    let type_name = assoc.type_name.map(|type_ref| {
                        // For simplicity, just show a placeholder type name
                        // In a full implementation, we'd resolve the actual type
                        format!("type_{}", type_ref.base.get())
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
            ResolvedNodeKind::StaticAssert(Box::new(resolve_node(ast, *expr)), msg.to_string())
        }
        ParsedNodeKind::CompoundLiteral(type_ref, init) => {
            // Check if init is an InitializerList, if so use resolve_initializer, otherwise resolve_node
            let init_node = ast.get_node(*init);
            let resolved_init = match init_node.kind {
                ParsedNodeKind::InitializerList(_) => resolve_initializer(ast, *init),
                _ => resolve_node(ast, *init),
            };
            ResolvedNodeKind::CompoundLiteral(
                format!("parsed_type_{}", type_ref.base.get()), // Simplified type
                Box::new(resolved_init),
            )
        }
        ParsedNodeKind::TranslationUnit(nodes) => {
            ResolvedNodeKind::TranslationUnit(nodes.iter().map(|&n| resolve_node(ast, n)).collect())
        }
        ParsedNodeKind::FunctionDef(def) => {
            let specifiers = resolve_specifiers(ast, &def.specifiers);
            let name = extract_declarator_name(&def.declarator).unwrap_or_else(|| "<unnamed>".to_string());
            let kind_str = extract_declarator_kind(&def.declarator);
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
        ParsedNodeKind::EmptyStatement | ParsedNodeKind::Dummy => ResolvedNodeKind::Empty,
        // Add more cases as needed for other ParsedNodeKind variants used in tests
        _ => panic!("Unsupported ParsedNodeKind for resolution: {:?}", node.kind),
    }
}

fn extract_declarator_name(declarator: &ParsedDeclarator) -> Option<String> {
    match declarator {
        ParsedDeclarator::Identifier(name, _) => Some(name.to_string()),
        ParsedDeclarator::Pointer(_, next) => next.as_ref().and_then(|d| extract_declarator_name(d)),
        ParsedDeclarator::Array(next, _) => extract_declarator_name(next),
        ParsedDeclarator::Function { inner, .. } => extract_declarator_name(inner),
        ParsedDeclarator::BitField(next, _) => extract_declarator_name(next),
        ParsedDeclarator::Abstract => None,
        _ => None,
    }
}

fn extract_declarator_kind(declarator: &ParsedDeclarator) -> String {
    match declarator {
        ParsedDeclarator::Identifier(_, _) => "identifier".to_string(),
        ParsedDeclarator::Pointer(_, Some(inner)) => {
            let inner_kind = extract_declarator_kind(inner);
            if inner_kind == "identifier" || inner_kind == "abstract" {
                "pointer".to_string()
            } else {
                format!("pointer to {}", inner_kind)
            }
        }

        ParsedDeclarator::Pointer(_, None) => "pointer".to_string(),
        ParsedDeclarator::Array(inner, _) => {
            let inner_kind = extract_declarator_kind(inner);
            if inner_kind == "identifier" || inner_kind == "abstract" {
                "array".to_string()
            } else {
                format!("array of {}", inner_kind)
            }
        }
        ParsedDeclarator::Function {
            inner,
            params,
            is_variadic,
        } => {
            let return_type = extract_declarator_kind(inner);
            let mut param_str = if params.is_empty() {
                "void".to_string()
            } else {
                params
                    .iter()
                    .map(|param| {
                        // Extract parameter type from specifiers
                        let mut type_parts = Vec::new();
                        for spec in &param.specifiers {
                            if let ParsedDeclSpecifier::TypeSpecifier(ts) = spec {
                                match ts {
                                    ParsedTypeSpecifier::Void => type_parts.push("void"),
                                    ParsedTypeSpecifier::Char => type_parts.push("char"),
                                    ParsedTypeSpecifier::Short => type_parts.push("short"),
                                    ParsedTypeSpecifier::Int => type_parts.push("int"),
                                    ParsedTypeSpecifier::Long => type_parts.push("long"),
                                    ParsedTypeSpecifier::Float => type_parts.push("float"),
                                    ParsedTypeSpecifier::Double => type_parts.push("double"),
                                    ParsedTypeSpecifier::Signed => type_parts.push("signed"),
                                    ParsedTypeSpecifier::Unsigned => type_parts.push("unsigned"),
                                    _ => type_parts.push("..."),
                                }
                            }
                        }
                        let base_type = if type_parts.is_empty() {
                            "int".to_string()
                        } else {
                            type_parts.join(" ")
                        };

                        if let Some(decl) = &param.declarator {
                            let param_kind = extract_declarator_kind(decl);
                            if param_kind == "identifier" {
                                base_type
                            } else if param_kind.starts_with("function(") && param_kind.ends_with(") -> int") {
                                param_kind
                            } else {
                                format!("{} {}", base_type, param_kind)
                            }
                        } else {
                            base_type
                        }
                    })
                    .collect::<Vec<_>>()
                    .join(", ")
            };

            if *is_variadic {
                if params.is_empty() {
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
        ParsedDeclarator::BitField(inner, _) => {
            let inner_kind = extract_declarator_kind(inner);
            format!("bitfield {}", inner_kind)
        }
        ParsedDeclarator::Abstract => "abstract".to_string(),
        ParsedDeclarator::AnonymousRecord(is_union, _) => {
            if *is_union {
                "union".to_string()
            } else {
                "struct".to_string()
            }
        }
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

/// Generic helper function for parsing source code with common setup
pub(crate) fn setup_source<F, T>(source: &str, parse_fn: F) -> (ParsedAst, T)
where
    F: FnOnce(&mut Parser<'_, '_>) -> T,
{
    let phase = CompilePhase::Lex;
    let (driver, out) = test_utils::run_pipeline(source, phase);
    let mut out = out.unwrap();
    let first = out.units.first_mut().unwrap();
    let artifact = first.1;
    let tokens = artifact.lexed.clone().unwrap();

    let mut diag = driver.diagnostics;
    let mut ast = ParsedAst::new();
    let mut parser = Parser::new(&tokens, &mut ast, &mut diag);
    let result = parse_fn(&mut parser);

    assert!(diag.diagnostics.is_empty());
    (ast, result)
}

pub(crate) fn setup_expr(source: &str) -> ResolvedNodeKind {
    let (ast, expr_result) = setup_source(source, |parser| {
        parser.parse_expression(crate::parser::BindingPower::MIN)
    });

    let node_ref = expr_result.unwrap();
    resolve_node(&ast, node_ref)
}

pub(crate) fn setup_declaration(source: &str) -> ResolvedNodeKind {
    let (ast, decl_result) = setup_source(source, declarations::parse_declaration);

    match decl_result {
        Ok(node_ref) => resolve_node(&ast, node_ref),
        _ => panic!("Expected declaration"),
    }
}

pub(crate) fn setup_declaration_with_errors(source: &str) -> ParseError {
    let (_, decl_result) = setup_source(source, declarations::parse_declaration);
    match decl_result {
        Ok(_) => panic!("Expected parse error"),
        Err(e) => e,
    }
}

pub(crate) fn setup_statement(source: &str) -> ResolvedNodeKind {
    let (ast, stmt_result) = setup_source(source, statements::parse_statement);

    match stmt_result {
        Ok(node_ref) => resolve_node(&ast, node_ref),
        _ => panic!("Expected statement"),
    }
}

/// Setup a compound statement, useful for testing multi-statement blocks
pub(crate) fn setup_compound(source: &str) -> ResolvedNodeKind {
    let source = format!("{{ {} }}", source);
    let (ast, stmt_result) = setup_source(&source, parse_compound_statement);

    match stmt_result {
        Ok((node_ref, _)) => resolve_node(&ast, node_ref),
        _ => panic!("Expected multi statement block"),
    }
}

pub(crate) fn setup_translation_unit(source: &str) -> ResolvedNodeKind {
    let phase = CompilePhase::Parse;
    let (_, out) = test_utils::run_pipeline(source, phase);
    let mut out = out.unwrap();
    let first = out.units.first_mut().unwrap();
    let artifact = first.1;
    let ast = artifact.parsed_ast.clone().unwrap();
    let root_ref = ast.get_root();
    resolve_node(&ast, root_ref)
}
