#![cfg(test)]
use crate::ast::{Ast, BinaryOp, DeclSpecifier, Declarator, NodeKind, NodeRef, TypeSpecifier, UnaryOp};
use crate::diagnostic::DiagnosticEngine;
use crate::lang_options::LangOptions;
use crate::lexer::Lexer;
use crate::parser::Parser;
use crate::pp::Preprocessor;
use crate::source_manager::SourceManager;
use serde::Serialize;
use target_lexicon::Triple;

/// Resolved AST node kind for testing - replaces NodeRef with actual content
#[derive(Debug, Serialize)]
enum ResolvedNodeKind {
    LiteralInt(i64),
    LiteralFloat(f64),
    LiteralString(String),
    LiteralChar(u8),
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
                                            // Add more as needed for tests
}

/// Simplified resolved generic association for testing
#[derive(Debug, Serialize)]
struct ResolvedGenericAssociation {
    type_name: Option<String>, // None for 'default:'
    result_expr: ResolvedNodeKind,
}

/// Simplified resolved init declarator for testing
#[derive(Debug, Serialize)]
struct ResolvedInitDeclarator {
    name: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    kind: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    initializer: Option<ResolvedNodeKind>,
}

/// Resolve a NodeRef to a ResolvedNodeKind by recursively following references
fn resolve_node(ast: &Ast, node_ref: NodeRef) -> ResolvedNodeKind {
    let node = ast.get_node(node_ref);
    match &node.kind {
        NodeKind::LiteralInt(value) => ResolvedNodeKind::LiteralInt(*value),
        NodeKind::LiteralFloat(value) => ResolvedNodeKind::LiteralFloat(*value),
        NodeKind::LiteralString(symbol) => ResolvedNodeKind::LiteralString(symbol.to_string()),
        NodeKind::LiteralChar(value) => ResolvedNodeKind::LiteralChar(*value),
        NodeKind::Ident(symbol, _) => ResolvedNodeKind::Ident(symbol.to_string()),
        NodeKind::UnaryOp(op, operand) => ResolvedNodeKind::UnaryOp(*op, Box::new(resolve_node(ast, *operand))),
        NodeKind::BinaryOp(op, left, right) => ResolvedNodeKind::BinaryOp(
            *op,
            Box::new(resolve_node(ast, *left)),
            Box::new(resolve_node(ast, *right)),
        ),
        NodeKind::TernaryOp(cond, then_expr, else_expr) => ResolvedNodeKind::TernaryOp(
            Box::new(resolve_node(ast, *cond)),
            Box::new(resolve_node(ast, *then_expr)),
            Box::new(resolve_node(ast, *else_expr)),
        ),
        NodeKind::PostIncrement(operand) => ResolvedNodeKind::PostIncrement(Box::new(resolve_node(ast, *operand))),
        NodeKind::PostDecrement(operand) => ResolvedNodeKind::PostDecrement(Box::new(resolve_node(ast, *operand))),
        NodeKind::Assignment(op, lhs, rhs) => ResolvedNodeKind::Assignment(
            *op,
            Box::new(resolve_node(ast, *lhs)),
            Box::new(resolve_node(ast, *rhs)),
        ),
        NodeKind::FunctionCall(func, args) => ResolvedNodeKind::FunctionCall(
            Box::new(resolve_node(ast, *func)),
            args.iter().map(|&arg| resolve_node(ast, arg)).collect(),
        ),
        NodeKind::MemberAccess(object, field, is_arrow) => {
            ResolvedNodeKind::MemberAccess(Box::new(resolve_node(ast, *object)), field.to_string(), *is_arrow)
        }
        NodeKind::IndexAccess(array, index) => {
            ResolvedNodeKind::IndexAccess(Box::new(resolve_node(ast, *array)), Box::new(resolve_node(ast, *index)))
        }
        NodeKind::Cast(type_ref, expr) => {
            // For simplicity, just show a placeholder type name
            // In a full implementation, we'd resolve the actual type
            ResolvedNodeKind::Cast(format!("type_{}", type_ref.get()), Box::new(resolve_node(ast, *expr)))
        }
        NodeKind::SizeOfExpr(expr) => ResolvedNodeKind::SizeOfExpr(Box::new(resolve_node(ast, *expr))),
        NodeKind::SizeOfType(type_ref) => ResolvedNodeKind::SizeOfType(format!("type_{}", type_ref.get())),
        NodeKind::AlignOf(type_ref) => ResolvedNodeKind::AlignOf(format!("type_{}", type_ref.get())),
        NodeKind::Declaration(decl) => {
            let specifiers = decl
                .specifiers
                .iter()
                .map(|s| match s {
                    DeclSpecifier::TypeSpecifier(ts) => match ts {
                        TypeSpecifier::Void => "void".to_string(),
                        TypeSpecifier::Bool => "_Bool".to_string(),
                        TypeSpecifier::Char => "char".to_string(),
                        TypeSpecifier::Short => "short".to_string(),
                        TypeSpecifier::Int => "int".to_string(),
                        TypeSpecifier::Long => "long".to_string(),
                        TypeSpecifier::Float => "float".to_string(),
                        TypeSpecifier::Double => "double".to_string(),
                        TypeSpecifier::Signed => "signed".to_string(),
                        TypeSpecifier::Unsigned => "unsigned".to_string(),
                        TypeSpecifier::Complex => "_Complex".to_string(),
                        TypeSpecifier::Enum(tag, enumerators) => {
                            let tag_str = tag.as_ref().map(|s| s.as_str()).unwrap_or("");
                            if let Some(enums) = enumerators {
                                let enum_parts: Vec<String> = enums
                                    .iter()
                                    .map(|&node_ref| match &ast.get_node(node_ref).kind {
                                        NodeKind::EnumConstant(name, Some(value_expr)) => {
                                            let value = resolve_node(ast, *value_expr);
                                            match value {
                                                ResolvedNodeKind::LiteralInt(val) => format!("{} = {}", name, val),
                                                _ => format!("{} = <expr>", name),
                                            }
                                        }
                                        NodeKind::EnumConstant(name, None) => name.to_string(),
                                        _ => "<invalid>".to_string(),
                                    })
                                    .collect();
                                format!("enum {} {{ {} }}", tag_str, enum_parts.join(", "))
                            } else {
                                format!("enum {}", tag_str)
                            }
                        }
                        TypeSpecifier::Record(is_union, tag, def) => {
                            let record_kind = if *is_union { "union" } else { "struct" };
                            let tag_str = tag.as_ref().map(|s| s.as_str()).unwrap_or("");
                            let has_body = def.as_ref().map_or(false, |d| d.members.is_some());

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
                    DeclSpecifier::StorageClass(sc) => format!("{:?}", sc),
                    DeclSpecifier::TypeQualifiers(tq) => format!("{:?}", tq),
                    DeclSpecifier::FunctionSpecifiers(fs) => format!("{:?}", fs),
                    DeclSpecifier::AlignmentSpecifier(aspec) => format!("{:?}", aspec),
                    DeclSpecifier::Attribute => "__attribute__".to_string(),
                })
                .collect();
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
                        .map(|init| resolve_initializer(ast, init));
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
        NodeKind::EnumConstant(name, value_expr) => ResolvedNodeKind::EnumConstant(
            name.to_string(),
            value_expr.map(|expr| Box::new(resolve_node(ast, expr))),
        ),
        NodeKind::ExpressionStatement(expr) => {
            ResolvedNodeKind::ExpressionStatement(expr.map(|e| Box::new(resolve_node(ast, e))))
        }
        NodeKind::CompoundStatement(statements) => {
            ResolvedNodeKind::CompoundStatement(statements.iter().map(|&stmt| resolve_node(ast, stmt)).collect())
        }
        NodeKind::GnuStatementExpression(compound_stmt, result_expr) => ResolvedNodeKind::GnuStatementExpression(
            Box::new(resolve_node(ast, *compound_stmt)),
            Box::new(resolve_node(ast, *result_expr)),
        ),
        NodeKind::GenericSelection(controlling_expr, associations) => {
            let resolved_controlling = Box::new(resolve_node(ast, *controlling_expr));
            let resolved_associations = associations
                .iter()
                .map(|assoc| {
                    let type_name = assoc.type_name.map(|type_ref| {
                        // For simplicity, just show a placeholder type name
                        // In a full implementation, we'd resolve the actual type
                        format!("type_{}", type_ref.get())
                    });
                    let result_expr = resolve_node(ast, assoc.result_expr);
                    ResolvedGenericAssociation { type_name, result_expr }
                })
                .collect();
            ResolvedNodeKind::GenericSelection(resolved_controlling, resolved_associations)
        }
        // Add more cases as needed for other NodeKind variants used in tests
        _ => panic!("Unsupported NodeKind for resolution: {:?}", node.kind),
    }
}

fn extract_declarator_name(declarator: &Declarator) -> Option<String> {
    match declarator {
        Declarator::Identifier(name, _, _) => Some(name.to_string()),
        Declarator::Pointer(_, next) => next.as_ref().and_then(|d| extract_declarator_name(d)),
        Declarator::Array(next, _) => extract_declarator_name(next),
        Declarator::Function(next, _) => extract_declarator_name(next),
        Declarator::BitField(next, _) => extract_declarator_name(next),
        Declarator::Abstract => None,
        _ => None,
    }
}

fn extract_declarator_kind(declarator: &Declarator) -> String {
    match declarator {
        Declarator::Identifier(_, _, _) => "identifier".to_string(),
        Declarator::Pointer(_, Some(inner)) => {
            let inner_kind = extract_declarator_kind(inner);
            if inner_kind == "identifier" || inner_kind == "abstract" {
                "pointer".to_string()
            } else {
                format!("pointer to {}", inner_kind)
            }
        }
        Declarator::Pointer(_, None) => "pointer".to_string(),
        Declarator::Array(inner, _) => {
            let inner_kind = extract_declarator_kind(inner);
            if inner_kind == "identifier" || inner_kind == "abstract" {
                "array".to_string()
            } else {
                format!("array of {}", inner_kind)
            }
        }
        Declarator::Function(inner, params) => {
            let return_type = extract_declarator_kind(inner);
            let param_str = if params.is_empty() {
                "void".to_string()
            } else {
                params
                    .iter()
                    .map(|param| {
                        // Extract parameter type from specifiers
                        let mut type_parts = Vec::new();
                        for spec in &param.specifiers {
                            if let DeclSpecifier::TypeSpecifier(ts) = spec {
                                match ts {
                                    TypeSpecifier::Void => type_parts.push("void"),
                                    TypeSpecifier::Char => type_parts.push("char"),
                                    TypeSpecifier::Short => type_parts.push("short"),
                                    TypeSpecifier::Int => type_parts.push("int"),
                                    TypeSpecifier::Long => type_parts.push("long"),
                                    TypeSpecifier::Float => type_parts.push("float"),
                                    TypeSpecifier::Double => type_parts.push("double"),
                                    TypeSpecifier::Signed => type_parts.push("signed"),
                                    TypeSpecifier::Unsigned => type_parts.push("unsigned"),
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

            let return_type_str = if return_type == "abstract" {
                "int".to_string()
            } else if return_type == "identifier" {
                "int".to_string()
            } else {
                return_type
            };
            format!("function({}) -> {}", param_str, return_type_str)
        }
        Declarator::BitField(inner, _) => {
            let inner_kind = extract_declarator_kind(inner);
            format!("bitfield {}", inner_kind)
        }
        Declarator::Abstract => "abstract".to_string(),
        Declarator::AnonymousRecord(is_union, _) => {
            if *is_union {
                "union".to_string()
            } else {
                "struct".to_string()
            }
        }
    }
}

fn resolve_initializer(ast: &Ast, initializer: &crate::ast::Initializer) -> ResolvedNodeKind {
    match initializer {
        crate::ast::Initializer::Expression(expr) => resolve_node(ast, *expr),
        crate::ast::Initializer::List(designated_inits) => {
            let mut elements = Vec::new();
            for designated in designated_inits {
                // For now, ignore designations and just collect the initializer values
                // In a full implementation, we'd handle [index] and .field designators
                elements.push(resolve_initializer(ast, &designated.initializer));
            }
            ResolvedNodeKind::InitializerList(elements)
        }
    }
}

/// Generic helper function for parsing source code with common setup
fn setup_source<F, T>(source: &str, parse_fn: F) -> (Ast, T)
where
    F: FnOnce(&mut Parser<'_, '_>) -> T,
{
    let mut sm = SourceManager::new();
    let mut diag = DiagnosticEngine::new();
    let lang_opts = LangOptions::c11();
    let target_info = Triple::unknown();
    let source_id = sm.add_buffer(source.as_bytes().to_vec(), "test.c");

    let mut pp = Preprocessor::new(
        &mut sm,
        &mut diag,
        lang_opts.clone(),
        target_info.clone(),
        &crate::pp::PPConfig {
            max_include_depth: 200,
            ..Default::default()
        },
    );
    let pp_tokens = pp.process(source_id, &Default::default()).unwrap();

    let mut lexer = Lexer::new(&pp_tokens);
    let tokens = lexer.tokenize_all();

    let mut ast = Ast::new();
    let mut parser = Parser::new(&tokens, &mut ast, &mut diag);
    let result = parse_fn(&mut parser);
    assert!(diag.diagnostics.is_empty());
    (ast, result)
}

fn setup_expr(source: &str) -> ResolvedNodeKind {
    let (ast, expr_result) = setup_source(source, |parser| {
        parser.parse_expression(crate::parser::BindingPower::MIN)
    });

    match expr_result {
        Ok(crate::parser::ParseExprOutput::Expression(node_ref)) => resolve_node(&ast, node_ref),
        _ => panic!("Expected expression"),
    }
}

fn setup_declaration(source: &str) -> ResolvedNodeKind {
    let (ast, decl_result) = setup_source(source, |parser| parser.parse_declaration());

    match decl_result {
        Ok(node_ref) => resolve_node(&ast, node_ref),
        _ => panic!("Expected declaration"),
    }
}

fn parse_declaration_with_errors(source: &str) -> Result<ResolvedNodeKind, Vec<String>> {
    let mut sm = SourceManager::new();
    let mut diag = DiagnosticEngine::new();
    let lang_opts = LangOptions::c11();
    let target_info = Triple::unknown();
    let source_id = sm.add_buffer(source.as_bytes().to_vec(), "test.c");

    let mut pp = Preprocessor::new(
        &mut sm,
        &mut diag,
        lang_opts.clone(),
        target_info.clone(),
        &crate::pp::PPConfig {
            max_include_depth: 200,
            ..Default::default()
        },
    );
    let pp_tokens = pp.process(source_id, &Default::default()).unwrap();

    let mut lexer = Lexer::new(&pp_tokens);
    let tokens = lexer.tokenize_all();

    let mut ast = Ast::new();
    let mut parser = Parser::new(&tokens, &mut ast, &mut diag);
    let result = parser.parse_declaration();

    let errors: Vec<String> = diag.diagnostics.iter().map(|d| d.message.clone()).collect();

    match result {
        Ok(node_ref) => {
            if errors.is_empty() {
                Ok(resolve_node(&ast, node_ref))
            } else {
                Err(errors)
            }
        }
        Err(e) => Err(vec![format!("Parse error: {:?}", e)]),
    }
}

#[test]
fn test_function_returning_array_rejected() {
    let result = parse_declaration_with_errors("int f(int)[3];");
    assert!(result.is_err(), "Parser should reject function returning array");
    let errors = result.unwrap_err();
    assert_eq!(errors.len(), 1);
    assert!(errors[0].contains("function returning an array is not allowed"));
}

#[test]
fn test_simple_addition() {
    let resolved = setup_expr("1 + 2");
    insta::assert_yaml_snapshot!(&resolved, @r"
    BinaryOp:
      - Add
      - LiteralInt: 1
      - LiteralInt: 2
    ");
}

#[test]
fn test_unary_operators() {
    let resolved = setup_expr("-1");
    insta::assert_yaml_snapshot!(&resolved, @r"
    UnaryOp:
      - Minus
      - LiteralInt: 1
    ");
}

#[test]
fn test_simple_struct_declaration() {
    let resolved = setup_declaration("struct Point;");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Declaration:
      specifiers:
        - struct Point
      init_declarators: []
    ");
}

#[test]
fn test_struct_declaration_with_body() {
    let resolved = setup_declaration("struct Point { int x; int y; };");
    insta::assert_yaml_snapshot!(&resolved, @r#"
    Declaration:
      specifiers:
        - "struct Point { ... }"
      init_declarators: []
    "#);
}

#[test]
fn test_struct_variable_declaration() {
    let resolved = setup_declaration("struct Point p;");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Declaration:
      specifiers:
        - struct Point
      init_declarators:
        - name: p
    ");
}

#[test]
fn test_struct_definition_and_variable() {
    let resolved = setup_declaration("struct Point { int x; } p;");
    insta::assert_yaml_snapshot!(&resolved, @r#"
    Declaration:
      specifiers:
        - "struct Point { ... }"
      init_declarators:
        - name: p
    "#);
}

#[test]
fn test_anonymous_struct_declaration() {
    let resolved = setup_declaration("struct { int x; } p;");
    insta::assert_yaml_snapshot!(&resolved, @r#"
    Declaration:
      specifiers:
        - "struct { ... }"
      init_declarators:
        - name: p
    "#);
}

#[test]
fn test_precedence() {
    let resolved = setup_expr("1 + 2 * 3");
    insta::assert_yaml_snapshot!(&resolved, @r"
    BinaryOp:
      - Add
      - LiteralInt: 1
      - BinaryOp:
          - Mul
          - LiteralInt: 2
          - LiteralInt: 3
    ");
}

#[test]
fn test_parenthesized_expression() {
    let resolved = setup_expr("(1 + 2) * 3");
    insta::assert_yaml_snapshot!(&resolved, @r"
    BinaryOp:
      - Mul
      - BinaryOp:
          - Add
          - LiteralInt: 1
          - LiteralInt: 2
      - LiteralInt: 3
    ");
}

#[test]
fn test_assignment() {
    let resolved = setup_expr("a = 1");
    insta::assert_yaml_snapshot!(&resolved, @r"
    BinaryOp:
      - Assign
      - Ident: a
      - LiteralInt: 1
    ");
}

#[test]
fn test_function_call() {
    let resolved = setup_expr("foo(1, 2)");
    insta::assert_yaml_snapshot!(&resolved, @r"
    FunctionCall:
      - Ident: foo
      - - LiteralInt: 1
        - LiteralInt: 2
    ");
}

#[test]
fn test_member_access() {
    let resolved = setup_expr("a.b");
    insta::assert_yaml_snapshot!(&resolved, @r"
    MemberAccess:
      - Ident: a
      - b
      - false
    ");
}

#[test]
fn test_array_indexing() {
    let resolved = setup_expr("a[1]");
    insta::assert_yaml_snapshot!(&resolved, @r"
    IndexAccess:
      - Ident: a
      - LiteralInt: 1
    ");
}

#[test]
fn test_sizeof_expression() {
    let resolved = setup_expr("sizeof(a)");
    insta::assert_yaml_snapshot!(&resolved, @r"
    SizeOfExpr:
      Ident: a
    ");
}

#[test]
fn test_complex_expression() {
    let resolved = setup_expr("a + b * c[d] - e.f");
    insta::assert_yaml_snapshot!(&resolved, @r"
    BinaryOp:
      - Sub
      - BinaryOp:
          - Add
          - Ident: a
          - BinaryOp:
              - Mul
              - Ident: b
              - IndexAccess:
                  - Ident: c
                  - Ident: d
      - MemberAccess:
          - Ident: e
          - f
          - false
    ");
}

#[test]
fn test_simple_declaration() {
    let resolved = setup_declaration("int x;");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: x
    ");
}

#[test]
fn test_declaration_with_initializer() {
    let resolved = setup_declaration("int x = 42;");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: x
          initializer:
            LiteralInt: 42
    ");
}

#[test]
fn test_multiple_declarators() {
    let resolved = setup_declaration("int x, y = 1, z;");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: x
        - name: y
          initializer:
            LiteralInt: 1
        - name: z
    ");
}

#[test]
fn test_pointer_declaration() {
    let resolved = setup_declaration("int *p;");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: p
          kind: pointer
    ");
}

#[test]
fn test_array_declaration() {
    let resolved = setup_declaration("int arr[10];");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: arr
          kind: array
    ");
}

#[test]
fn test_array_declaration_with_initializer() {
    let resolved = setup_declaration("int arr[3] = {1, 2, 3};");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: arr
          kind: array
          initializer:
            InitializerList:
              - LiteralInt: 1
              - LiteralInt: 2
              - LiteralInt: 3
    ");
}

#[test]
fn test_complex_declaration() {
    let resolved = setup_declaration("int a = 1, *b[3], c(struct X, int), d = (1, 2, 3);");
    insta::assert_yaml_snapshot!(&resolved, @r#"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: a
          initializer:
            LiteralInt: 1
        - name: b
          kind: pointer to array
        - name: c
          kind: "function(..., int) -> int"
        - name: d
          initializer:
            BinaryOp:
              - Comma
              - BinaryOp:
                  - Comma
                  - LiteralInt: 1
                  - LiteralInt: 2
              - LiteralInt: 3
    "#);
}

#[test]
fn test_function_with_array_of_pointer_param() {
    let resolved = setup_declaration("int f(int (*arr)[3]);");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: f
          kind: function(int array of pointer) -> int
    ");
}

#[test]
fn test_array_of_function_pointers() {
    let resolved = setup_declaration("int (*callbacks[10])(int, float);");
    insta::assert_yaml_snapshot!(&resolved, @r#"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: callbacks
          kind: "function(int, float) -> pointer to array"
    "#);
}

#[test]
fn test_function_pointer_with_initializer() {
    let resolved = setup_declaration("int (*f)(int) = 0;");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: f
          kind: function(int) -> pointer
          initializer:
            LiteralInt: 0
    ");
}

#[test]
fn test_array_of_pointers_with_initializer() {
    let resolved = setup_declaration("int *p[3] = { &x, 0, &y };");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: p
          kind: pointer to array
          initializer:
            InitializerList:
              - UnaryOp:
                  - AddrOf
                  - Ident: x
              - LiteralInt: 0
              - UnaryOp:
                  - AddrOf
                  - Ident: y
    ");
}

#[test]
fn test_function_pointer_with_cast_initializer() {
    let resolved = setup_declaration("int (*fp)(int) = (int (*)(int))0;");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: fp
          kind: function(int) -> pointer
          initializer:
            Cast:
              - type_4
              - LiteralInt: 0
    ");
}

#[test]
fn test_mixed_declarators_simple() {
    let resolved = setup_declaration("int *a, (*b)(int), c[10];");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: a
          kind: pointer
        - name: b
          kind: function(int) -> pointer
        - name: c
          kind: array
    ");
}

#[test]
fn test_deeply_mixed_declarators() {
    let resolved = setup_declaration("int *a, (*b[5])(double), c(struct X, int), d = (1, 2);");
    insta::assert_yaml_snapshot!(&resolved, @r#"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: a
          kind: pointer
        - name: b
          kind: function(double) -> pointer to array
        - name: c
          kind: "function(..., int) -> int"
        - name: d
          initializer:
            BinaryOp:
              - Comma
              - LiteralInt: 1
              - LiteralInt: 2
    "#);
}

#[test]
fn test_madness_with_parentheses() {
    let resolved = setup_declaration("int (*a)(int), *(*b)(float), (*c[3])(int, int);");
    insta::assert_yaml_snapshot!(&resolved, @r#"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: a
          kind: function(int) -> pointer
        - name: b
          kind: pointer to function(float) -> pointer
        - name: c
          kind: "function(int, int) -> pointer to array"
    "#);
}

#[test]
fn test_callback_style_function() {
    let resolved = setup_declaration("int sort(int (*cmp)(int, int));");
    insta::assert_yaml_snapshot!(&resolved, @r#"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: sort
          kind: "function(int function(int, int) -> pointer) -> int"
    "#);
}

#[test]
fn test_function_returning_pointer_to_function() {
    let resolved = setup_declaration("int (*make_cb(int (*cmp)(int, int)))(int, int);");
    insta::assert_yaml_snapshot!(&resolved, @r#"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: make_cb
          kind: "function(int, int) -> pointer to function(int function(int, int) -> pointer) -> int"
    "#);
}

#[test]
fn test_parentheses_that_do_nothing() {
    let resolved = setup_declaration("int (((a)));");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: a
    ");
}

#[test]
fn test_insane_parentheses_on_pointer_to_array_to_function() {
    let resolved = setup_declaration("int (*(((*f))(int)))[5];");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: f
          kind: array of pointer to function(int) -> pointer
    ");
}

#[test]
fn test_array_of_functions_rejected() {
    let result = parse_declaration_with_errors("int f[3](int);");
    assert!(result.is_err(), "Parser should reject array of functions");
}

#[test]
fn test_function_returning_function_rejected() {
    let result = parse_declaration_with_errors("int f(int)(float);");
    assert!(result.is_err(), "Parser should reject function returning function");
}

#[test]
fn test_ellipsis_not_last_parameter_rejected() {
    let result = parse_declaration_with_errors("int f(int ..., int);");
    assert!(result.is_err(), "Expected parse error for ellipsis not last parameter");
}

#[test]
fn test_enum_declaration_with_values() {
    let resolved = setup_declaration("enum Color { RED = 1, GREEN = 2, BLUE };");
    insta::assert_yaml_snapshot!(&resolved, @r#"
    Declaration:
      specifiers:
        - "enum Color { RED = 1, GREEN = 2, BLUE }"
      init_declarators: []
    "#);
}

#[test]
fn test_function_with_array_abstract_declarator() {
    let resolved = setup_declaration("int f(int ([4]));");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: f
          kind: function(int array) -> int
    ");
}

#[test]
fn test_complex_abstract_declarator_function() {
    let resolved = setup_declaration("int f5(int (*fp)(int));");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: f5
          kind: function(int function(int) -> pointer) -> int
    ");
}

#[test]
fn test_attribute_in_cast() {
    let resolved = setup_expr("(__attribute__((__noinline__)) int) 1");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Cast:
      - type_1
      - LiteralInt: 1
    ");
}

#[test]
fn test_gnu_statement_expression() {
    let resolved = setup_expr("({ int x = 1; x + 2; })");
    insta::assert_yaml_snapshot!(&resolved, @r"
    GnuStatementExpression:
      - CompoundStatement:
          - Declaration:
              specifiers:
                - int
              init_declarators:
                - name: x
                  initializer:
                    LiteralInt: 1
          - ExpressionStatement:
              BinaryOp:
                - Add
                - Ident: x
                - LiteralInt: 2
      - BinaryOp:
          - Add
          - Ident: x
          - LiteralInt: 2
  ");
}

#[test]
fn test_struct_member_multiple_declarators() {
    let resolved = setup_declaration("struct flowi6 { struct in6_addr saddr, daddr; };");
    insta::assert_yaml_snapshot!(&resolved, @r#"
  Declaration:
    specifiers:
      - "struct flowi6 { ... }"
    init_declarators: []
  "#);
}

#[test]
fn test_bitfield_declaration() {
    let resolved = setup_declaration("struct Test { int x: 8; unsigned y: 1; };");
    insta::assert_yaml_snapshot!(&resolved, @r#"
  Declaration:
    specifiers:
      - "struct Test { ... }"
    init_declarators: []
  "#);
}

#[test]
fn test_bitfield_with_mixed_members() {
    let resolved =
        setup_declaration("struct Mixed { int regular; int bitfield: 4; int another_regular; unsigned flag: 1; };");
    insta::assert_yaml_snapshot!(&resolved, @r#"
  Declaration:
    specifiers:
      - "struct Mixed { ... }"
    init_declarators: []
  "#);
}

#[test]
fn test_bitfield_with_large_width() {
    let resolved = setup_declaration("struct LargeBitfield { unsigned long value: 32; };");
    insta::assert_yaml_snapshot!(&resolved, @r#"
  Declaration:
    specifiers:
      - "struct LargeBitfield { ... }"
    init_declarators: []
  "#);
}

#[test]
fn test_designated_initializer_simple_array() {
    let resolved = setup_declaration("int arr[10] = { [5] = 42 };");
    insta::assert_yaml_snapshot!(&resolved, @r"
  Declaration:
    specifiers:
      - int
    init_declarators:
      - name: arr
        kind: array
        initializer:
          InitializerList:
            - LiteralInt: 42
  ");
}

#[test]
fn test_designated_initializer_range_syntax() {
    let resolved = setup_declaration("int arr[10] = { [1 ... 5] = 9 };");
    insta::assert_yaml_snapshot!(&resolved, @r"
  Declaration:
    specifiers:
      - int
    init_declarators:
      - name: arr
        kind: array
        initializer:
          InitializerList:
            - LiteralInt: 9
  ");
}

#[test]
fn test_designated_initializer_multiple_ranges() {
    let resolved = setup_declaration("int arr[20] = { [1 ... 5] = 9, [10 ... 15] = 42 };");
    insta::assert_yaml_snapshot!(&resolved, @r"
  Declaration:
    specifiers:
      - int
    init_declarators:
      - name: arr
        kind: array
        initializer:
          InitializerList:
            - LiteralInt: 9
            - LiteralInt: 42
  ");
}

#[test]
fn test_designated_initializer_mixed_single_and_range() {
    let resolved = setup_declaration("int arr[10] = { [0] = 1, [2 ... 5] = 9, [8] = 42 };");
    insta::assert_yaml_snapshot!(&resolved, @r"
  Declaration:
    specifiers:
      - int
    init_declarators:
      - name: arr
        kind: array
        initializer:
          InitializerList:
            - LiteralInt: 1
            - LiteralInt: 9
            - LiteralInt: 42
  ");
}

#[test]
fn test_designated_initializer_range_with_expressions() {
    let resolved = setup_declaration("int arr[10] = { [1 ... 2+3] = 9 };");
    insta::assert_yaml_snapshot!(&resolved, @r"
  Declaration:
    specifiers:
      - int
    init_declarators:
      - name: arr
        kind: array
        initializer:
          InitializerList:
            - LiteralInt: 9
  ");
}

#[test]
fn test_designated_initializer_struct_with_range() {
    let resolved = setup_declaration("struct T { int s[16]; int a; } lt2 = { { [1 ... 5] = 9, [6 ... 10] = 42 }, 1 };");
    insta::assert_yaml_snapshot!(&resolved, @r#"
  Declaration:
    specifiers:
      - "struct T { ... }"
    init_declarators:
      - name: lt2
        initializer:
          InitializerList:
            - InitializerList:
                - LiteralInt: 9
                - LiteralInt: 42
            - LiteralInt: 1
  "#);
}

#[test]
fn test_generic_selection_simple() {
    let resolved = setup_expr("_Generic(a, int: a_f)");
    insta::assert_yaml_snapshot!(&resolved, @r"
    GenericSelection:
      - Ident: a
      - - type_name: type_1
          result_expr:
            Ident: a_f
    ");
}

#[test]
fn test_generic_selection_with_multiple_associations() {
    let resolved = setup_expr("_Generic(a, int: a_f, const int: b_f)");
    insta::assert_yaml_snapshot!(&resolved, @r"
    GenericSelection:
      - Ident: a
      - - type_name: type_1
          result_expr:
            Ident: a_f
        - type_name: type_2
          result_expr:
            Ident: b_f
    ");
}

#[test]
fn test_generic_selection_with_default() {
    let resolved = setup_expr("_Generic(a, int: a_f, default: b_f)");
    insta::assert_yaml_snapshot!(&resolved, @r"
    GenericSelection:
      - Ident: a
      - - type_name: type_1
          result_expr:
            Ident: a_f
        - type_name: ~
          result_expr:
            Ident: b_f
    ");
}

#[test]
fn test_generic_selection_with_function_call() {
    let resolved = setup_expr("_Generic(a, int: a_f)()");
    insta::assert_yaml_snapshot!(&resolved, @r"
    FunctionCall:
      - GenericSelection:
          - Ident: a
          - - type_name: type_1
              result_expr:
                Ident: a_f
      - []
    ");
}

#[test]
fn test_generic_selection_with_qualified_type() {
    let resolved = setup_expr("_Generic(i, const int: 1/1, default: 0)");
    insta::assert_yaml_snapshot!(&resolved, @r"
    GenericSelection:
      - Ident: i
      - - type_name: type_1
          result_expr:
            BinaryOp:
              - Div
              - LiteralInt: 1
              - LiteralInt: 1
        - type_name: ~
          result_expr:
            LiteralInt: 0
    ");
}

#[test]
fn test_generic_selection_with_pointer_types() {
    let resolved = setup_expr("_Generic(ptr, int *:1, int * const:2, default:20)");
    insta::assert_yaml_snapshot!(&resolved, @r"
    GenericSelection:
      - Ident: ptr
      - - type_name: type_2
          result_expr:
            LiteralInt: 1
        - type_name: type_4
          result_expr:
            LiteralInt: 2
        - type_name: ~
          result_expr:
            LiteralInt: 20
    ");
}

#[test]
fn test_chained_assignment() {
    let resolved = setup_expr("a = b = c");
    insta::assert_yaml_snapshot!(&resolved, @r"
    BinaryOp:
      - Assign
      - Ident: a
      - BinaryOp:
          - Assign
          - Ident: b
          - Ident: c
    ");
}

#[test]
fn test_ternary_with_assignment() {
    let resolved = setup_expr("a ? b : c = 1");
    insta::assert_yaml_snapshot!(&resolved, @r"
    BinaryOp:
      - Assign
      - TernaryOp:
          - Ident: a
          - Ident: b
          - Ident: c
      - LiteralInt: 1
    ");
}

#[test]
fn test_ternary_with_assignment_in_middle_operand() {
    let resolved = setup_expr("a ? b = 1 : c");
    insta::assert_yaml_snapshot!(&resolved, @r"
    TernaryOp:
      - Ident: a
      - BinaryOp:
          - Assign
          - Ident: b
          - LiteralInt: 1
      - Ident: c
    ");
}

#[test]
fn test_chained_subtraction() {
    let resolved = setup_expr("a - b - c");
    insta::assert_yaml_snapshot!(&resolved, @r"
    BinaryOp:
      - Sub
      - BinaryOp:
          - Sub
          - Ident: a
          - Ident: b
      - Ident: c
    ");
}

#[test]
fn test_array_indexing_with_expression() {
    let resolved = setup_expr("a[b + c]");
    insta::assert_yaml_snapshot!(&resolved, @r"
    IndexAccess:
      - Ident: a
      - BinaryOp:
          - Add
          - Ident: b
          - Ident: c
    ");
}
