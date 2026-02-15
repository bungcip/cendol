use super::semantic_common::setup_lowering;
use crate::ast::{Ast, NodeKind, NodeRef};
use crate::semantic::{QualType, SymbolTable, TypeQualifiers, TypeRegistry};
use serde::Serialize;

#[derive(Debug, Serialize)]
enum ResolvedAstNode {
    TranslationUnit(Vec<ResolvedAstNode>),
    VarDecl {
        name: String,
        ty: String,
        init: Option<Box<ResolvedAstNode>>,
        alignment: Option<u16>,
    },
    RecordDecl {
        name: String,
        members: Vec<ResolvedAstNode>,
    },
    FieldDecl {
        name: String,
        ty: String,
    },
    EnumDecl {
        name: String,
        members: Vec<ResolvedAstNode>,
    },
    EnumMember {
        name: String,
        value: i64,
    },
    Function {
        name: String,
        body: Box<ResolvedAstNode>,
    },
    FunctionCall {
        callee: Box<ResolvedAstNode>,
        args: Vec<ResolvedAstNode>,
    },
    BinaryOp {
        op: String,
        lhs: Box<ResolvedAstNode>,
        rhs: Box<ResolvedAstNode>,
    },
    CompoundStatement(Vec<ResolvedAstNode>),
    Return(Option<Box<ResolvedAstNode>>),
    LiteralInt(i64),
    Ident(String),
    // Fallback for nodes we haven't explicitly mapped yet
    #[serde(untagged)]
    Other(String),
}

fn resolve_node(ast: &Ast, registry: &TypeRegistry, symbol_table: &SymbolTable, node_ref: NodeRef) -> ResolvedAstNode {
    let kind = ast.get_kind(node_ref);

    match kind {
        NodeKind::TranslationUnit(data) => {
            let nodes = data
                .decl_start
                .range(data.decl_len)
                .map(|child_ref| resolve_node(ast, registry, symbol_table, child_ref))
                .collect();
            ResolvedAstNode::TranslationUnit(nodes)
        }
        NodeKind::VarDecl(data) => ResolvedAstNode::VarDecl {
            name: data.name.as_str().to_string(),
            ty: display_qual_type(registry, data.ty),
            init: data
                .init
                .map(|r| Box::new(resolve_node(ast, registry, symbol_table, r))),
            alignment: data.alignment,
        },
        NodeKind::RecordDecl(data) => {
            let members = data
                .member_start
                .range(data.member_len)
                .map(|child_ref| resolve_node(ast, registry, symbol_table, child_ref))
                .collect();
            ResolvedAstNode::RecordDecl {
                name: data
                    .name
                    .map(|n| n.as_str().to_string())
                    .unwrap_or_else(|| "<anon>".to_string()),
                members,
            }
        }
        NodeKind::FieldDecl(data) => ResolvedAstNode::FieldDecl {
            name: data
                .name
                .map(|n| n.as_str().to_string())
                .unwrap_or_else(|| "<anon>".to_string()),
            ty: display_qual_type(registry, data.ty),
        },
        NodeKind::EnumDecl(data) => {
            let members = data
                .member_start
                .range(data.member_len)
                .map(|child_ref| resolve_node(ast, registry, symbol_table, child_ref))
                .collect();
            ResolvedAstNode::EnumDecl {
                name: data
                    .name
                    .map(|n| n.as_str().to_string())
                    .unwrap_or_else(|| "<anon>".to_string()),
                members,
            }
        }
        NodeKind::EnumMember(data) => ResolvedAstNode::EnumMember {
            name: data.name.as_str().to_string(),
            value: data.value,
        },
        NodeKind::Function(data) => {
            let symbol = symbol_table.get_symbol(data.symbol);
            ResolvedAstNode::Function {
                name: symbol.name.as_str().to_string(),
                body: Box::new(resolve_node(ast, registry, symbol_table, data.body)),
            }
        }
        NodeKind::FunctionCall(call) => {
            let args = call
                .arg_start
                .range(call.arg_len)
                .map(|child_ref| resolve_node(ast, registry, symbol_table, child_ref))
                .collect();
            ResolvedAstNode::FunctionCall {
                callee: Box::new(resolve_node(ast, registry, symbol_table, call.callee)),
                args,
            }
        }
        NodeKind::BinaryOp(op, lhs, rhs) => ResolvedAstNode::BinaryOp {
            op: format!("{:?}", op),
            lhs: Box::new(resolve_node(ast, registry, symbol_table, *lhs)),
            rhs: Box::new(resolve_node(ast, registry, symbol_table, *rhs)),
        },
        NodeKind::CompoundStatement(data) => {
            let stmts = data
                .stmt_start
                .range(data.stmt_len)
                .map(|child_ref| resolve_node(ast, registry, symbol_table, child_ref))
                .collect();
            ResolvedAstNode::CompoundStatement(stmts)
        }
        NodeKind::Return(expr) => {
            ResolvedAstNode::Return(expr.map(|r| Box::new(resolve_node(ast, registry, symbol_table, r))))
        }
        NodeKind::Literal(literal) => match literal {
            crate::ast::literal::Literal::Int { val, .. } => ResolvedAstNode::LiteralInt(*val),
            _ => panic!("Not implemented for this literal type"),
        },
        NodeKind::Ident(name, _) => ResolvedAstNode::Ident(name.as_str().to_string()),
        _ => ResolvedAstNode::Other(format!("{:?}", kind)),
    }
}

fn display_qual_type(registry: &TypeRegistry, qt: QualType) -> String {
    let mut s = String::new();
    if qt.is_const() {
        s.push_str("const ");
    }
    if qt.qualifiers().contains(TypeQualifiers::VOLATILE) {
        s.push_str("volatile ");
    }
    if qt.qualifiers().contains(TypeQualifiers::RESTRICT) {
        s.push_str("restrict ");
    }
    if qt.qualifiers().contains(TypeQualifiers::ATOMIC) {
        s.push_str("_Atomic ");
    }

    let ty_ref = qt.ty();
    let type_cow = registry.get(ty_ref);
    use crate::semantic::TypeKind;
    let kind = &type_cow.kind;

    match kind {
        TypeKind::Pointer { pointee } => {
            let pointee_qt = *pointee;
            let inner = display_qual_type(registry, pointee_qt);
            s.push_str(&format!("{} *", inner));
        }
        _ => s.push_str(&format!("{}", kind)),
    }
    s.trim().to_string()
}

#[test]
fn test_const_pointer_init() {
    let (ast, registry, symbol_table) = setup_lowering("const int * const * volatile p;");
    let root = ast.get_root();
    let resolved = resolve_node(&ast, &registry, &symbol_table, root);
    insta::assert_yaml_snapshot!(resolved, @"
    TranslationUnit:
      - VarDecl:
          name: p
          ty: volatile const const int * *
          init: ~
          alignment: ~
    ");
}

#[test]
fn test_record_decl_members_populated() {
    let (ast, registry, symbol_table) = setup_lowering(
        r#"
        struct Point {
            int x;
            int y;
        };
    "#,
    );
    let root = ast.get_root();
    let resolved = resolve_node(&ast, &registry, &symbol_table, root);
    insta::assert_yaml_snapshot!(resolved, @"
    TranslationUnit:
      - RecordDecl:
          name: Point
          members:
            - FieldDecl:
                name: x
                ty: int
            - FieldDecl:
                name: y
                ty: int
    ");
}

#[test]
fn test_enum_decl_members_populated() {
    let (ast, registry, symbol_table) = setup_lowering(
        r#"
        enum Color {
            RED,
            GREEN,
            BLUE
        };
    "#,
    );

    let root = ast.get_root();
    let resolved = resolve_node(&ast, &registry, &symbol_table, root);
    insta::assert_yaml_snapshot!(resolved, @"
    TranslationUnit:
      - EnumDecl:
          name: Color
          members:
            - EnumMember:
                name: RED
                value: 0
            - EnumMember:
                name: GREEN
                value: 1
            - EnumMember:
                name: BLUE
                value: 2
    ");
}

#[test]
fn test_struct_member_qualifiers_preserved() {
    let (ast, registry, symbol_table) = setup_lowering(
        r#"
        struct S {
            const int x;
            volatile int *y;
        };
    "#,
    );

    let root = ast.get_root();
    let resolved = resolve_node(&ast, &registry, &symbol_table, root);
    insta::assert_yaml_snapshot!(resolved, @"
    TranslationUnit:
      - RecordDecl:
          name: S
          members:
            - FieldDecl:
                name: x
                ty: const int
            - FieldDecl:
                name: y
                ty: volatile int *
    ");
}

#[test]
fn test_function_call_args_contiguity() {
    let (ast, registry, symbol_table) = setup_lowering(
        r#"
        int add(int a, int b) { return a + b; }
        int main() {
            return add(1 + 2, 3);
        }
    "#,
    );

    let root = ast.get_root();
    let resolved = resolve_node(&ast, &registry, &symbol_table, root);
    insta::assert_yaml_snapshot!(resolved, @"
    TranslationUnit:
      - Function:
          name: add
          body:
            CompoundStatement:
              - Return:
                  BinaryOp:
                    op: Add
                    lhs:
                      Ident: a
                    rhs:
                      Ident: b
      - Function:
          name: main
          body:
            CompoundStatement:
              - Return:
                  FunctionCall:
                    callee:
                      Ident: add
                    args:
                      - BinaryOp:
                          op: Add
                          lhs:
                            LiteralInt: 1
                          rhs:
                            LiteralInt: 2
                      - LiteralInt: 3
    ");
}

#[test]
fn test_alignment_specifier() {
    let (ast, registry, symbol_table) = setup_lowering(
        r#"
        _Alignas(8) int x;
        _Alignas(double) char c;
        _Alignas(16) _Alignas(8) int y;
    "#,
    );

    let root = ast.get_root();
    let resolved = resolve_node(&ast, &registry, &symbol_table, root);
    insta::assert_yaml_snapshot!(resolved, @"
    TranslationUnit:
      - VarDecl:
          name: x
          ty: int
          init: ~
          alignment: 8
      - VarDecl:
          name: c
          ty: char
          init: ~
          alignment: 8
      - VarDecl:
          name: y
          ty: int
          init: ~
          alignment: 16
    ");
}
