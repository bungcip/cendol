#![cfg(test)]
use crate::ast::dumper::AstDumper;
use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils;

fn dump_parsed_ast(source: &str) -> String {
    let phase = CompilePhase::Parse;
    let (_, out) = test_utils::run_pipeline(source, phase);
    let mut out = out.unwrap();
    let first = out.units.first_mut().unwrap();
    let artifact = first.1;
    let ast = artifact.parsed_ast.as_ref().unwrap();
    AstDumper::dump_parsed_ast(ast).to_string()
}

fn dump_parser_ast(source: &str) -> String {
    let phase = CompilePhase::SemanticLowering;
    let (_, out) = test_utils::run_pipeline(source, phase);
    let mut out = out.unwrap();
    let first = out.units.first_mut().unwrap();
    let artifact = first.1;
    let ast = artifact.ast.as_ref().unwrap();
    let symbol_table = artifact.symbol_table.as_ref().unwrap();
    AstDumper::dump_parser(ast, Some(symbol_table)).to_string()
}

fn dump_type_registry(source: &str) -> String {
    let phase = CompilePhase::SemanticLowering;
    let (_, out) = test_utils::run_pipeline(source, phase);
    let mut out = out.unwrap();
    let first = out.units.first_mut().unwrap();
    let artifact = first.1;
    let ast = artifact.ast.as_ref().unwrap();
    let type_registry = artifact.type_registry.as_ref().unwrap();
    AstDumper::dump_type_registry(ast, type_registry).to_string()
}

#[test]
fn test_parsed_ast_ternary() {
    let output = dump_parsed_ast("int f() { return 1 ? 2 : 3; }");
    insta::assert_snapshot!(output);
}

#[test]
fn test_parsed_ast_access() {
    let output = dump_parsed_ast("struct S { int a; }; int f() { struct S s; struct S *p; int arr[10]; return s.a + p->a + arr[0]; }");
    insta::assert_snapshot!(output);
}

#[test]
fn test_parsed_ast_sizeof_alignof() {
    let output = dump_parsed_ast("int f() { return (int)3.14 + sizeof(int) + sizeof(1) + _Alignof(int); }");
    insta::assert_snapshot!(output);
}

#[test]
fn test_parsed_ast_compound_literal() {
    let output = dump_parsed_ast("struct S { int a; }; int f() { return ((struct S){1}).a; }");
    insta::assert_snapshot!(output);
}

#[test]
fn test_parsed_ast_gnu_stmt_expr() {
    let output = dump_parsed_ast("int f() { return ({ int x = 1; x; }); }");
    insta::assert_snapshot!(output);
}

#[test]
fn test_parsed_ast_builtins() {
    let output = dump_parsed_ast("
        typedef __builtin_va_list va_list;
        int f(int x, ...) {
            va_list ap;
            __builtin_va_start(ap, x);
            int y = __builtin_va_arg(ap, int);
            __builtin_va_end(ap);
            __builtin_va_copy(ap, ap);
            return y;
        }
        struct S { int a; };
        int g() { return __builtin_offsetof(struct S, a); }
    ");
    insta::assert_snapshot!(output);
}

#[test]
fn test_parsed_ast_generic() {
    let output = dump_parsed_ast("int f() { return _Generic(1, int: 1, default: 0); }");
    insta::assert_snapshot!(output);
}

#[test]
fn test_parsed_ast_labels() {
    let output = dump_parsed_ast("int f() { label: goto label; }");
    insta::assert_snapshot!(output);
}

#[test]
fn test_parsed_ast_static_assert() {
    let output = dump_parsed_ast("_Static_assert(1, \"msg\");");
    insta::assert_snapshot!(output);
}

#[test]
fn test_parsed_ast_empty_stmt() {
    let output = dump_parsed_ast("void f() { ; }");
    insta::assert_snapshot!(output);
}

#[test]
fn test_parser_ast_control_flow() {
    let output = dump_parser_ast("void f() { if (1) {} while(0) {} do {} while(0); for(;;) {} }");
    insta::assert_snapshot!(output);
}

#[test]
fn test_parser_ast_switch() {
    let output = dump_parser_ast("void f() { switch(1) { case 1: break; default: continue; } }");
    insta::assert_snapshot!(output);
}

#[test]
fn test_parser_ast_ops() {
    let output = dump_parser_ast("void f() { int a = 1; int b = 2; int c; c = a + b; c = a > b ? a : b; c += 1; a++; ++b; }");
    insta::assert_snapshot!(output);
}

#[test]
fn test_parser_ast_sizeof_alignof() {
    let output = dump_parser_ast("void f() { int a = (int)1.0; int s = sizeof(int) + sizeof(a) + _Alignof(int); }");
    insta::assert_snapshot!(output);
}

#[test]
fn test_parser_ast_access() {
    let output = dump_parser_ast("struct S { int a; }; void f() { struct S s; struct S *p; int arr[10]; int x = s.a + p->a + arr[0]; }");
    insta::assert_snapshot!(output);
}

#[test]
fn test_parser_ast_compound_literal() {
    let output = dump_parser_ast("struct S { int a; }; void f() { struct S s = (struct S){1}; }");
    insta::assert_snapshot!(output);
}

#[test]
fn test_parser_ast_generic() {
    let output = dump_parser_ast("void f() { int x = _Generic(1, int: 1, default: 0); }");
    insta::assert_snapshot!(output);
}

#[test]
fn test_parser_ast_gnu_stmt_expr() {
    let output = dump_parser_ast("void f() { int x = ({ int y = 1; y; }); }");
    insta::assert_snapshot!(output);
}

#[test]
fn test_parser_ast_builtin_offsetof() {
    let output = dump_parser_ast("struct S { int a; }; void f() { int x = __builtin_offsetof(struct S, a); }");
    insta::assert_snapshot!(output);
}

#[test]
fn test_parser_ast_static_assert() {
    let output = dump_parser_ast("_Static_assert(1, \"msg\");");
    insta::assert_snapshot!(output);
}

#[test]
fn test_parser_ast_labels() {
    let output = dump_parser_ast("void f() { L: goto L; }");
    insta::assert_snapshot!(output);
}

#[test]
fn test_type_registry_complex() {
    let output = dump_type_registry("
        typedef struct Point { int x, y; } Point;
        enum Color { RED, GREEN, BLUE };
        void f(int n) {
            _Complex double c;
            int arr[n]; // VLA
            Point p;
            enum Color color;
        }
        void g(int x, ...); // Variadic
    ");
    insta::assert_snapshot!(output);
}

#[test]
fn test_atomic_ops_and_case_range() {
    // __atomic_load_n etc are parser builtins that map to ParsedNodeKind::AtomicOp
    let output_parsed = dump_parsed_ast("
        void f() {
            int a = 0;
            int b = __atomic_load_n(&a, 0);
            switch(a) {
                case 1 ... 5: break;
            }
        }
    ");
    insta::assert_snapshot!(output_parsed);

    let output_parser = dump_parser_ast("
        void f() {
            int a = 0;
            // Semantic lowering currently doesn't support atomic ops fully or might convert them differently?
            // But let's check CaseRange.
            switch(a) {
                case 1 ... 5: break;
            }
        }
    ");
    insta::assert_snapshot!(output_parser);
}
