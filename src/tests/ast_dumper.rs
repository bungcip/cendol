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
fn test_dump_parsed_ast_simple() {
    let output = dump_parsed_ast("int main() { return 0; }");
    insta::assert_snapshot!(output, @r#"
    1: TranslationUnit(decls=[3])
    3: FunctionDef(ParsedFunctionDefData { specifiers: [TypeSpecifier(Int)], declarator: Function { inner: Identifier("main", TypeQualifiers(0x0)), params: [], is_variadic: false }, body: 4 })
    4: CompoundStatement(stmts=[6])
    5: LiteralInt(0, None)
    6: Return(5)
    "#);
}

#[test]
fn test_dump_parsed_ast_with_variables() {
    let output = dump_parsed_ast("int x = 42; int y = x + 5;");
    insta::assert_snapshot!(output, @r#"
    1: TranslationUnit(decls=[2, 4])
    2: Declaration(ParsedDeclarationData { specifiers: [TypeSpecifier(Int)], init_declarators: [ParsedInitDeclarator { declarator: Identifier("x", TypeQualifiers(0x0)), initializer: Some(3), span: SourceSpan(2199123918852) }] })
    3: LiteralInt(42, None)
    4: Declaration(ParsedDeclarationData { specifiers: [TypeSpecifier(Int)], init_declarators: [ParsedInitDeclarator { declarator: Identifier("y", TypeQualifiers(0x0)), initializer: Some(7), span: SourceSpan(2199174250512) }] })
    5: Ident(x)
    6: LiteralInt(5, None)
    7: BinaryOp(Add, 5, 6)
    "#
    );
}

#[test]
fn test_dump_parsed_ast_with_structs() {
    let output = dump_parsed_ast("struct Point { int x; int y; } p = {1, 2};");
    insta::assert_snapshot!(output, @r#"
    1: TranslationUnit(decls=[2])
    2: Declaration(ParsedDeclarationData { specifiers: [TypeSpecifier(Record(false, Some("Point"), Some(ParsedRecordDefData { tag: Some("Point"), members: Some([ParsedDeclarationData { specifiers: [TypeSpecifier(Int)], init_declarators: [ParsedInitDeclarator { declarator: Identifier("x", TypeQualifiers(0x0)), initializer: None, span: SourceSpan(2199040032787) }] }, ParsedDeclarationData { specifiers: [TypeSpecifier(Int)], init_declarators: [ParsedInitDeclarator { declarator: Identifier("y", TypeQualifiers(0x0)), initializer: None, span: SourceSpan(2199040032794) }] }]), is_union: false })))], init_declarators: [ParsedInitDeclarator { declarator: Identifier("p", TypeQualifiers(0x0)), initializer: Some(5), span: SourceSpan(2199191027743) }] })
    3: LiteralInt(1, None)
    4: LiteralInt(2, None)
    5: InitializerList([ParsedDesignatedInitializer { designation: [], initializer: 3 }, ParsedDesignatedInitializer { designation: [], initializer: 4 }])
    "#
    );
}

#[test]
fn test_dump_parsed_ast_with_enums() {
    let output = dump_parsed_ast("enum Color { RED, GREEN = 2, BLUE } c = RED;");
    insta::assert_snapshot!(output, @r#"
    1: TranslationUnit(decls=[2])
    2: Declaration(ParsedDeclarationData { specifiers: [TypeSpecifier(Enum(Some("Color"), Some([3, 5, 6])))], init_declarators: [ParsedInitDeclarator { declarator: Identifier("c", TypeQualifiers(0x0)), initializer: Some(7), span: SourceSpan(2199140696100) }] })
    3: EnumConstant(RED, auto)
    4: LiteralInt(2, None)
    5: EnumConstant(GREEN, 4)
    6: EnumConstant(BLUE, auto)
    7: Ident(RED)
    "#);
}

#[test]
fn test_dump_parsed_ast_with_strings() {
    let output = dump_parsed_ast("char* msg = \"Hello, world!\";");
    insta::assert_snapshot!(output, @r#"
    1: TranslationUnit(decls=[2])
    2: Declaration(ParsedDeclarationData { specifiers: [TypeSpecifier(Char)], init_declarators: [ParsedInitDeclarator { declarator: Pointer(TypeQualifiers(0x0), Some(Identifier("msg", TypeQualifiers(0x0)))), initializer: Some(3), span: SourceSpan(2199409131524) }] })
    3: LiteralString("Hello, world!")
    "#);
}

#[test]
fn test_dump_parsed_ast_with_floats() {
    let output = dump_parsed_ast("float pi = 3.14159; double e = 2.71828;");
    insta::assert_snapshot!(output, @r#"
    1: TranslationUnit(decls=[2, 4])
    2: Declaration(ParsedDeclarationData { specifiers: [TypeSpecifier(Float)], init_declarators: [ParsedInitDeclarator { declarator: Identifier("pi", TypeQualifiers(0x0)), initializer: Some(3), span: SourceSpan(2199224582150) }] })
    3: LiteralFloat(3.14159)
    4: Declaration(ParsedDeclarationData { specifiers: [TypeSpecifier(Double)], init_declarators: [ParsedInitDeclarator { declarator: Identifier("e", TypeQualifiers(0x0)), initializer: Some(5), span: SourceSpan(2199207804955) }] })
    5: LiteralFloat(2.71828)
    "#);
}

#[test]
fn test_dump_parsed_ast_with_chars() {
    let output = dump_parsed_ast("char c = 'a'; signed char sc = 'b'; unsigned char uc = 'c';");
    insta::assert_snapshot!(output, @r#"
    1: TranslationUnit(decls=[2, 4, 6])
    2: Declaration(ParsedDeclarationData { specifiers: [TypeSpecifier(Char)], init_declarators: [ParsedInitDeclarator { declarator: Identifier("c", TypeQualifiers(0x0)), initializer: Some(3), span: SourceSpan(2199140696069) }] })
    3: LiteralChar('a')
    4: Declaration(ParsedDeclarationData { specifiers: [TypeSpecifier(Signed), TypeSpecifier(Char)], init_declarators: [ParsedInitDeclarator { declarator: Identifier("sc", TypeQualifiers(0x0)), initializer: Some(5), span: SourceSpan(2199157473306) }] })
    5: LiteralChar('b')
    6: Declaration(ParsedDeclarationData { specifiers: [TypeSpecifier(Unsigned), TypeSpecifier(Char)], init_declarators: [ParsedInitDeclarator { declarator: Identifier("uc", TypeQualifiers(0x0)), initializer: Some(7), span: SourceSpan(2199157473330) }] })
    7: LiteralChar('c')
    "#);
}

#[test]
fn test_dump_parsed_ast_with_pointers() {
    let output = dump_parsed_ast("int x = 10; int* ptr = &x; int** ptr_ptr = &ptr;");
    insta::assert_snapshot!(output, @r#"
    1: TranslationUnit(decls=[2, 4, 7])
    2: Declaration(ParsedDeclarationData { specifiers: [TypeSpecifier(Int)], init_declarators: [ParsedInitDeclarator { declarator: Identifier("x", TypeQualifiers(0x0)), initializer: Some(3), span: SourceSpan(2199123918852) }] })
    3: LiteralInt(10, None)
    4: Declaration(ParsedDeclarationData { specifiers: [TypeSpecifier(Int)], init_declarators: [ParsedInitDeclarator { declarator: Pointer(TypeQualifiers(0x0), Some(Identifier("ptr", TypeQualifiers(0x0)))), initializer: Some(6), span: SourceSpan(2199191027727) }] })
    5: Ident(x)
    6: UnaryOp(AddrOf, 5)
    7: Declaration(ParsedDeclarationData { specifiers: [TypeSpecifier(Int)], init_declarators: [ParsedInitDeclarator { declarator: Pointer(TypeQualifiers(0x0), Some(Pointer(TypeQualifiers(0x0), Some(Identifier("ptr_ptr", TypeQualifiers(0x0)))))), initializer: Some(9), span: SourceSpan(2199308468254) }] })
    8: Ident(ptr)
    9: UnaryOp(AddrOf, 8)
    "#);
}

#[test]
fn test_dump_parsed_ast_with_arrays() {
    let output = dump_parsed_ast("int arr[5] = {1, 2, 3, 4, 5}; int* ptr_arr[3];");
    insta::assert_snapshot!(output, @r#"
    1: TranslationUnit(decls=[2, 10])
    2: Declaration(ParsedDeclarationData { specifiers: [TypeSpecifier(Int)], init_declarators: [ParsedInitDeclarator { declarator: Array(Identifier("arr", TypeQualifiers(0x0)), Expression { expr: 3, qualifiers: TypeQualifiers(0x0) }), initializer: Some(9), span: SourceSpan(2199425908740) }] })
    3: LiteralInt(5, None)
    4: LiteralInt(1, None)
    5: LiteralInt(2, None)
    6: LiteralInt(3, None)
    7: LiteralInt(4, None)
    8: LiteralInt(5, None)
    9: InitializerList([ParsedDesignatedInitializer { designation: [], initializer: 4 }, ParsedDesignatedInitializer { designation: [], initializer: 5 }, ParsedDesignatedInitializer { designation: [], initializer: 6 }, ParsedDesignatedInitializer { designation: [], initializer: 7 }, ParsedDesignatedInitializer { designation: [], initializer: 8 }])
    10: Declaration(ParsedDeclarationData { specifiers: [TypeSpecifier(Int)], init_declarators: [ParsedInitDeclarator { declarator: Pointer(TypeQualifiers(0x0), Some(Array(Identifier("ptr_arr", TypeQualifiers(0x0)), Expression { expr: 11, qualifiers: TypeQualifiers(0x0) }))), initializer: None, span: SourceSpan(2199224582177) }] })
    11: LiteralInt(3, None)
    "#);
}

#[test]
fn test_dump_parsed_ast_with_loops() {
    let output = dump_parsed_ast(
        "int main() { int i = 0; while (i < 10) { i++; } for (int j = 0; j < 5; j++) { printf(\"%d\", j); } do { i--; } while (i > 0); return 0; }",
    );
    insta::assert_snapshot!(output, @r#"
    1: TranslationUnit(decls=[3])
    3: FunctionDef(ParsedFunctionDefData { specifiers: [TypeSpecifier(Int)], declarator: Function { inner: Identifier("main", TypeQualifiers(0x0)), params: [], is_variadic: false }, body: 4 })
    4: CompoundStatement(stmts=[5, 14, 15, 36, 38])
    5: Declaration(ParsedDeclarationData { specifiers: [TypeSpecifier(Int)], init_declarators: [ParsedInitDeclarator { declarator: Identifier("i", TypeQualifiers(0x0)), initializer: Some(6), span: SourceSpan(2199107141649) }] })
    6: LiteralInt(0, None)
    7: Ident(i)
    8: LiteralInt(10, None)
    9: BinaryOp(Less, 7, 8)
    10: CompoundStatement(stmts=[11])
    11: ExpressionStatement(13)
    12: Ident(i)
    13: PostIncrement(12)
    14: While(ParsedWhileStmt { condition: 9, body: 10 })
    15: For(ParsedForStmt { init: Some(17), condition: Some(20), increment: Some(22), body: 23 })
    16: LiteralInt(0, None)
    17: Declaration(ParsedDeclarationData { specifiers: [TypeSpecifier(Int)], init_declarators: [ParsedInitDeclarator { declarator: Identifier("j", TypeQualifiers(0x0)), initializer: Some(16), span: SourceSpan(2199107141689) }] })
    18: Ident(j)
    19: LiteralInt(5, None)
    20: BinaryOp(Less, 18, 19)
    21: Ident(j)
    22: PostIncrement(21)
    23: CompoundStatement(stmts=[24])
    24: ExpressionStatement(28)
    25: Ident(printf)
    26: LiteralString("%d")
    27: Ident(j)
    28: FunctionCall(callee=25, args=[26, 27])
    29: CompoundStatement(stmts=[30])
    30: ExpressionStatement(32)
    31: Ident(i)
    32: PostDecrement(31)
    33: Ident(i)
    34: LiteralInt(0, None)
    35: BinaryOp(Greater, 33, 34)
    36: DoWhile(body=29, cond=35)
    37: LiteralInt(0, None)
    38: Return(37)
    "#);
}

#[test]
fn test_dump_parsed_ast_with_conditional() {
    let output = dump_parsed_ast(
        "int main() { int x = 10; if (x > 5) { printf(\"x is greater than 5\"); } else if (x < 5) { printf(\"x is less than 5\"); } else { printf(\"x is 5\"); } return 0; }",
    );
    insta::assert_snapshot!(output, @r#"
    1: TranslationUnit(decls=[3])
    3: FunctionDef(ParsedFunctionDefData { specifiers: [TypeSpecifier(Int)], declarator: Function { inner: Identifier("main", TypeQualifiers(0x0)), params: [], is_variadic: false }, body: 4 })
    4: CompoundStatement(stmts=[5, 29, 31])
    5: Declaration(ParsedDeclarationData { specifiers: [TypeSpecifier(Int)], init_declarators: [ParsedInitDeclarator { declarator: Identifier("x", TypeQualifiers(0x0)), initializer: Some(6), span: SourceSpan(2199123918865) }] })
    6: LiteralInt(10, None)
    7: Ident(x)
    8: LiteralInt(5, None)
    9: BinaryOp(Greater, 7, 8)
    10: CompoundStatement(stmts=[11])
    11: ExpressionStatement(14)
    12: Ident(printf)
    13: LiteralString("x is greater than 5")
    14: FunctionCall(callee=12, args=[13])
    15: Ident(x)
    16: LiteralInt(5, None)
    17: BinaryOp(Less, 15, 16)
    18: CompoundStatement(stmts=[19])
    19: ExpressionStatement(22)
    20: Ident(printf)
    21: LiteralString("x is less than 5")
    22: FunctionCall(callee=20, args=[21])
    23: CompoundStatement(stmts=[24])
    24: ExpressionStatement(27)
    25: Ident(printf)
    26: LiteralString("x is 5")
    27: FunctionCall(callee=25, args=[26])
    28: If(ParsedIfStmt { condition: 17, then_branch: 18, else_branch: Some(23) })
    29: If(ParsedIfStmt { condition: 9, then_branch: 10, else_branch: Some(28) })
    30: LiteralInt(0, None)
    31: Return(30)
    "#);
}

#[test]
fn test_dump_parsed_ast_with_switch() {
    let output = dump_parsed_ast(
        "int main() { int x = 2; switch (x) { case 1: printf(\"1\"); break; case 2: printf(\"2\"); break; default: printf(\"default\"); } return 0; }",
    );
    insta::assert_snapshot!(output, @r#"
    1: TranslationUnit(decls=[3])
    3: FunctionDef(ParsedFunctionDefData { specifiers: [TypeSpecifier(Int)], declarator: Function { inner: Identifier("main", TypeQualifiers(0x0)), params: [], is_variadic: false }, body: 4 })
    4: CompoundStatement(stmts=[5, 28, 30])
    5: Declaration(ParsedDeclarationData { specifiers: [TypeSpecifier(Int)], init_declarators: [ParsedInitDeclarator { declarator: Identifier("x", TypeQualifiers(0x0)), initializer: Some(6), span: SourceSpan(2199107141649) }] })
    6: LiteralInt(2, None)
    7: Ident(x)
    8: CompoundStatement(stmts=[14, 15, 21, 22, 27])
    9: LiteralInt(1, None)
    10: ExpressionStatement(13)
    11: Ident(printf)
    12: LiteralString("1")
    13: FunctionCall(callee=11, args=[12])
    14: Case(9, 10)
    15: Break
    16: LiteralInt(2, None)
    17: ExpressionStatement(20)
    18: Ident(printf)
    19: LiteralString("2")
    20: FunctionCall(callee=18, args=[19])
    21: Case(16, 17)
    22: Break
    23: ExpressionStatement(26)
    24: Ident(printf)
    25: LiteralString("default")
    26: FunctionCall(callee=24, args=[25])
    27: Default(23)
    28: Switch(7, 8)
    29: LiteralInt(0, None)
    30: Return(29)
    "#);
}

#[test]
fn test_dump_parser_ast() {
    let output = dump_parser_ast("int main() { return 0; }");
    insta::assert_snapshot!(output, @r"
    1: TranslationUnit(decls=2..2) (parser kind)
    2: Function(name=main, symbol=1, ty=TypeRef(base=19, class=Function, ptr=0, arr=None), params=[], body=4)
    3: LiteralString(main)
    4: CompoundStatement(stmts=5..5)
    5: Return(6)
    6: LiteralInt(0, None)
    ");
}

#[test]
fn test_dump_parser_ast_with_functions() {
    let output = dump_parser_ast("int add(int a, int b) { return a + b; } int main() { return add(2, 3); }");
    insta::assert_snapshot!(output, @r"
    1: TranslationUnit(decls=2..3) (parser kind)
    2: Function(name=add, symbol=1, ty=TypeRef(base=19, class=Function, ptr=0, arr=None), params=5..6, body=7)
    3: Function(name=main, symbol=5, ty=TypeRef(base=20, class=Function, ptr=0, arr=None), params=[], body=13)
    4: LiteralString(add)
    5: Param(symbol=3, ty=QualType(8))
    6: Param(symbol=4, ty=QualType(8))
    7: CompoundStatement(stmts=8..8)
    8: Return(9)
    9: BinaryOp(Add, 10, 11)
    10: Ident(a)
    11: Ident(b)
    12: LiteralString(main)
    13: CompoundStatement(stmts=14..14)
    14: Return(15)
    15: FunctionCall(callee=16, args=17..18)
    16: Ident(add)
    17: LiteralInt(2, None)
    18: LiteralInt(3, None)
    ");
}

#[test]
fn test_dump_type_registry() {
    let output = dump_type_registry("int main() { int x = 42; float y = 3.14; return x + (int)y; }");
    insta::assert_snapshot!(output, @r"
    === TypeRegistry (Used TypeRefs) ===
    TypeRef(8): int
    TypeRef(14): float
    TypeRef(19): int()
    ");
}

#[test]
fn test_dump_type_registry_with_complex_types() {
    let output = dump_type_registry(
        "struct Point { int x; int y; }; int main() { struct Point p = {1, 2}; int *ptr = &p.x; float arr[10]; return 0; }",
    );
    insta::assert_snapshot!(output, @r"
    === TypeRegistry (Used TypeRefs) ===
    TypeRef(8): int
    TypeRef(20): int()
    TypeRef(19): struct Point
    TypeRef(8): int*
    TypeRef(14): float[10]
    ");
}

#[test]
fn test_dump_parser_ast_with_designated_initializers() {
    let output = dump_parser_ast(
        "struct Point { int x; int y; }; int main() { struct Point p = {.x = 1, .y = 2}; int arr[5] = {[1] = 10, [3] = 30}; return 0; }",
    );
    insta::assert_snapshot!(output, @r#"
    1: TranslationUnit(decls=2..3) (parser kind)
    2: RecordDecl(name=Some("Point"), ty=1048595, is_union=false, members=4..5)
    3: Function(name=main, symbol=2, ty=TypeRef(base=20, class=Function, ptr=0, arr=None), params=[], body=7)
    4: FieldDecl(name=Some("x"), ty=Int)
    5: FieldDecl(name=Some("y"), ty=Int)
    6: LiteralString(main)
    7: CompoundStatement(stmts=8..10)
    8: VarDecl(name=p, ty=TypeRef(base=19, class=Record, ptr=0, arr=None), storage=None)
    9: VarDecl(name=arr, ty=TypeRef(base=8, class=Array, ptr=0, arr=Some(5)), storage=None)
    10: Return(28)
    11: InitializerList(inits=12..13)
    12: InitializerItem(.x = 14)
    13: InitializerItem(.y = 16)
    14: LiteralInt(1, None)
    15: Designator(.x)
    16: LiteralInt(2, None)
    17: Designator(.y)
    18: LiteralInt(5, None)
    19: InitializerList(inits=20..21)
    20: InitializerItem([24] = 22)
    21: InitializerItem([27] = 25)
    22: LiteralInt(10, None)
    23: Designator([24])
    24: LiteralInt(1, None)
    25: LiteralInt(30, None)
    26: Designator([27])
    27: LiteralInt(3, None)
    28: LiteralInt(0, None)
    "#);
}
