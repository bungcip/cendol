//! Tests for parser functionality
//!
//! This module tests the parser's ability to correctly parse C source code
//! and generate the expected Abstract Syntax Tree (AST) structures.

use cendol::parser::Parser;
use cendol::parser::ast::{Decl, FuncDecl, Stmt, TranslationUnit};
use cendol::test_utils::{create_file_manager, create_preprocessor};
use thin_vec::ThinVec;

macro_rules! assert_stmt_expr {
    ($stmt:expr, $pat:pat) => {
        assert!(
            matches!($stmt, Stmt::Expr(ref expr) if matches!(**expr, $pat)),
            "Expected stmt to match pattern `{}`",
            stringify!($pat)
        );
    };
}
macro_rules! assert_decl_full {
    ($stmts:expr, $idx:expr, $expected_name:expr, $expected_kind:pat, $expr_pat:pat) => {{
        assert!(
            matches!(&$stmts[$idx], Stmt::Declaration(..)),
            "Expected declaration at stmts[{}]",
            $idx
        );

        if let Stmt::Declaration(Decl::VarGroup(ty, declarators)) = &$stmts[$idx] {
            assert!(
                !declarators.is_empty(),
                "Expected at least one declarator at stmts[{}]",
                $idx
            );

            let decl = &declarators[0];

            // cek nama
            assert_eq!(
                decl.name.unwrap().as_str(),
                $expected_name,
                "Unexpected declarator name at stmts[{}]",
                $idx
            );

            // cek tipe
            assert!(
                matches!(ty.kind, $expected_kind),
                "Unexpected type for declarator `{}` at stmts[{}]: got {:?}",
                decl.name.unwrap(),
                $idx,
                ty
            );

            // cek initializer -> Expr pattern
            match &decl.init {
                Some(expr) => {
                    assert!(
                        matches!(**expr, $expr_pat),
                        "Initializer expression for `{}` did not match `{}` at stmts[{}]: got {:?}",
                        decl.name.unwrap(),
                        stringify!($expr_pat),
                        $idx,
                        **expr
                    );
                }
                other => panic!(
                    "Expected expression initializer for `{}` at stmts[{}], found {:?}",
                    decl.name.unwrap(),
                    $idx,
                    other
                ),
            }
        } else {
            panic!("Expected Stmt::Declaration at stmts[{}]", $idx);
        }
    }};
}

macro_rules! assert_type_spec {
    // Case 1: with explicit declarators list (for arrays, pointers, etc.)
    ($input:expr, $type_keyword:expr, [$(($name:expr, $ptr:expr, $arr:expr)),+ $(,)?]) => {{
        let stmts = parse_c_body($input);
        if let Stmt::Declaration(Decl::VarGroup(ty, declarators)) = &stmts[0] {
            assert!(
                matches!(
                    ty.kind,
                    TypeSpecKind::Builtin(ref k) if *k == $type_keyword
                ),
                "Type keyword mismatch: expected {:?}, got {:?}",
                $type_keyword,
                ty.kind
            );

            let expected = vec![$(($name, $ptr, $arr)),+];
            assert_eq!(
                declarators.len(),
                expected.len(),
                "Number of declarators mismatch: expected {}, got {}",
                expected.len(),
                declarators.len()
            );

            for ((expected_name, expected_ptr, expected_arr), decl) in expected.iter().zip(declarators.iter()) {
                assert_eq!(
                    decl.name.unwrap().as_str(),
                    *expected_name,
                    "Declarator name mismatch: expected {}, got {}",
                    expected_name,
                    decl.name.unwrap().as_str()
                );
                assert_eq!(
                    decl.pointer_depth, *expected_ptr,
                    "Pointer depth mismatch for {}: expected {}, got {}",
                    expected_name, expected_ptr, decl.pointer_depth
                );
                assert_eq!(
                    decl.array_sizes.len(), *expected_arr,
                    "Array size count mismatch for {}: expected {}, got {}",
                    expected_name, expected_arr, decl.array_sizes.len()
                );
            }
        } else {
            panic!("Expected Declaration");
        }
    }};

    // Case 2: simple case (just check the first declarator)
    ($input:expr, $type_keyword:expr) => {{
        let stmts = parse_c_body($input);
        if let Stmt::Declaration(Decl::VarGroup(ty, declarators)) = &stmts[0] {
            assert_eq!(declarators[0].name.unwrap().as_str(), "x");
            assert!(
                matches!(
                    ty.kind,
                    TypeSpecKind::Builtin(ref k) if *k == $type_keyword
                ),
                "Type keyword mismatch: expected {:?}, got {:?}",
                $type_keyword,
                ty.kind
            );
        } else {
            panic!("Expected Declaration");
        }
    }};

    // Case 3: simple case with storage class
    ($input:expr, $type_keyword:expr, $storage:expr) => {{
        let stmts = parse_c_body($input);
        if let Stmt::Declaration(Decl::VarGroup(ty, declarators)) = &stmts[0] {
            assert_eq!(declarators[0].name.unwrap().as_str(), "x");
            assert!(
                matches!(
                    ty.kind,
                    TypeSpecKind::Builtin(ref k) if *k == $type_keyword
                ),
                "Type keyword mismatch: expected {:?}, got {:?}",
                $type_keyword,
                ty.kind
            );
            assert_eq!(ty.storage, $storage);
        } else {
            panic!("Expected Declaration");
        }
    }};

    // Case 4: simple case with qualifiers
    ($input:expr, $type_keyword:expr, $storage:expr, $qualifiers:expr) => {{
        let stmts = parse_c_body($input);
        if let Stmt::Declaration(Decl::VarGroup(ty, declarators)) = &stmts[0] {
            assert_eq!(declarators[0].name.unwrap().as_str(), "x");
            assert!(
                matches!(
                    ty.kind,
                    TypeSpecKind::Builtin(ref k) if *k == $type_keyword
                ),
                "Type keyword mismatch: expected {:?}, got {:?}",
                $type_keyword,
                ty.kind
            );
            assert_eq!(ty.storage, $storage);
            assert_eq!(ty.qualifiers, $qualifiers);
        } else {
            panic!("Expected Declaration");
        }
    }};
}




/// Test configuration constants
mod config {
    pub const TEST_FILENAME: &str = "test.c";
}

/// Helper function to parse C code and return the AST
fn parse_c_code(input: &str) -> Result<TranslationUnit, Box<dyn std::error::Error>> {
    let mut fm = create_file_manager();
    let pp = create_preprocessor();
    let tokens = pp.preprocess_virtual_file(&mut fm, input, config::TEST_FILENAME)?;
    let mut parser = Parser::new(tokens)?;
    let ast = parser.parse()?;
    Ok(ast)
}

/// helper function to parse C function body and return the statements
fn parse_c_body(input: &str) -> ThinVec<Stmt> {
    let input = format!(
        "
        int func1() {{ return 0; }}
        int func2(int a, int b, int c) {{ return 0; }}

        void c_body(int x, int y, int a, int b, int c, int arr[], struct S obj, struct S *ptr, int *p)
        {{
            {input}
        }}
    ");

    let mut fm = create_file_manager();
    let pp = create_preprocessor();
    let tokens = pp
        .preprocess_virtual_file(&mut fm, &input, config::TEST_FILENAME)
        .unwrap();
    let mut parser = Parser::new(tokens).unwrap();
    let ast = parser.parse().unwrap();
    let func_def = ast
        .globals
        .iter()
        .find_map(|d| {
            if let Decl::Func(f) = d {
                if f.name.as_str() == "c_body" {
                    Some(f)
                } else {
                    None
                }
            } else {
                None
            }
        })
        .unwrap();
    // Note: globals field is still present in AST, but will be removed in semantic analysis
    func_def.body.clone().unwrap()
}

#[cfg(test)]
mod tests {
    use super::parse_c_code;
    use crate::parse_c_body;
    use cendol::parser::ast::{Decl, Declarator, Expr, FuncDecl, Initializer, Stmt};
    use cendol::types::{TypeKeywordMask as TypeKeyword, TypeSpecKind, StorageClass, TypeQualifiers};

    #[test]
    fn test_return_stmt() {
        let input = "return 0;";
        let stmts = parse_c_body(input);

        assert!(matches!(&stmts[0], Stmt::Return(..)));
    }

    /// Test parsing of programs with control flow (if-else statements)
    #[test]
    fn test_control_flow() {
        let input = "if (1) return 1; else return 0;";
        let stmts = parse_c_body(input);

        assert!(matches!(&stmts[0], Stmt::If(..)));
        if let Stmt::If(cond, then_block, else_block) = &stmts[0] {
            assert!(matches!(**cond, Expr::Number(..)));
            assert!(matches!(**then_block, Stmt::Return(..)));

            let else_block = *else_block.clone().unwrap();
            assert!(matches!(else_block, Stmt::Return(..)));
        }
    }

    /// Test parsing of programs with _Bool variable declarations
    #[test]
    fn test_bool_declaration() {
        let input = "_Bool roti_bakar = 1;";
        let stmts = parse_c_body(input);

        // Debug: print the actual AST structure
        println!("Actual AST for test_bool_declaration:");
        for (i, stmt) in stmts.iter().enumerate() {
            println!("stmt[{}]: {:?}", i, stmt);
        }

        assert_decl_full!(
            stmts,
            0,
            "roti_bakar",
            TypeSpecKind::Builtin(_),
            Expr::Number(..)
        )
    }

    /// Test parsing of switch statements
    #[test]
    fn test_switch_statement() {
        let input = r#"
            switch (x) {
                case 1:
                    y = 1;
                    break;
                case 2:
                    y = 2;
                    break;
                default:
                    y = 0;
            }
        "#;
        let stmts = parse_c_body(input);
        assert!(matches!(&stmts[0], Stmt::Switch(..)));

        if let Stmt::Switch(cond, body) = &stmts[0] {
            assert!(matches!(**cond, Expr::Variable(..)));
            if let Stmt::Block(stmts) = &**body {
                assert_eq!(stmts.len(), 5);
                assert!(matches!(&stmts[0], Stmt::Case(..)));
                assert!(matches!(&stmts[1], Stmt::Break));
                assert!(matches!(&stmts[2], Stmt::Case(..)));
                assert!(matches!(&stmts[3], Stmt::Break));
                assert!(matches!(&stmts[4], Stmt::Default(..)));
            } else {
                panic!("Expected switch body to be a block");
            }
        } else {
            panic!("Expected Stmt::Switch");
        }
    }

    /// Test parsing of multiple declarators in a single declaration
    #[test]
    fn test_multiple_declarators() {
        let input = "int x, *p, **pp;";
        let stmts = parse_c_body(input);

        if let Stmt::Declaration(Decl::VarGroup(ty, declarators)) = &stmts[0] {
            assert_eq!(declarators.len(), 3);
            // Check first declarator: int x
            assert_eq!(declarators[0].name.unwrap().as_str(), "x");
            assert_eq!(declarators[0].pointer_depth, 0);
            assert!(
                matches!(ty.kind, TypeSpecKind::Builtin(ref k) if *k == TypeKeyword::INT.bits())
            );

            // Check second declarator: int *p
            assert_eq!(declarators[1].name.unwrap().as_str(), "p");
            assert_eq!(declarators[1].pointer_depth, 1);
            assert!(
                matches!(ty.kind, TypeSpecKind::Builtin(ref k) if *k == TypeKeyword::INT.bits())
            );

            // Check third declarator: int **pp
            assert_eq!(declarators[2].name.unwrap().as_str(), "pp");
            assert_eq!(declarators[2].pointer_depth, 2);
            assert!(
                matches!(ty.kind, TypeSpecKind::Builtin(ref k) if *k == TypeKeyword::INT.bits())
            );
        } else {
            panic!("Expected a declaration statement");
        }
    }

    #[test]
    fn test_all_expressions() {
        let input = r#"
            // Primary
            x;
            42;
            'a';
            "hello";
            (x + 1);

            // Postfix
            arr[2];
            func1();
            func2(a, b, c);
            obj.member;
            ptr->member;
            x++;
            y--;
            (int){1, 2}; // compound literal (C99)

            // unary
            ++x;
            --y;
            &x;
            *p;
            +x;
            -x;
            ~x;
            !x;
            sizeof x;
            sizeof(int);
            _Alignof(int);

            // cast
            (int)x;

            // Multiplicative
            a *b;
            a / b;
            a % b;

            // Additive
            a + b;
            a - b;

            // Relational
            a << 2;
            b >> 1;
            a < b;
            a > b;
            a <= b;
            a >= b;

            // Equality
            a == b;
            a != b;

            // Bitwise
            a & b;
            a ^ b;
            a | b;

            // Logical
            a &&b;
            a || b;

            // Conditional
            a > b ? a : b;

            // Assignment
            x = y;
            x *= y;
            x /= y;
            x %= y;
            x += y;
            x -= y;
            x <<= 2;
            x >>= 2;
            x &= y;
            x ^= y;
            x |= y;

            // Comma
        	(x = 1, y = 2);
        "#;
        let stmts = parse_c_body(input);

        // primary expressions
        assert_stmt_expr!(stmts[0], Expr::Variable(..));
        assert_stmt_expr!(stmts[1], Expr::Number(..));
        assert_stmt_expr!(stmts[2], Expr::Char(..));
        assert_stmt_expr!(stmts[3], Expr::String(..));
        assert_stmt_expr!(stmts[4], Expr::Add(..)); // currenty don't have Paren expr

        // postfix expressions
        assert_stmt_expr!(stmts[5], Expr::Deref(..));
        assert_stmt_expr!(stmts[6], Expr::Call(..));
        assert_stmt_expr!(stmts[7], Expr::Call(..));
        assert_stmt_expr!(stmts[8], Expr::Member(..));
        assert_stmt_expr!(stmts[9], Expr::PointerMember(..));
        assert_stmt_expr!(stmts[10], Expr::PostIncrement(..));
        assert_stmt_expr!(stmts[11], Expr::PostDecrement(..));
        assert_stmt_expr!(stmts[12], Expr::CompoundLiteral(..));

        // unary expressions
        assert_stmt_expr!(stmts[13], Expr::PreIncrement(..));
        assert_stmt_expr!(stmts[14], Expr::PreDecrement(..));
        assert_stmt_expr!(stmts[15], Expr::AddressOf(..));
        assert_stmt_expr!(stmts[16], Expr::Deref(..));
        assert_stmt_expr!(stmts[17], Expr::Variable(..)); // +x is parsed as just x
        assert_stmt_expr!(stmts[18], Expr::Neg(..));
        assert_stmt_expr!(stmts[19], Expr::BitwiseNot(..));
        assert_stmt_expr!(stmts[20], Expr::LogicalNot(..));
        assert_stmt_expr!(stmts[21], Expr::Sizeof(..));
        assert_stmt_expr!(stmts[22], Expr::SizeofType(..));
        assert_stmt_expr!(stmts[23], Expr::AlignofType(..));

        // cast expression
        assert_stmt_expr!(stmts[24], Expr::ExplicitCast(..));

        // multiplicative expressions
        assert_stmt_expr!(stmts[25], Expr::Mul(..));
        assert_stmt_expr!(stmts[26], Expr::Div(..));
        assert_stmt_expr!(stmts[27], Expr::Mod(..));

        // additive expressions
        assert_stmt_expr!(stmts[28], Expr::Add(..));
        assert_stmt_expr!(stmts[29], Expr::Sub(..));

        // relational expressions
        assert_stmt_expr!(stmts[30], Expr::LeftShift(..));
        assert_stmt_expr!(stmts[31], Expr::RightShift(..));
        assert_stmt_expr!(stmts[32], Expr::LessThan(..));
        assert_stmt_expr!(stmts[33], Expr::GreaterThan(..));
        assert_stmt_expr!(stmts[34], Expr::LessThanOrEqual(..));
        assert_stmt_expr!(stmts[35], Expr::GreaterThanOrEqual(..));

        // equality expressions
        assert_stmt_expr!(stmts[36], Expr::Equal(..));
        assert_stmt_expr!(stmts[37], Expr::NotEqual(..));

        // bitwise expressions
        assert_stmt_expr!(stmts[38], Expr::BitwiseAnd(..));
        assert_stmt_expr!(stmts[39], Expr::BitwiseXor(..));
        assert_stmt_expr!(stmts[40], Expr::BitwiseOr(..));

        // logical expressions
        assert_stmt_expr!(stmts[41], Expr::LogicalAnd(..));
        assert_stmt_expr!(stmts[42], Expr::LogicalOr(..));

        // conditional expression
        assert_stmt_expr!(stmts[43], Expr::Ternary(..));
        // assignment expressions
        assert_stmt_expr!(stmts[44], Expr::Assign(..));
        assert_stmt_expr!(stmts[45], Expr::AssignMul(..));
        assert_stmt_expr!(stmts[46], Expr::AssignDiv(..));
        assert_stmt_expr!(stmts[47], Expr::AssignMod(..));
        assert_stmt_expr!(stmts[48], Expr::AssignAdd(..));
        assert_stmt_expr!(stmts[49], Expr::AssignSub(..));
        assert_stmt_expr!(stmts[50], Expr::AssignLeftShift(..));
        assert_stmt_expr!(stmts[51], Expr::AssignRightShift(..));
        assert_stmt_expr!(stmts[52], Expr::AssignBitwiseAnd(..));
        assert_stmt_expr!(stmts[53], Expr::AssignBitwiseXor(..));
        assert_stmt_expr!(stmts[54], Expr::AssignBitwiseOr(..));

        // comma expression
        assert_stmt_expr!(stmts[55], Expr::Comma(..));
    }

    /// Test parsing of _Generic expressions
    #[test]
    #[ignore="not supported for now"]
    fn test_generic_expression() {
        let input = r#"
            _Generic(x, int: 1, double: 2.0, default: 0);
        "#;
        let stmts = parse_c_body(input);
        assert_stmt_expr!(stmts[0], Expr::Generic(..));
    }

    /// Test parsing of _Alignas alignment specifier
    #[test]
    #[ignore="not supported for now"]
    fn test_alignas_specifier() {
        let input = r#"
            _Alignas(8) int x;
        "#;
        let stmts = parse_c_body(input);
        // Debug: print the actual AST structure
        println!("Actual AST for test_alignas_specifier:");
        for (i, stmt) in stmts.iter().enumerate() {
            println!("stmt[{}]: {:?}", i, stmt);
        }
        if let Stmt::Declaration(Decl::VarGroup(ty, declarators)) = &stmts[0] {
            assert!(ty.alignas.is_some());
            assert_eq!(declarators[0].name.unwrap().as_str(), "x");
        } else {
            panic!("Expected Declaration");
        }
    }

    /// Test parsing of static_assert
    #[test]
    fn test_static_assert() {
        let input = r#"
            _Static_assert(sizeof(int) == 4, "int must be 4 bytes");
        "#;
        let stmts = parse_c_body(input);
        assert!(matches!(
            &stmts[0],
            Stmt::Declaration(Decl::StaticAssert(..))
        ));
    }

    /// Test parsing of goto and label statements
    #[test]
    fn test_goto_and_label() {
        let input = r#"
            goto a;
            a: x = 1;
        "#;
        let stmts = parse_c_body(input);
        assert!(matches!(&stmts[0], Stmt::Goto(..)));
        assert!(matches!(&stmts[1], Stmt::Label(..)));
    }

    /// Test parsing of floating-point literals
    #[test]
    fn test_float_literals() {
        let input = r#"
            float a = 1.0;
            double b = 2.0f;
            float c = 3e-10;
        "#;
        let stmts = parse_c_body(input);

        assert_decl_full!(
            stmts,
            0,
            "a",
            TypeSpecKind::Builtin(_),
            Expr::FloatNumber(..)
        );
        assert_decl_full!(
            stmts,
            1,
            "b",
            TypeSpecKind::Builtin(_),
            Expr::FloatNumber(..)
        );
        assert_decl_full!(
            stmts,
            2,
            "c",
            TypeSpecKind::Builtin(_),
            Expr::FloatNumber(..)
        );
    }

    /// Test parsing of function declarations with void star
    #[test]
    fn test_function_with_pointer() {
        let input = r#"
            void *calloc(int __nmemb, int __size);
        "#;
        let ast = parse_c_code(input).unwrap();

        // Check first function declaration
        if let Decl::Func(FuncDecl { name, params, .. }) = &ast.globals[0] {
            assert_eq!(name.as_str(), "calloc");
            assert_eq!(params.len(), 2);
            assert_eq!(params[0].name.as_str(), "__nmemb");
            assert_eq!(params[1].name.as_str(), "__size");
        } else {
            panic!("Expected FunctionDeclaration");
        }
        // Note: globals field is still present in AST, but will be removed in semantic analysis
    }

    /// Test parsing of `_Noreturn` function specifier
    #[test]
    fn test_function_with_noreturn() {
        let input = "_Noreturn void exit(int status);";
        let ast = parse_c_code(input).unwrap();
        assert!(matches!(
            &ast.globals[0],
            Decl::Func(FuncDecl {
                is_noreturn: true,
                ..
            })
        ));
        // Note: globals field is still present in AST, but will be removed in semantic analysis
    }

    /// Test parsing of pointer and address-of operator precedence
    #[test]
    fn test_pointer_precedence() {
        let input = "&x[1] - &x[0];";
        let stmts = parse_c_body(input);
        assert_stmt_expr!(stmts[0], Expr::Sub(..));
        if let Stmt::Expr(expr) = &stmts[0] {
            if let Expr::Sub(lhs, rhs) = &**expr {
                assert!(matches!(**lhs, Expr::AddressOf(..)));
                assert!(matches!(**rhs, Expr::AddressOf(..)));
            } else {
                panic!("Expected a subtraction expression");
            }
        }
    }

    /// Test parsing of various type declaration in function body
    #[test]
    fn test_var_declaration() {
        // simple builtin with single keyword
        assert_type_spec!("_Bool x;", TypeKeyword::BOOL.bits());
        assert_type_spec!("char x;", TypeKeyword::CHAR.bits());
        assert_type_spec!("short x;", TypeKeyword::SHORT.bits());
        assert_type_spec!("int x;", TypeKeyword::INT.bits());
        assert_type_spec!("long x;", TypeKeyword::LONG.bits());
        assert_type_spec!("float x;", TypeKeyword::FLOAT.bits());
        assert_type_spec!("double x;", TypeKeyword::DOUBLE.bits());

        // builtin with double keyword
        assert_type_spec!(
            "long unsigned x;",
            TypeKeyword::UNSIGNED.bits() | TypeKeyword::LONG.bits()
        );
        assert_type_spec!(
            "unsigned long x;",
            TypeKeyword::UNSIGNED.bits() | TypeKeyword::LONG.bits()
        );
        assert_type_spec!(
            "long int x;",
            TypeKeyword::INT.bits() | TypeKeyword::LONG.bits()
        );
        assert_type_spec!(
            "int long x;",
            TypeKeyword::INT.bits() | TypeKeyword::LONG.bits()
        );

        // builtin with triple keyword
        assert_type_spec!(
            "long long unsigned x;",
            TypeKeyword::UNSIGNED.bits() | TypeKeyword::LONGLONG.bits()
        );
        assert_type_spec!(
            "long unsigned long x;",
            TypeKeyword::UNSIGNED.bits() | TypeKeyword::LONGLONG.bits()
        );
        assert_type_spec!(
            "unsigned long long x;",
            TypeKeyword::UNSIGNED.bits() | TypeKeyword::LONGLONG.bits()
        );

        // modifier
        assert_type_spec!("static int x;", TypeKeyword::INT.bits(), StorageClass::Static);

        assert_type_spec!("const int x;", TypeKeyword::INT.bits(), StorageClass::None, TypeQualifiers::CONST);
        assert_type_spec!("volatile int x;", TypeKeyword::INT.bits(), StorageClass::None, TypeQualifiers::VOLATILE);
        assert_type_spec!("restrict int x;", TypeKeyword::INT.bits(), StorageClass::None, TypeQualifiers::RESTRICT);

        // enum
        {
            let stmts = parse_c_body("enum{A,B} x;");
            if let Stmt::Declaration(Decl::VarGroup(ty, declarators)) = &stmts[0] {
                assert!(
                    matches!(ty.kind, TypeSpecKind::Enum(_)),
                    "Expected enum type, got {:?}",
                    ty.kind
                );
                assert_eq!(declarators[0].name.unwrap().as_str(), "x");
            } else {
                panic!("Expected Declaration");
            }
        }


        // multi declaration with pointer and array
        assert_type_spec!(
            "int a, *b, **c, d[10], e[10][20], *f[10], (*ptr_to_arr)[5];",
            TypeKeyword::INT.bits(),
            [
                ("a", 0, 0),
                ("b", 1, 0),
                ("c", 2, 0),
                ("d", 0, 1),
                ("e", 0, 2),
                ("f", 1, 1),
                ("ptr_to_arr", 1, 1)
            ]
        );

        // function pointer declarator not supported for now
        // assert_type_spec!(
        //     "int (*func_ptr)(int, char);",
        //     TypeKeyword::INT.bits(),
        //     [("func_ptr", 1, 0)]
        // );
    }
}
