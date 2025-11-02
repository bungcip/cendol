//! Tests for parser functionality
//!
//! This module tests the parser's ability to correctly parse C source code
//! and generate the expected Abstract Syntax Tree (AST) structures.

use cendol::parser::Parser;
use cendol::parser::ast::{Stmt, TranslationUnit};
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
    ($stmts:expr, $idx:expr, $expected_name:expr, $expected_ty:pat, $expr_pat:pat) => {{
        assert!(
            matches!(&$stmts[$idx], Stmt::Declaration(..)),
            "Expected declaration at stmts[{}]",
            $idx
        );

        if let Stmt::Declaration(_, declarators, _) = &$stmts[$idx] {
            assert!(
                !declarators.is_empty(),
                "Expected at least one declarator at stmts[{}]",
                $idx
            );

            let decl = &declarators[0];

            // cek nama
            assert_eq!(
                decl.name.as_str(),
                $expected_name,
                "Unexpected declarator name at stmts[{}]",
                $idx
            );

            // cek tipe
            assert!(
                matches!(decl.ty, $expected_ty),
                "Unexpected type for declarator `{}` at stmts[{}]: got {:?}",
                decl.name,
                $idx,
                decl.ty
            );

            // cek initializer -> Expr pattern
            match &decl.initializer {
                Some(Initializer::Expr(expr)) => {
                    assert!(
                        matches!(**expr, $expr_pat),
                        "Initializer expression for `{}` did not match `{}` at stmts[{}]",
                        decl.name,
                        stringify!($expr_pat),
                        $idx
                    );
                }
                other => panic!(
                    "Expected expression initializer for `{}` at stmts[{}], found {:?}",
                    decl.name, $idx, other
                ),
            }
        } else {
            panic!("Expected Stmt::Declaration at stmts[{}]", $idx);
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
    let input = format!("
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
    let body = ast.functions.last().unwrap().body.clone();
    body
}

#[cfg(test)]
mod tests {
    use super::parse_c_code;
    use crate::parse_c_body;
    use cendol::parser::ast::{Expr, Initializer, Stmt, Type};

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

        assert_decl_full!(
            stmts,
            0,
            "roti_bakar",
            Type::Bool(_),
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
        let input = "int main() { int x, *p, **pp; return 0; }";
        let ast = parse_c_code(input).unwrap();
        let body = &ast.functions[0].body;

        if let Stmt::Declaration(ty, declarators, false) = &body[0] {
            assert_eq!(declarators.len(), 3);
            assert!(matches!(**ty, Type::Int(_)));

            // Check first declarator: int x
            assert_eq!(declarators[0].name.as_str(), "x");
            assert!(matches!(declarators[0].ty, Type::Int(_)));

            // Check second declarator: int *p
            assert_eq!(declarators[1].name.as_str(), "p");
            assert!(matches!(
                declarators[1].ty,
                Type::Pointer(ref inner, _) if matches!(**inner, Type::Int(_))
            ));

            // Check third declarator: int **pp
            assert_eq!(declarators[2].name.as_str(), "pp");
            assert!(matches!(
                declarators[2].ty,
                Type::Pointer(ref inner1, _)
                    if matches!(**inner1, Type::Pointer(ref inner2, _) if matches!(**inner2, Type::Int(_)))
            ));
        } else {
            panic!("Expected a declaration statement");
        }

        if let Stmt::Return(expr) = &body[1] {
            assert!(matches!(**expr, Expr::Number(0, ..)));
        } else {
            panic!("Expected a return statement");
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

        assert_decl_full!(stmts, 0, "a", Type::Float(_), Expr::FloatNumber(..));
        assert_decl_full!(stmts, 1, "b", Type::Double(_), Expr::FloatNumber(..));
        assert_decl_full!(stmts, 2, "c", Type::Float(_), Expr::FloatNumber(..));
    }

    /// Test parsing of function declarations with void star
    #[test]
    fn test_function_with_pointer() {
        let input = r#"
            void *calloc(int __nmemb, int __size);
        "#;
        let ast = parse_c_code(input).unwrap();

        // Check first function declaration
        if let Stmt::FunctionDeclaration { name, params, .. } = &ast.globals[0] {
            assert_eq!(name.as_str(), "calloc");
            assert_eq!(params.len(), 2);
            assert_eq!(params[0].name.as_str(), "__nmemb");
            assert_eq!(params[1].name.as_str(), "__size");
        } else {
            panic!("Expected FunctionDeclaration");
        }
    }

    /// Test parsing of `_Noreturn` function specifier
    #[test]
    fn test_function_with_noreturn() {
        let input = "_Noreturn void exit(int status);";
        let ast = parse_c_code(input).unwrap();
        assert!(matches!(
            &ast.globals[0],
            Stmt::FunctionDeclaration {
                is_noreturn: true,
                ..
            }
        ));
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

    /// Test parsing of various type specifier combinations to prevent regression
    /// Tests both original and new supported orderings
    #[test]
    fn test_type_specifier_combinations() {
        // Test original problematic case: long unsigned int
        let input1 = "void *calloc(long unsigned int __nmemb, long unsigned int __size);";
        let ast1 = parse_c_code(input1).unwrap();
        if let Stmt::FunctionDeclaration { params, .. } = &ast1.globals[0] {
            assert_eq!(params.len(), 2);
            assert!(matches!(params[0].ty, Type::UnsignedLong(_)));
            assert!(matches!(params[1].ty, Type::UnsignedLong(_)));
        } else {
            panic!("Expected FunctionDeclaration");
        }

        // Test long unsigned (without int)
        let input2 = "long unsigned x;";
        let stmts2 = parse_c_body(input2);
        if let Stmt::Declaration(ty, declarators, _) = &stmts2[0] {
            assert!(matches!(**ty, Type::UnsignedLong(_)));
            assert_eq!(declarators[0].name.as_str(), "x");
            assert!(matches!(declarators[0].ty, Type::UnsignedLong(_)));
        } else {
            panic!("Expected Declaration");
        }

        // Test long long unsigned
        let input3 = "long long unsigned x;";
        let stmts3 = parse_c_body(input3);
        if let Stmt::Declaration(ty, declarators, _) = &stmts3[0] {
            assert!(matches!(**ty, Type::UnsignedLongLong(_)));
            assert_eq!(declarators[0].name.as_str(), "x");
            assert!(matches!(declarators[0].ty, Type::UnsignedLongLong(_)));
        } else {
            panic!("Expected Declaration");
        }

        // Test long unsigned long
        let input4 = "long unsigned long x;";
        let stmts4 = parse_c_body(input4);
        if let Stmt::Declaration(ty, declarators, _) = &stmts4[0] {
            assert!(matches!(**ty, Type::UnsignedLongLong(_)));
            assert_eq!(declarators[0].name.as_str(), "x");
            assert!(matches!(declarators[0].ty, Type::UnsignedLongLong(_)));
        } else {
            panic!("Expected Declaration");
        }

        // Test that original combinations still work: unsigned long
        let input5 = "unsigned long x;";
        let stmts5 = parse_c_body(input5);
        if let Stmt::Declaration(ty, declarators, _) = &stmts5[0] {
            assert!(matches!(**ty, Type::UnsignedLong(_)));
            assert_eq!(declarators[0].name.as_str(), "x");
            assert!(matches!(declarators[0].ty, Type::UnsignedLong(_)));
        } else {
            panic!("Expected Declaration");
        }

        // Test that original combinations still work: unsigned long long
        let input6 = "unsigned long long x;";
        let stmts6 = parse_c_body(input6);
        if let Stmt::Declaration(ty, declarators, _) = &stmts6[0] {
            assert!(matches!(**ty, Type::UnsignedLongLong(_)));
            assert_eq!(declarators[0].name.as_str(), "x");
            assert!(matches!(declarators[0].ty, Type::UnsignedLongLong(_)));
        } else {
            panic!("Expected Declaration");
        }

        // Test long int
        let input7 = "long int x;";
        let stmts7 = parse_c_body(input7);
        if let Stmt::Declaration(ty, declarators, _) = &stmts7[0] {
            assert!(matches!(**ty, Type::Long(_)));
            assert_eq!(declarators[0].name.as_str(), "x");
            assert!(matches!(declarators[0].ty, Type::Long(_)));
        } else {
            panic!("Expected Declaration");
        }

        // Test multiple type combinations in same declaration
        let input8 =
            "unsigned long a; long unsigned int b; unsigned long long c; long long unsigned d;";
        let stmts8 = parse_c_body(input8);

        // Check first: unsigned long a
        if let Stmt::Declaration(ty1, decls1, _) = &stmts8[0] {
            assert!(matches!(**ty1, Type::UnsignedLong(_)));
            assert_eq!(decls1[0].name.as_str(), "a");
            assert!(matches!(decls1[0].ty, Type::UnsignedLong(_)));
        } else {
            panic!("Expected Declaration for a");
        }

        // Check second: long unsigned int b
        if let Stmt::Declaration(ty2, decls2, _) = &stmts8[1] {
            assert!(matches!(**ty2, Type::UnsignedLong(_)));
            assert_eq!(decls2[0].name.as_str(), "b");
            assert!(matches!(decls2[0].ty, Type::UnsignedLong(_)));
        } else {
            panic!("Expected Declaration for b");
        }

        // Check third: unsigned long long c
        if let Stmt::Declaration(ty3, decls3, _) = &stmts8[2] {
            assert!(matches!(**ty3, Type::UnsignedLongLong(_)));
            assert_eq!(decls3[0].name.as_str(), "c");
            assert!(matches!(decls3[0].ty, Type::UnsignedLongLong(_)));
        } else {
            panic!("Expected Declaration for c");
        }

        // Check fourth: long long unsigned d
        if let Stmt::Declaration(ty4, decls4, _) = &stmts8[3] {
            assert!(matches!(**ty4, Type::UnsignedLongLong(_)));
            assert_eq!(decls4[0].name.as_str(), "d");
            assert!(matches!(decls4[0].ty, Type::UnsignedLongLong(_)));
        } else {
            panic!("Expected Declaration for d");
        }
    }
}
