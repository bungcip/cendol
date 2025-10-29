//! Tests for parser functionality
//!
//! This module tests the parser's ability to correctly parse C source code
//! and generate the expected Abstract Syntax Tree (AST) structures.

use cendol::file::FileManager;
use cendol::parser::Parser;
use cendol::parser::ast::{Expr, Function, Stmt, TranslationUnit, Type};
use cendol::preprocessor::Preprocessor;

/// Test configuration constants
mod config {
    pub const TEST_FILENAME: &str = "test.c";
}

/// Helper function to parse C code and return the AST
fn parse_c_code(input: &str) -> Result<TranslationUnit, Box<dyn std::error::Error>> {
    let mut preprocessor = Preprocessor::new(FileManager::new());
    let tokens = preprocessor.preprocess(input, config::TEST_FILENAME)?;
    let mut parser = Parser::new(tokens)?;
    let ast = parser.parse()?;
    Ok(ast)
}

/// helper function to parse C function body and return the statements
fn parse_c_body(input: &str) -> Vec<Stmt> {
    let input = format!("
        int func1() {{ return 0; }}
        int func2(int a, int b, int c) {{ return 0; }}

        void c_body(int x, int y, int a, int b, int c, int arr[], struct S obj, struct S *ptr, int *p)
        {{
            {input}
        }}
    ");

    let mut preprocessor = Preprocessor::new(FileManager::new());
    let tokens = preprocessor
        .preprocess(&input, config::TEST_FILENAME)
        .unwrap();
    let mut parser = Parser::new(tokens).unwrap();
    let ast = parser.parse().unwrap();
    let body = ast.functions.last().unwrap().body.clone();
    body
}

/// Creates a simple C program AST for testing
fn create_simple_program_ast() -> TranslationUnit {
    TranslationUnit {
        globals: vec![],
        functions: vec![Function {
            return_type: Type::Int,
            name: "main".to_string(),
            params: vec![],
            body: vec![Stmt::Return(Expr::Number(0))],
            is_inline: false,
            is_variadic: false,
        }],
    }
}

/// Creates a program AST with if-else control flow
fn create_control_flow_program_ast() -> TranslationUnit {
    TranslationUnit {
        globals: vec![],
        functions: vec![Function {
            return_type: Type::Int,
            name: "main".to_string(),
            params: vec![],
            body: vec![Stmt::If(
                Box::new(Expr::Number(1)),
                Box::new(Stmt::Return(Expr::Number(1))),
                Some(Box::new(Stmt::Return(Expr::Number(0)))),
            )],
            is_inline: false,
            is_variadic: false,
        }],
    }
}

#[cfg(test)]
mod tests {
    use crate::parse_c_body;

    use super::{
        create_control_flow_program_ast, create_simple_program_ast, parse_c_code,
    };
    use cendol::parser::ast::{Declarator, Expr, Initializer, Stmt, Type};

    /// Test parsing of simple C programs
    #[test]
    fn test_simple_program() {
        let input = "int main() { return 0; }";
        let ast = parse_c_code(input).unwrap();
        let expected = create_simple_program_ast();
        assert_eq!(ast.functions[0].name, expected.functions[0].name);
        assert_eq!(
            ast.functions[0].body.len(),
            expected.functions[0].body.len()
        );
    }

    /// Test parsing of programs with control flow (if-else statements)
    #[test]
    fn test_control_flow() {
        let input = "int main() { if (1) return 1; else return 0; }";
        let ast = parse_c_code(input).unwrap();
        let expected = create_control_flow_program_ast();
        assert_eq!(ast.functions[0].name, expected.functions[0].name);
        assert_eq!(
            ast.functions[0].body.len(),
            expected.functions[0].body.len()
        );
    }

    /// Test parsing of programs with _Bool variable declarations
    #[test]
    fn test_bool_declaration() {
        let input = "int main() { _Bool a = 1; return 0; }";
        let ast = parse_c_code(input).unwrap();
        assert!(matches!(
            &ast.functions[0].body[0],
            Stmt::Declaration(Type::Bool, declarators, false) if matches!(
                &declarators[0],
                Declarator {
                    ty: Type::Bool,
                    name,
                    initializer: Some(Initializer::Expr(expr)),
                    ..
                } if name == "a" && matches!(**expr, Expr::Number(1))
            )
        ));
        assert!(matches!(&ast.functions[0].body[1], Stmt::Return(Expr::Number(0))));
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
        assert!(matches!(
            &ast.functions[0].body[0],
            Stmt::Declaration(Type::Int, declarators, false) if declarators.len() == 3 &&
                matches!(
                    &declarators[0],
                    Declarator { ty: Type::Int, name, .. } if name == "x"
                ) &&
                matches!(
                    &declarators[1],
                    Declarator { ty: Type::Pointer(inner), name, .. } if name == "p" && **inner == Type::Int
                ) &&
                matches!(
                    &declarators[2],
                    Declarator { ty: Type::Pointer(inner1), name, .. } if name == "pp" &&
                        matches!(&**inner1, Type::Pointer(inner2) if **inner2 == Type::Int)
                )
        ));
        assert!(matches!(&ast.functions[0].body[1], Stmt::Return(Expr::Number(0))));
    }

    // /// Test parsing of designated initializers for structs
    // #[test]
    // fn test_designated_initializer() {
    //     let input = "struct { int x; int y; } point = { .y = 10, .x = 20 };";
    //     let stmts = parse_c_body(input);
    //     let expected = Stmt::Declaration(
    //         Type::Struct(
    //             None,
    //             vec![
    //                 cendol::parser::ast::Parameter {
    //                     ty: Type::Int,
    //                     name: "x".to_string(),
    //                 },
    //                 cendol::parser::ast::Parameter {
    //                     ty: Type::Int,
    //                     name: "y".to_string(),
    //                 },
    //             ],
    //         ),
    //         "point".to_string(),
    //         Some(Box::new(Expr::StructInitializer(vec![
    //             Expr::DesignatedInitializer("y".to_string(), Box::new(Expr::Number(10))),
    //             Expr::DesignatedInitializer("x".to_string(), Box::new(Expr::Number(20))),
    //         ]))),
    //     );
    //     assert_eq!(stmts[0], expected);
    // }

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
        assert!(matches!(stmts[0], Stmt::Expr(Expr::Variable(_, _))));
        assert!(matches!(stmts[1], Stmt::Expr(Expr::Number(_))));
        assert!(matches!(stmts[2], Stmt::Expr(Expr::Char(_))));
        assert!(matches!(stmts[3], Stmt::Expr(Expr::String(_))));
        assert!(matches!(stmts[4], Stmt::Expr(Expr::Add(..)))); // currenty don't have Paren expr

        // postfix expressions
        assert!(matches!(stmts[5], Stmt::Expr(Expr::Deref(..))));
        assert!(matches!(stmts[6], Stmt::Expr(Expr::Call(..))));
        assert!(matches!(stmts[7], Stmt::Expr(Expr::Call(..))));
        assert!(matches!(stmts[8], Stmt::Expr(Expr::Member(..))));
        assert!(matches!(stmts[9], Stmt::Expr(Expr::PointerMember(..))));
        assert!(matches!(stmts[10], Stmt::Expr(Expr::PostIncrement(..))));
        assert!(matches!(stmts[11], Stmt::Expr(Expr::PostDecrement(..))));
        assert!(matches!(stmts[12], Stmt::Expr(Expr::CompoundLiteral(..))));

        // unary expressions
        assert!(matches!(stmts[13], Stmt::Expr(Expr::PreIncrement(..))));
        assert!(matches!(stmts[14], Stmt::Expr(Expr::PreDecrement(..))));
        assert!(matches!(stmts[15], Stmt::Expr(Expr::AddressOf(..))));
        assert!(matches!(stmts[16], Stmt::Expr(Expr::Deref(..))));
        assert!(matches!(stmts[17], Stmt::Expr(Expr::Variable(..)))); // +x is parsed as just x
        assert!(matches!(stmts[18], Stmt::Expr(Expr::Neg(..))));
        assert!(matches!(stmts[19], Stmt::Expr(Expr::BitwiseNot(..))));
        assert!(matches!(stmts[20], Stmt::Expr(Expr::LogicalNot(..))));
        assert!(matches!(stmts[21], Stmt::Expr(Expr::Sizeof(..))));
        assert!(matches!(stmts[22], Stmt::Expr(Expr::SizeofType(..))));

        // cast expression
        assert!(matches!(stmts[23], Stmt::Expr(Expr::ExplicitCast(..))));

        // multiplicative expressions
        assert!(matches!(stmts[24], Stmt::Expr(Expr::Mul(..))));
        assert!(matches!(stmts[25], Stmt::Expr(Expr::Div(..))));
        assert!(matches!(stmts[26], Stmt::Expr(Expr::Mod(..))));

        // additive expressions
        assert!(matches!(stmts[27], Stmt::Expr(Expr::Add(..))));
        assert!(matches!(stmts[28], Stmt::Expr(Expr::Sub(..))));

        // relational expressions
        assert!(matches!(stmts[29], Stmt::Expr(Expr::LeftShift(..))));
        assert!(matches!(stmts[30], Stmt::Expr(Expr::RightShift(..))));
        assert!(matches!(stmts[31], Stmt::Expr(Expr::LessThan(..))));
        assert!(matches!(stmts[32], Stmt::Expr(Expr::GreaterThan(..))));
        assert!(matches!(stmts[33], Stmt::Expr(Expr::LessThanOrEqual(..))));
        assert!(matches!(
            stmts[34],
            Stmt::Expr(Expr::GreaterThanOrEqual(..))
        ));

        // equality expressions
        assert!(matches!(stmts[35], Stmt::Expr(Expr::Equal(..))));
        assert!(matches!(stmts[36], Stmt::Expr(Expr::NotEqual(..))));

        // bitwise expressions
        assert!(matches!(stmts[37], Stmt::Expr(Expr::BitwiseAnd(..))));
        assert!(matches!(stmts[38], Stmt::Expr(Expr::BitwiseXor(..))));
        assert!(matches!(stmts[39], Stmt::Expr(Expr::BitwiseOr(..))));

        // logical expressions
        assert!(matches!(stmts[40], Stmt::Expr(Expr::LogicalAnd(..))));
        assert!(matches!(stmts[41], Stmt::Expr(Expr::LogicalOr(..))));

        // conditional expression
        assert!(matches!(stmts[42], Stmt::Expr(Expr::Ternary(..))));
        // assignment expressions
        assert!(matches!(stmts[43], Stmt::Expr(Expr::Assign(..))));
        assert!(matches!(stmts[44], Stmt::Expr(Expr::AssignMul(..))));
        assert!(matches!(stmts[45], Stmt::Expr(Expr::AssignDiv(..))));
        assert!(matches!(stmts[46], Stmt::Expr(Expr::AssignMod(..))));
        assert!(matches!(stmts[47], Stmt::Expr(Expr::AssignAdd(..))));
        assert!(matches!(stmts[48], Stmt::Expr(Expr::AssignSub(..))));
        assert!(matches!(stmts[49], Stmt::Expr(Expr::AssignLeftShift(..))));
        assert!(matches!(stmts[50], Stmt::Expr(Expr::AssignRightShift(..))));
        assert!(matches!(stmts[51], Stmt::Expr(Expr::AssignBitwiseAnd(..))));
        assert!(matches!(stmts[52], Stmt::Expr(Expr::AssignBitwiseXor(..))));
        assert!(matches!(stmts[53], Stmt::Expr(Expr::AssignBitwiseOr(..))));

        // comma expression
        assert!(matches!(stmts[54], Stmt::Expr(Expr::Comma(..))));
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
        assert!(matches!(&stmts[0], Stmt::Declaration(..)));
        if let Stmt::Declaration(_, declarators, _) = &stmts[0] {
            if let Some(Initializer::Expr(expr)) = &declarators[0].initializer {
                assert!(matches!(**expr, Expr::FloatNumber(..)));
            } else {
                panic!("Expected an initializer");
            }
        }
        assert!(matches!(&stmts[1], Stmt::Declaration(..)));
        if let Stmt::Declaration(_, declarators, _) = &stmts[1] {
            if let Some(Initializer::Expr(expr)) = &declarators[0].initializer {
                assert!(matches!(**expr, Expr::FloatNumber(..)));
            } else {
                panic!("Expected an initializer");
            }
        }
        assert!(matches!(&stmts[2], Stmt::Declaration(..)));
        if let Stmt::Declaration(_, declarators, _) = &stmts[2] {
            if let Some(Initializer::Expr(expr)) = &declarators[0].initializer {
                assert!(matches!(**expr, Expr::FloatNumber(..)));
            } else {
                panic!("Expected an initializer");
            }
        }
    }
}
