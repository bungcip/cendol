//! Tests for parser functionality
//!
//! This module tests the parser's ability to correctly parse C source code
//! and generate the expected Abstract Syntax Tree (AST) structures.

use cendol::file::FileManager;
use cendol::logger::Logger;
use cendol::parser::Parser;
use cendol::parser::ast::{Expr, Function, Program, Stmt, Type};
use cendol::preprocessor::Preprocessor;

/// Test configuration constants
mod config {
    pub const TEST_FILENAME: &str = "test.c";
}

/// Helper function to parse C code and return the AST
fn parse_c_code(input: &str) -> Result<Program, Box<dyn std::error::Error>> {
    let mut preprocessor = Preprocessor::new(FileManager::new());
    let tokens = preprocessor.preprocess(input, config::TEST_FILENAME)?;
    let logger = Logger::new(true); // Enable verbose logging for debugging
    let mut parser = Parser::new(tokens, logger)?;
    let ast = parser.parse()?;
    Ok(ast)
}

/// helper function to parse C function body and return the statements
fn parse_c_body(input: &str) -> Vec<Stmt> {
    let input = format!("
        int func1() {{ return 0; }}
        int func2(int a, int b, int c) {{ return 0; }}
        struct S {{ int member; }};

        void c_body(int x, int y, int a, int b, int c, int arr[], struct S obj, struct S *ptr, int *p)
        {{
            {input}
        }}
    ");

    let mut preprocessor = Preprocessor::new(FileManager::new());
    let tokens = preprocessor
        .preprocess(&input, config::TEST_FILENAME)
        .unwrap();
    let logger = Logger::new(true); // Enable verbose logging for debugging
    let mut parser = Parser::new(tokens, logger).unwrap();
    let ast = parser.parse().unwrap();
    let body = ast.functions.last().unwrap().body.clone();
    body
}

/// Creates a simple C program AST for testing
fn create_simple_program_ast() -> Program {
    Program {
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

/// Creates a program AST with a _Bool variable declaration
fn create_bool_program_ast() -> Program {
    Program {
        globals: vec![],
        functions: vec![Function {
            return_type: Type::Int,
            name: "main".to_string(),
            params: vec![],
            body: vec![
                Stmt::Declaration(Type::Bool, "a".to_string(), Some(Box::new(Expr::Number(1)))),
                Stmt::Return(Expr::Number(0)),
            ],
            is_inline: false,
            is_variadic: false,
        }],
    }
}


/// Creates a program AST with if-else control flow
fn create_control_flow_program_ast() -> Program {
    Program {
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
        create_bool_program_ast, create_control_flow_program_ast,
        create_simple_program_ast, parse_c_code,
    };
    use cendol::parser::ast::{Expr, Stmt, Type};

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
        let expected = create_bool_program_ast();
        assert_eq!(ast.functions[0].name, expected.functions[0].name);
        assert_eq!(ast.functions[0].body, expected.functions[0].body);
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
        assert!(matches!(stmts[10], Stmt::Expr(Expr::Increment(..))));
        assert!(matches!(stmts[11], Stmt::Expr(Expr::Decrement(..))));
        assert!(matches!(stmts[12], Stmt::Expr(Expr::CompoundLiteral(..))));

        // unary expressions continued
        assert!(matches!(stmts[21], Stmt::Expr(Expr::Sizeof(..))));
        assert!(matches!(stmts[22], Stmt::Expr(Expr::SizeofType(..))));

        // cast expression
        assert!(matches!(stmts[23], Stmt::Expr(Expr::Cast(..))));

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
}
