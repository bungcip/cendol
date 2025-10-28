//! Tests for code generation functionality
//!
//! This module tests the code generation pipeline from C source code
//! to executable binaries, ensuring that the generated code produces
//! the expected results.

use cendol::test_utils::{compile_and_run, compile_and_run_with_output};

#[cfg(test)]
mod tests {
    use super::{compile_and_run, compile_and_run_with_output};

    /// Test basic code generation with a simple function
    #[test]
    fn test_codegen() {
        let input = "int main() { return 0; }";
        let exit_code = compile_and_run(input, "codegen").unwrap();
        assert_eq!(exit_code, 0);
    }

    /// Test code generation with external function calls
    #[test]
    fn test_external_function_call() {
        let input = r#"
        int puts(const char *s);
        int main() {
            puts("hello world");
            return 0;
        }
        "#;
        let output = compile_and_run_with_output(input, "external_function_call").unwrap();
        assert_eq!(output.trim(), "hello world");
    }

    /// Test code generation with ternary conditional expressions
    #[test]
    fn test_ternary_true_condition() {
        let input = r#"
        int main() {
            return 1 ? 42 : 24;
        }
        "#;
        let exit_code = compile_and_run(input, "ternary_true").unwrap();
        assert_eq!(exit_code, 42);
    }

    /// Test code generation with ternary conditional expressions (false condition)
    #[test]
    fn test_ternary_false_condition() {
        let input = r#"
        int main() {
            return 0 ? 42 : 24;
        }
        "#;
        let exit_code = compile_and_run(input, "ternary_false").unwrap();
        assert_eq!(exit_code, 24);
    }

    // /// Test code generation with ternary in variable assignment
    // #[test]
    // fn test_ternary_assignment() {
    //     let input = r#"
    //     int main() {
    //         int result;
    //         result = 1 ? 100 : 200;
    //         return result;
    //     }
    //     "#;
    //     let exit_code = compile_and_run(input, "ternary_assignment").unwrap();
    //     assert_eq!(exit_code, 100);
    // }

    /// Test code generation with ternary using variable condition
    #[test]
    fn test_ternary_variable_condition() {
        let input = r#"
        int main() {
            int condition = 1;
            return condition ? 77 : 88;
        }
        "#;
        let exit_code = compile_and_run(input, "ternary_var_condition").unwrap();
        assert_eq!(exit_code, 77);
    }

    /// Test code generation with nested ternary expressions
    #[test]
    fn test_nested_ternary() {
        let input = r#"
        int main() {
            return 1 ? 0 ? 10 : 20 : 30;
        }
        "#;
        let exit_code = compile_and_run(input, "nested_ternary").unwrap();
        assert_eq!(exit_code, 20);
    }

    /// Test code generation with ternary in arithmetic expression
    #[test]
    fn test_ternary_arithmetic() {
        let input = r#"
        int main() {
            int x = 5;
            return x > 0 ? x + 10 : x - 10;
        }
        "#;
        let exit_code = compile_and_run(input, "ternary_arithmetic").unwrap();
        assert_eq!(exit_code, 15);
    }

    // /// Test code generation with ternary in function argument
    // #[test]
    // fn test_ternary_function_arg() {
    //     let input = r#"
    //     int printf(const char *s, int n);
    //     int main() {
    //         printf("%d\n", 1 ? 123 : 456);
    //         return 0;
    //     }
    //     "#;
    //     let output = compile_and_run_with_output(input, "ternary_function_arg").unwrap();
    //     assert_eq!(output, "123\\n");
    // }

    /// Test code generation with ternary expressions (basic functionality)
    #[test]
    fn test_ternary_basic() {
        let input = r#"
        int main() {
            return 1 ? 42 : 24;
        }
        "#;
        let exit_code = compile_and_run(input, "ternary_basic").unwrap();
        assert_eq!(exit_code, 42);
    }

    /// Test code generation with _Bool variable declarations
    #[test]
    fn test_bool_variable() {
        let input = r#"
        int main() {
            _Bool a = 1;
            if (a) {
                return 42;
            }
            return 0;
        }
        "#;
        let exit_code = compile_and_run(input, "bool_variable").unwrap();
        assert_eq!(exit_code, 42);
    }

    /// Test code generation with designated initializers for structs
    #[test]
    fn test_designated_initializer() {
        let input = r#"
        int main() {
            struct { int x; int y; } point = { .y = 10, .x = 20 };
            return point.x;
        }
        "#;
        let exit_code = compile_and_run(input, "designated_initializer").unwrap();
        assert_eq!(exit_code, 20);
    }

    /// Test code generation with nested designated initializers
    #[test]
    fn test_nested_designated_initializer() {
        let input = r#"
        int main() {
            struct { struct { int x; } inner; } outer = { .inner = { .x = 30 } };
            return outer.inner.x;
        }
        "#;
        let exit_code = compile_and_run(input, "nested_designated_initializer").unwrap();
        assert_eq!(exit_code, 30);
    }

    /// Test code generation with designated initializers for arrays
    #[test]
    #[ignore = "designated initializer for arrays not yet supported"]
    fn test_designated_initializer_array() {
        let input = r#"
        int main() {
            int arr[5] = { [2] = 10, [4] = 20 };
            return arr[2] + arr[4];
        }
        "#;
        let exit_code = compile_and_run(input, "designated_initializer_array").unwrap();
        assert_eq!(exit_code, 30);
    }

    // /// Test code generation with struct padding
    // #[test]
    // fn test_struct_padding() {
    //     let input = r#"
    //     int main() {
    //         struct { char a; int b; } s = { .a = 1, .b = 2 };
    //         return s.b;
    //     }
    //     "#;
    //     let exit_code = compile_and_run(input, "struct_padding").unwrap();
    //     assert_eq!(exit_code, 2);
    // }

    // /// Test code generation with pointer member access
    // #[test]
    // fn test_pointer_member_access() {
    //     let input = r#"
    //     int main() {
    //         struct { int x; int y; } point = { .x = 10, .y = 20 };
    //         struct { int x; int y; } *p = &point;
    //         return p->y;
    //     }
    //     "#;
    //     let exit_code = compile_and_run(input, "pointer_member_access").unwrap();
    //     assert_eq!(exit_code, 20);
    // }

    // /// Test code generation with advanced pointer member access
    // #[test]
    // fn test_advanced_pointer_member_access() {
    //     let input = r#"
    //     struct Point { int x; int y; };
    //     struct Point get_point() {
    //         struct Point p;
    //         p.y = 20;
    //         return p;
    //     }
    //     int main() {
    //         return get_point().y;
    //     }
    //     "#;
    //     let exit_code = compile_and_run(input, "advanced_pointer_member_access").unwrap();
    //     assert_eq!(exit_code, 20);
    // }

    /// Test code generation for type casting
    #[test]
    fn test_type_casting() {
        let input = r#"
        int main() {
            int x = 1;
            char y = (char)x;
            return y;
        }
        "#;
        let exit_code = compile_and_run(input, "type_casting").unwrap();
        assert_eq!(exit_code, 1);
    }

    /// Test code generation for compound literals with structs
    #[test]
    fn test_compound_literal_struct() {
        let input = r#"
        struct Point { int x; int y; };
        int main() {
            struct Point p = (struct Point){ .x = 10, .y = 20 };
            return p.x;
        }
        "#;
        let exit_code = compile_and_run(input, "compound_literal_struct").unwrap();
        assert_eq!(exit_code, 10);
    }

    // /// Test code generation for compound literals with arrays
    // #[test]
    // fn test_compound_literal_array() {
    //     let input = r#"
    //     int main() {
    //         int *p = (int[]){ 1, 2, 3 };
    //         return p[1];
    //     }
    //     "#;
    //     let exit_code = compile_and_run(input, "compound_literal_array").unwrap();
    //     assert_eq!(exit_code, 2);
    // }

    /// Test code generation for pointer subtraction
    #[test]
    #[ignore = "pointer subtraction currently gives wrong result"]
    fn test_pointer_subtraction() {
        let input = r#"
        int main() {
            int arr[5];
            int *p1 = &arr[1];
            int *p2 = &arr[4];
            return p2 - p1;
        }
        "#;
        let exit_code = compile_and_run(input, "pointer_subtraction").unwrap();
        assert_eq!(exit_code, 3);
    }

    // /// Test code generation for inline functions
    // #[test]
    // fn test_inline_function() {
    //     let input = r#"
    //     inline int add(int a, int b) {
    //         return a + b;
    //     }
    //     int main() {
    //         return add(5, 3);
    //     }
    //     "#;
    //     let exit_code = compile_and_run(input, "inline_function").unwrap();
    //     assert_eq!(exit_code, 8);
    // }

    /// Test code generation for variadic functions
    #[test]
    fn test_variadic_function() {
        let input = r#"
        int main() {
            return variadic_func(42, 1, 2, 3);
        }
        int variadic_func(int a, ...) {
            return a;
        }
        "#;
        let exit_code = compile_and_run(input, "variadic_function").unwrap();
        assert_eq!(exit_code, 42);
    }

    /// Test code generation for chained assignments
    #[test]
    fn test_chained_assignment() {
        let input = r#"
        int main() {
            int x;
            int y;
            x = y = 0;
            return x;
        }
        "#;
        let exit_code = compile_and_run(input, "chained_assignment").unwrap();
        assert_eq!(exit_code, 0);
    }

    /// Test code generation for bitwise and shift assignment operators
    #[test]
    fn test_bitwise_and_shift_assignment_operators() {
        let input = r#"
        int main() {
            int x = 15;
            x &= 7;
            x |= 8;
            x ^= 12;
            x <<= 1;
            x >>= 2;
            return x;
        }
        "#;
        let exit_code = compile_and_run(input, "bitwise_and_shift_assignment_operators").unwrap();
        assert_eq!(exit_code, 1);
    }

    /// Test code generation for post-increment and post-decrement operators
    #[test]
    fn test_post_increment_and_decrement() {
        let input = r#"
        int main() {
            int i = 0;
            int j = i++;
            int k = i--;
            return j + k + i;
        }
        "#;
        let exit_code = compile_and_run(input, "post_increment_and_decrement").unwrap();
        assert_eq!(exit_code, 1);
    }

    #[test]
    fn test_string_literal() {
        let input = r#"
        unsigned long strlen(const char *);

        int
        main()
        {
        char *p;

        p = "hello";
        return strlen(p) - 5;
        }
        "#;
        let exit_code = compile_and_run(input, "string_literal").unwrap();
        assert_eq!(exit_code, 0);
    }

    /// Test code generation for typedef
    #[test]
    fn test_typedef() {
        let input = r#"
        typedef int x;
        int main() {
            x v;
            v = 0;
            return v;
        }
        "#;
        let exit_code = compile_and_run(input, "typedef").unwrap();
        assert_eq!(exit_code, 0);
    }

    /// Test code generation for break and continue in for loops
    #[test]
    fn test_for_loop_break_continue() {
        let input = r#"
        int main() {
            int y = 0;
            for (int x = 0; x < 20; x = x + 1) {
                if (x > 10) {
                    break;
                }
                if (x % 2 == 0) {
                    continue;
                }
                y = y + 1;
            }
            return y;
        }
        "#;
        let exit_code = compile_and_run(input, "for_loop_break_continue").unwrap();
        assert_eq!(exit_code, 5);
    }

    /// Test code generation for unions
    #[test]
    fn test_union() {
        let input = r#"
        int
        main()
        {
            union { int a; int b; } u;
            u.a = 1;
            u.b = 3;

            if (u.a != 3 || u.b != 3)
                return 1;
            return 0;
        }
        "#;
        let exit_code = compile_and_run(input, "union").unwrap();
        assert_eq!(exit_code, 0);
    }

    /// Test code generation for nested structs
    #[test]
    fn test_nested_struct() {
        let input = r#"
        struct s {
            int x;
            struct {
                int y;
                int z;
            } nest;
        };

        int
        main() {
            struct s v;
            v.x = 1;
            v.nest.y = 2;
            v.nest.z = 3;
            if (v.x + v.nest.y + v.nest.z != 6)
                return 1;
            return 0;
        }
        "#;
        let exit_code = compile_and_run(input, "nested_struct").unwrap();
        assert_eq!(exit_code, 0);
    }

    /// Test code generation for unsigned int
    #[test]
    fn test_unsigned_int() {
        let input = r#"
        int main() {
            unsigned int x = 2;
            return x;
        }
        "#;
        let exit_code = compile_and_run(input, "unsigned_int").unwrap();
        assert_eq!(exit_code, 2);
    }

    /// Test code generation for short
    #[test]
    fn test_short() {
        let input = r#"
        int main() {
            short x = 3;
            return x;
        }
        "#;
        let exit_code = compile_and_run(input, "short").unwrap();
        assert_eq!(exit_code, 3);
    }

    /// Test code generation for unsigned int division
    #[test]
    fn test_unsigned_int_division() {
        let input = r#"
        int main() {
            unsigned int x = 10;
            unsigned int y = 3;
            return x / y;
        }
        "#;
        let exit_code = compile_and_run(input, "unsigned_int_division").unwrap();
        assert_eq!(exit_code, 3);
    }

    /// Test code generation for unsigned int comparison
    #[test]
    fn test_unsigned_int_comparison() {
        let input = r#"
        int main() {
            unsigned int x = 10;
            unsigned int y = 3;
            return x > y;
        }
        "#;
        let exit_code = compile_and_run(input, "unsigned_int_comparison").unwrap();
        assert_eq!(exit_code, 1);
    }

    /// Test code generation for mixed-sign comparison
    #[test]
    fn test_mixed_sign_comparison() {
        let input = r#"
        int main() {
            int x = -1;
            unsigned int y = 1;
            return x > y;
        }
        "#;
        let exit_code = compile_and_run(input, "mixed_sign_comparison").unwrap();
        assert_eq!(exit_code, 1);
    }

    /// Test code generation for mixed-sign comparison with different integer ranks
    #[test]
    fn test_mixed_sign_comparison_different_ranks() {
        let input = r#"
        int main() {
            long long x = -1;
            unsigned int y = 1;
            return x > y;
        }
        "#;
        let exit_code = compile_and_run(input, "mixed_sign_comparison_different_ranks").unwrap();
        assert_eq!(exit_code, 0);
    }

    /// Test code generation for mixed-sign addition
    #[test]
    fn test_mixed_sign_addition() {
        let input = r#"
        int main() {
            int x = -1;
            unsigned int y = 1;
            return x + y;
        }
        "#;
        let exit_code = compile_and_run(input, "mixed_sign_addition").unwrap();
        assert_eq!(exit_code, 0);
    }

    #[test]
    fn test_short_circuit() {
        let c_code = r#"
            int main() {
                int x = 0;
                int y = 1;

                if (x && (y = 0)) {
                    return 1;
                }
                if (y || (x = 1)) {
                }
                return y;
            }
        "#;
        assert_eq!(compile_and_run(c_code, "short_circuit").unwrap(), 1);
    }

    /// Test code generation for goto and labels
    #[test]
    #[ignore]
    fn test_goto() {
        let input = r#"
        int main() {
            int x = 0;
            goto end;
            x = 1;
        end:
            return x;
        }
        "#;
        let exit_code = compile_and_run(input, "goto").unwrap();
        assert_eq!(exit_code, 0);
    }

    /// Test code generation for character literals
    #[test]
    fn test_char_literal() {
        let input = "int main() { return 'a'; }";
        let exit_code = compile_and_run(input, "char_literal").unwrap();
        assert_eq!(exit_code, 97);
    }

    /// Test code generation for uninitialized global variables
    #[test]
    fn test_uninitialized_global() {
        let input = r#"
        int x;
        int main() {
            return x;
        }
        "#;
        let exit_code = compile_and_run(input, "uninitialized_global").unwrap();
        assert_eq!(exit_code, 0);
    }

    /// Test code generation for initialized global variables
    #[test]
    fn test_initialized_global() {
        let input = r#"
        int x = 42;
        int main() {
            return x;
        }
        "#;
        let exit_code = compile_and_run(input, "initialized_global").unwrap();
        assert_eq!(exit_code, 42);
    }

    /// Test code generation for assigning to a global variable
    #[test]
    fn test_assign_to_global() {
        let input = r#"
        int x = 10;
        int main() {
            x = 20;
            return x;
        }
        "#;
        let exit_code = compile_and_run(input, "assign_to_global").unwrap();
        assert_eq!(exit_code, 20);
    }

    /// Test code generation for pre-increment on a pointer dereference
    #[test]
    fn test_pre_increment_pointer() {
        let input = r#"
        int main() {
            int x = 10;
            int *p = &x;
            ++(*p);
            return x;
        }
        "#;
        let exit_code = compile_and_run(input, "pre_increment_pointer").unwrap();
        assert_eq!(exit_code, 11);
    }

    /// Test code generation for post-increment on a struct member
    #[test]
    fn test_post_increment_struct_member() {
        let input = r#"
        struct S { int x; };
        int main() {
            struct S s;
            s.x = 20;
            int y = s.x++;
            return y;
        }
        "#;
        let exit_code = compile_and_run(input, "post_increment_struct_member").unwrap();
        assert_eq!(exit_code, 20);
    }

    /// Test code generation for pre-decrement on a struct member
    #[test]
    fn test_pre_decrement_struct_member() {
        let input = r#"
        struct S { int x; };
        int main() {
            struct S s;
            s.x = 30;
            --s.x;
            return s.x;
        }
        "#;
        let exit_code = compile_and_run(input, "pre_decrement_struct_member").unwrap();
        assert_eq!(exit_code, 29);
    }

    /// Test code generation for post-decrement on a pointer dereference
    #[test]
    fn test_post_decrement_pointer() {
        let input = r#"
        int main() {
            int x = 40;
            int *p = &x;
            int y = (*p)--;
            return y + x;
        }
        "#;
        let exit_code = compile_and_run(input, "post_decrement_pointer").unwrap();
        assert_eq!(exit_code, 79);
    }

    /// Test code generation for do-while loops with break and continue
    #[test]
    fn test_do_while_loop_break_continue() {
        let input = r#"
        int main() {
            int y = 0;
            int x = 0;
            do {
                x = x + 1;
                if (x % 2 == 0) {
                    continue;
                }
                y = y + 1;
                if (x > 10) {
                    break;
                }
            } while (x < 20);
            return y;
        }
        "#;
        let exit_code = compile_and_run(input, "do_while_loop_break_continue").unwrap();
        assert_eq!(exit_code, 6);
    }

    /// Test code generation for enums
    #[test]
    fn test_enum() {
        let input = r#"
        int main() {
            enum { A, B, C };
            enum { D, E, F } x;
            x = F;
            if (x != 2)
                return 1;
            if (sizeof(x) != 8)
                return 1;
            return 0;
        }
        "#;
        let exit_code = compile_and_run(input, "enum").unwrap();
        assert_eq!(exit_code, 0);
    }

    /// Test code generation for dereferencing a compound literal array
    #[test]
    fn test_deref_compound_literal_array() {
        let input = r#"
        int main() {
            return *((int[2]){10, 20});
        }
        "#;
        let exit_code = compile_and_run(input, "deref_compound_literal_array").unwrap();
        assert_eq!(exit_code, 10);
    }
}
