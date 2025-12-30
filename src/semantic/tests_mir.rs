use crate::driver::compiler::CompilePhase;
use crate::driver::{cli::CompileConfig, compiler::CompilerDriver};

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mir_dumper::{MirDumpConfig, MirDumper};

    /// helper function to setup compiler driver with given source code
    fn setup_mir(source: &str) -> String {
        let phase = CompilePhase::Mir;
        let config = CompileConfig::from_virtual_file(source.to_string(), phase);
        let mut driver = CompilerDriver::from_config(config);
        let mut out = match driver.run_pipeline(phase) {
            Ok(out) => out,
            Err(_) => panic!("failed to run: {:?}", driver.get_diagnostics()),
        };
        let first = out.units.first_mut().unwrap();
        let artifact = first.1;

        // Get the complete semantic analysis output
        let sema_output = match artifact.sema_output.clone() {
            Some(sema_output) => sema_output,
            None => {
                let d = driver.get_diagnostics();
                println!("{:?}", d);
                panic!("No semantic output available");
            }
        };

        // Output MIR dump to string
        let dump_config = MirDumpConfig { include_header: false };
        let dumper = MirDumper::new(&sema_output, &dump_config);

        dumper.generate_mir_dump().unwrap()
    }

    /// helper function to setup compiler driver and return diagnostics output string
    fn setup_diagnostics_output(source: &str) -> String {
        // Use string-based MIR dump with no header for cleaner testing
        let config = CompileConfig::from_virtual_file(source.to_string(), CompilePhase::Mir);
        let mut driver = CompilerDriver::from_config(config);

        let _ = driver.run_pipeline(CompilePhase::Mir);

        // Get diagnostics from the driver
        let diagnostics = driver.get_diagnostics();

        // Format diagnostics for snapshot testing
        let diagnostic_output = format!(
            "Diagnostics count: {}\n\n{}",
            diagnostics.len(),
            diagnostics
                .iter()
                .map(|diag| format!(
                    "Level: {:?}\nMessage: {}\nSpan: {}",
                    diag.level, diag.message, diag.span
                ))
                .collect::<Vec<_>>()
                .join("\n\n")
        );

        diagnostic_output
    }

    #[test]
    fn test_if_else_statement() {
        let source = r#"
            int main() {
                int a = 1;
                int b = 2;
                if (a > b) {
                    return 1;
                } else {
                    return 2;
                }
            }
        "#;

        let mir_dump = setup_mir(source);
        insta::assert_snapshot!(mir_dump, @"
        type %t0 = i32

        fn main() -> i32
        {
          locals {
            %a: i32
            %b: i32
            %3: i32
          }

          bb1:
            %a = const 1
            %b = const 2
            %3 = %a > %b
            cond_br %3, bb2, bb3

          bb2:
            return const 1

          bb3:
            return const 2

          bb4:
            unreachable
        }
        ");
    }

    #[test]
    fn test_while_statement() {
        let source = r#"
          int main() {
            int steins = 99;
            while (steins)
              steins = steins - 1;
            return steins;
          }
        "#;

        let mir_dump = setup_mir(source);
        insta::assert_snapshot!(mir_dump, @"
        type %t0 = i32

        fn main() -> i32
        {
          locals {
            %steins: i32
          }

          bb1:
            %steins = const 99
            return %steins
        }
        ");
    }

    #[test]
    fn test_for_stmt() {
        let source = r#"
          int main() {
            int steins = 44;
            int gate = 1;

            for (; steins;)
              steins = steins - gate;
            return steins;
          }
        "#;

        let mir_dump = setup_mir(source);
        insta::assert_snapshot!(mir_dump, @r"
        type %t0 = i32

        fn main() -> i32
        {
          locals {
            %steins: i32
            %gate: i32
          }

          bb1:
            %steins = const 44
            %gate = const 1
            return %steins
        }
        ");
    }

    #[test]
    fn test_simple_variable_return() {
        let source = r#"
            int main() {
                int result = 99;
                return result;
            }
        "#;

        let mir_dump = setup_mir(source);
        insta::assert_snapshot!(mir_dump, @r"
        type %t0 = i32

        fn main() -> i32
        {
          locals {
            %result: i32
          }

          bb1:
            %result = const 99
            return %result
        }
        ");
    }

    #[test]
    fn test_global_variable() {
        let source = r#"
            int result = 99;
            int main() {
                return result;
            }
        "#;

        let mir_dump = setup_mir(source);
        insta::assert_snapshot!(mir_dump, @r"
        type %t0 = i32

        global @result: i32 = const 99

        fn main() -> i32
        {
          locals {
          }

          bb1:
            return @result
        }
        ");
    }

    #[test]
    fn test_consecutive_labels() {
        let source = r#"
            int main() {
                goto end;
                label1:
                label2:
                label3:
                    return 1;
                end:
                    return 0;
            }
        "#;

        let mir_dump = setup_mir(source);
        insta::assert_snapshot!(mir_dump, @"
        type %t0 = i32

        fn main() -> i32
        {
          locals {
          }

          bb1:
            unreachable
        }
        ");
    }

    #[test]
    fn test_struct_type_regression() {
        let source = r#"
            struct { int a; int b; int c; } s = {1, 2, 3};
            int main() {
                if (s.a != 1) return 1;
                return 0;
            }
        "#;

        let mir_dump = setup_mir(source);
        // We want to ensure %t0 is i32 and %t1 is struct using %t0
        // and NOT that %t0 is struct using %t0
        insta::assert_snapshot!(mir_dump, @r"
        type %t0 = i32
        type %t1 = struct anon_struct { a: %t0, b: %t0, c: %t0 }

        global @s: %t1 = const struct_literal { 0: const 1, 1: const 2, 2: const 3 }

        fn main() -> i32
        {
          locals {
            %1: i32
          }

          bb1:
            %1 = @s.field_0 != const 1
            cond_br %1, bb2, bb3

          bb2:
            return const 1

          bb3:
            return const 0
        }
        ");
    }

    #[test]
    fn test_designated_initializer_global() {
        let source = r#"
            struct S { int a; int b; };
            struct S s = { .b = 2, .a = 1 };
            int main() {
                return 0;
            }
        "#;

        let mir_dump = setup_mir(source);
        insta::assert_snapshot!(mir_dump, @r"
        type %t0 = i32
        type %t1 = struct S { a: %t0, b: %t0 }

        global @s: %t1 = const struct_literal { 0: const 1, 1: const 2 }

        fn main() -> i32
        {
          locals {
          }

          bb1:
            return const 0
        }
        ");
    }

    #[test]
    fn test_global_initializer_with_address() {
        let source = r#"
            int x = 10;
            struct S { int a; int *p; };
            struct S s = { .p = &x, .a = 1 };
            int main() {
                return 0;
            }
        "#;

        let mir_dump = setup_mir(source);
        insta::assert_snapshot!(mir_dump, @r"
        type %t0 = i32
        type %t1 = ptr<%t0>
        type %t2 = struct S { a: %t0, p: %t1 }

        global @x: i32 = const 10
        global @s: %t2 = const struct_literal { 0: const 1, 1: const @x }

        fn main() -> i32
        {
          locals {
          }

          bb1:
            return const 0
        }
        ");
    }

    #[test]
    fn test_nested_compound_initializer_global() {
        let source = r#"
            struct S1 {
                int a;
                int b;
            };

            struct S2 {
                int a;
                int b;
                struct S1 s;
            };

            struct S2 v = {1, 2, {3, 4}};

            int main() {
                return 0;
            }
        "#;

        let mir_dump = setup_mir(source);
        insta::assert_snapshot!(mir_dump, @r"
        type %t0 = i32
        type %t1 = struct S1 { a: %t0, b: %t0 }
        type %t2 = struct S2 { a: %t0, b: %t0, s: %t1 }

        global @v: %t2 = const struct_literal { 0: const 1, 1: const 2, 2: const struct_literal { 0: const 3, 1: const 4 } }

        fn main() -> i32
        {
          locals {
          }

          bb1:
            return const 0
        }
        ");
    }
    #[test]
    fn test_struct_tag_shadowing() {
        let source = r#"
            struct T { int x; } s1;
            int main() {
                s1.x = 1;
                {
                    struct T { int y; } s2;
                    s2.y = 2;
                }
                return s1.x;
            }
        "#;

        let mir_dump = setup_mir(source);
        insta::assert_snapshot!(mir_dump, @r"
        type %t0 = i32
        type %t1 = struct T { x: %t0 }
        type %t2 = struct T { y: %t0 }

        global @s1: %t1

        fn main() -> i32
        {
          locals {
            %s2: %t2
          }

          bb1:
            @s1.field_0 = const 1
            %s2.field_0 = const 2
            return @s1.field_0
        }
        ");
    }
    #[test]
    fn test_variable_shadowing() {
        let source = r#"
            int main() {
                int x = 1;
                {
                    int x = 2;
                    if (x != 2) return 1;
                }
                if (x != 1) return 1;
                return 0;
            }
        "#;

        let mir_dump = setup_mir(source);
        // We expect two different %x locals. MIR printer might show them with same name or different IDs.
        // Currently it shows names if available.
        insta::assert_snapshot!(mir_dump, @"
        type %t0 = i32

        fn main() -> i32
        {
          locals {
            %x: i32
            %x: i32
            %3: i32
            %4: i32
          }

          bb1:
            %x = const 1
            %x = const 2
            %3 = %x != const 2
            cond_br %3, bb2, bb3

          bb2:
            return const 1

          bb3:
            br bb4

          bb4:
            %4 = %x != const 1
            cond_br %4, bb5, bb6

          bb5:
            return const 1

          bb6:
            br bb7

          bb7:
            return const 0
        }
        ");
    }

    // #[test]
    // fn test_recursive_struct_access() {
    //     let source = r#"
    //         struct S {
    //             struct S *p;
    //             int x;
    //         };
    //         int main() {
    //             struct S s;
    //             return s.p->p->x;
    //         }
    //     "#;

    //     let mir_dump = setup_mir(source);
    //     insta::assert_snapshot!(mir_dump, @r"
    //     type %t0 = struct S {  }
    //     type %t1 = ptr<%t0>
    //     type %t2 = i32
    //     type %t3 = struct S { p: %t1, x: %t2 }

    //     fn main() -> i32
    //     {
    //       locals {
    //         %s: %t3
    //         %2: i32
    //         %3: i32
    //       }

    //       bb1:
    //         %2 = * %s.field_0
    //         %3 = * %2.field_0
    //         return %3.field_1
    //     }
    //     ");
    // }

    #[test]
    fn test_parameter_shadowing() {
        let source = r#"
            int foo(int x) {
                {
                    int x = 10;
                    return x;
                }
            }
            int main() {
                return foo(5);
            }
        "#;

        let mir_dump = setup_mir(source);
        insta::assert_snapshot!(mir_dump, @"
        type %t0 = i32
        type %t1 = fn(%t0) -> %t0

        fn foo(%x: i32) -> i32
        {
          locals {
            %x: i32
          }

          bb1:
            %x = const 10
            return %x
        }

        fn main() -> i32
        {
          locals {
            %3: i32
          }

          bb2:
            %3 = call foo(const 5)
            return %3
        }
        ");
    }

    #[test]
    fn test_function_with_many_return_types() {
        let source = r#"
          void fn_void() { return; }

          char fn_char() { return 'a'; }
          unsigned char fn_uchar() { return 'b'; }

          short fn_short() { return -7; }
          unsigned short fn_ushort() { return 14; }

          int fn_int() { return -1; }
          unsigned int fn_uint() { return 42; }

          long fn_long() { return 100000L; }
          unsigned long fn_ulong() { return 200000UL; }
          long long fn_llong() { return -3000000000LL; }
          unsigned long long fn_ullong() { return 4000000000ULL; }

          float fn_float() { return 3.14f; }
          double fn_double() { return 2.71828; }

          int main()
          {
              fn_void();

              fn_char();
              fn_uchar();

              fn_short();
              fn_ushort();

              fn_int();
              fn_uint();

              fn_long();
              fn_ulong();

              fn_llong();
              fn_ullong();

              fn_float();
              fn_double();

              return 0;
          }
        "#;

        let mir_dump = setup_mir(source);
        insta::assert_snapshot!(mir_dump, @"
        type %t0 = void
        type %t1 = i8
        type %t2 = u8
        type %t3 = i16
        type %t4 = i32
        type %t5 = u16
        type %t6 = u32
        type %t7 = i64
        type %t8 = u64
        type %t9 = f32
        type %t10 = f64
        type %t11 = fn() -> %t0
        type %t12 = fn() -> %t1
        type %t13 = fn() -> %t2
        type %t14 = fn() -> %t3
        type %t15 = fn() -> %t5
        type %t16 = fn() -> %t4
        type %t17 = fn() -> %t6
        type %t18 = fn() -> %t7
        type %t19 = fn() -> %t8
        type %t20 = fn() -> %t9
        type %t21 = fn() -> %t10

        fn fn_void() -> void
        {
          locals {
          }

          bb1:
            return
        }

        fn fn_char() -> i8
        {
          locals {
          }

          bb2:
            return const 97
        }

        fn fn_uchar() -> u8
        {
          locals {
          }

          bb3:
            return const 98
        }

        fn fn_short() -> i16
        {
          locals {
          }

          bb4:
            return const 0
        }

        fn fn_ushort() -> u16
        {
          locals {
          }

          bb5:
            return const 14
        }

        fn fn_int() -> i32
        {
          locals {
          }

          bb6:
            return const 0
        }

        fn fn_uint() -> u32
        {
          locals {
          }

          bb7:
            return const 42
        }

        fn fn_long() -> i32
        {
          locals {
          }

          bb8:
            return const 100000
        }

        fn fn_ulong() -> u32
        {
          locals {
          }

          bb9:
            return const 200000
        }

        fn fn_llong() -> i64
        {
          locals {
          }

          bb10:
            return const 0
        }

        fn fn_ullong() -> u64
        {
          locals {
          }

          bb11:
            return const 4000000000
        }

        fn fn_float() -> f32
        {
          locals {
          }

          bb12:
            return const 3.14
        }

        fn fn_double() -> f64
        {
          locals {
          }

          bb13:
            return const 2.71828
        }

        fn main() -> i32
        {
          locals {
            %1: void
            %2: i8
            %3: u8
            %4: i16
            %5: u16
            %6: i32
            %7: u32
            %8: i32
            %9: u32
            %10: i64
            %11: u64
            %12: f32
            %13: f64
          }

          bb14:
            %1 = call fn_void()
            %2 = call fn_char()
            %3 = call fn_uchar()
            %4 = call fn_short()
            %5 = call fn_ushort()
            %6 = call fn_int()
            %7 = call fn_uint()
            %8 = call fn_long()
            %9 = call fn_ulong()
            %10 = call fn_llong()
            %11 = call fn_ullong()
            %12 = call fn_float()
            %13 = call fn_double()
            return const 0
        }
        ");
    }

    #[test]
    fn test_duplicate_global_declaration() {
        let source = r#"
            int x;
            int x;

            int main() {
                return x;
            }
        "#;

        let mir_dump = setup_mir(source);
        insta::assert_snapshot!(mir_dump, @"
        type %t0 = i32

        global @x: i32
        global @x: i32

        fn main() -> i32
        {
          locals {
          }

          bb1:
            return @x
        }
        ");
    }

    #[test]
    fn test_duplicate_global_declaration_with_initializers_diagnostic() {
        let source = r#"
            int x = 1;
            int x = 2;

            int main() {
                return x;
            }
        "#;

        let output = setup_diagnostics_output(source);
        insta::assert_snapshot!(output, @r"
        Diagnostics count: 2

        Level: Error
        Message: redefinition of 'x'
        Span: SourceSpan(source_id=SourceId(2), start=36, end=46)

        Level: Note
        Message: previous definition is here
        Span: SourceSpan(source_id=SourceId(2), start=13, end=23)
        ");
    }

    #[test]
    fn test_basic_typedef() {
        let source = r#"
            typedef int my_int;
            int main() {
                my_int x = 10;
                return x;
            }
        "#;

        let mir_dump = setup_mir(source);
        insta::assert_snapshot!(mir_dump, @r"
        type %t0 = i32

        fn main() -> i32
        {
          locals {
            %x: i32
          }

          bb1:
            %x = const 10
            return %x
        }
        ");
    }
}
