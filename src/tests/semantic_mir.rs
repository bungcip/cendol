use super::semantic_common::{setup_diagnostics_output, setup_mir};

#[cfg(test)]
mod tests {
    use super::*;

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
        insta::assert_snapshot!(mir_dump, @r"
        type %t0 = i32

        fn main() -> i32
        {
          locals {
            %a: i32
            %b: i32
            %3: i32
          }

          bb1:
            %a = cast<i32>(const 1)
            %b = cast<i32>(const 2)
            %3 = %a > %b
            cond_br %3, bb2, bb3

          bb2:
            return cast<i32>(const 1)

          bb3:
            return cast<i32>(const 2)

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
        insta::assert_snapshot!(mir_dump, @r"
        type %t0 = i32

        fn main() -> i32
        {
          locals {
            %steins: i32
            %2: i32
          }

          bb1:
            %steins = cast<i32>(const 99)
            br bb2

          bb2:
            cond_br %steins, bb3, bb4

          bb3:
            %2 = %steins - cast<i32>(const 1)
            %steins = %2
            br bb2

          bb4:
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
            %3: i32
          }

          bb1:
            %steins = cast<i32>(const 44)
            %gate = cast<i32>(const 1)
            br bb2

          bb2:
            cond_br %steins, bb3, bb4

          bb3:
            %3 = %steins - %gate
            %steins = %3
            br bb2

          bb4:
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
            %result = cast<i32>(const 99)
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

        global @result: i32 = cast<i32>(const 99)

        fn main() -> i32
        {

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
        insta::assert_snapshot!(mir_dump, @r"
        type %t0 = i32

        fn main() -> i32
        {

          bb1:
            br bb5

          bb2:
            br bb3

          bb3:
            br bb4

          bb4:
            return cast<i32>(const 1)

          bb5:
            return cast<i32>(const 0)
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
        type %t1 = struct anonymous { a: %t0, b: %t0, c: %t0 }

        global @s: %t1 = const struct_literal { 0: const 1, 1: const 2, 2: const 3 }

        fn main() -> i32
        {
          locals {
            %1: i32
          }

          bb1:
            %1 = @s.field_0 != cast<i32>(const 1)
            cond_br %1, bb2, bb3

          bb2:
            return cast<i32>(const 1)

          bb3:
            br bb4

          bb4:
            return cast<i32>(const 0)
        }
        ");
    }

    #[test]
    fn test_long_long_comparison_crash() {
        // Regression test for issue where usual arithmetic conversions
        // were not correctly applied in MIR lowering for binary operators
        let source = r#"
            int main() {
                long long x;
                x = 0;
                x = x + 1;
                if (x != 1)
                    return 1;
                return 0;
            }
        "#;
        let mir_dump = setup_mir(source);
        // Verify that the constant 1 is cast to i64 (matching x) before comparison
        // and that the comparison result is used for the branch
        insta::assert_snapshot!(mir_dump, @r"
        type %t0 = i32
        type %t1 = i64

        fn main() -> i32
        {
          locals {
            %x: i64
            %2: i64
            %3: i32
          }

          bb1:
            %x = cast<i64>(const 0)
            %2 = %x + cast<i64>(const 1)
            %x = %2
            %3 = %x != cast<i64>(const 1)
            cond_br %3, bb2, bb3

          bb2:
            return cast<i32>(const 1)

          bb3:
            br bb4

          bb4:
            return cast<i32>(const 0)
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

        global @s: %t1 = const struct_literal { 1: const 2, 0: const 1 }

        fn main() -> i32
        {

          bb1:
            return cast<i32>(const 0)
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
        type %t1 = struct S { a: %t0, p: %t2 }
        type %t2 = ptr<%t0>

        global @x: i32 = cast<i32>(const 10)
        global @s: %t1 = const struct_literal { 1: const @x, 0: const 1 }

        fn main() -> i32
        {

          bb1:
            return cast<i32>(const 0)
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
        type %t1 = struct S2 { a: %t0, b: %t0, s: %t2 }
        type %t2 = struct S1 { a: %t0, b: %t0 }

        global @v: %t1 = const struct_literal { 0: const 1, 1: const 2, 2: const struct_literal { 0: const 3, 1: const 4 } }

        fn main() -> i32
        {

          bb1:
            return cast<i32>(const 0)
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

        global @s1: %t1 = const zero

        fn main() -> i32
        {
          locals {
            %s2: %t2
          }

          bb1:
            @s1.field_0 = cast<i32>(const 1)
            %s2.field_0 = cast<i32>(const 2)
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
        insta::assert_snapshot!(mir_dump, @r"
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
            %x = cast<i32>(const 1)
            %x = cast<i32>(const 2)
            %3 = %x != cast<i32>(const 2)
            cond_br %3, bb2, bb3

          bb2:
            return cast<i32>(const 1)

          bb3:
            br bb4

          bb4:
            %4 = %x != cast<i32>(const 1)
            cond_br %4, bb5, bb6

          bb5:
            return cast<i32>(const 1)

          bb6:
            br bb7

          bb7:
            return cast<i32>(const 0)
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
        insta::assert_snapshot!(mir_dump, @r"
        type %t0 = i32
        type %t1 = fn(%t0) -> %t0

        fn main() -> i32
        {
          locals {
            %3: i32
          }

          bb2:
            %3 = call foo(const 5)
            return %3
        }

        fn foo(%param0: i32) -> i32
        {
          locals {
            %x: i32
          }

          bb1:
            %x = cast<i32>(const 10)
            return %x
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
        insta::assert_snapshot!(mir_dump, @r"
        type %t0 = i32
        type %t1 = f64
        type %t2 = i8
        type %t3 = u32
        type %t4 = void
        type %t5 = u8
        type %t6 = u32
        type %t7 = i16
        type %t8 = f32
        type %t9 = i64
        type %t10 = i32
        type %t11 = u16
        type %t12 = u64
        type %t13 = fn() -> %t4
        type %t14 = fn() -> %t2
        type %t15 = fn() -> %t5
        type %t16 = fn() -> %t7
        type %t17 = fn() -> %t11
        type %t18 = fn() -> %t0
        type %t19 = fn() -> %t6
        type %t20 = fn() -> %t10
        type %t21 = fn() -> %t3
        type %t22 = fn() -> %t9
        type %t23 = fn() -> %t12
        type %t24 = fn() -> %t8
        type %t25 = fn() -> %t1

        fn main() -> i32
        {
          locals {
            %4: i8
            %5: u8
            %6: i16
            %7: u16
            %8: i32
            %9: u32
            %10: i32
            %11: u32
            %12: i64
            %13: u64
            %14: f32
            %15: f64
          }

          bb14:
            call fn_void()
            %4 = call fn_char()
            %5 = call fn_uchar()
            %6 = call fn_short()
            %7 = call fn_ushort()
            %8 = call fn_int()
            %9 = call fn_uint()
            %10 = call fn_long()
            %11 = call fn_ulong()
            %12 = call fn_llong()
            %13 = call fn_ullong()
            %14 = call fn_float()
            %15 = call fn_double()
            return cast<i32>(const 0)
        }

        fn fn_double() -> f64
        {

          bb13:
            return cast<f64>(const 2.71828)
        }

        fn fn_char() -> i8
        {

          bb2:
            return cast<i8>(const 97)
        }

        fn fn_ulong() -> u32
        {

          bb9:
            return cast<u32>(const 200000)
        }

        fn fn_void() -> void
        {

          bb1:
            return
        }

        fn fn_uchar() -> u8
        {

          bb3:
            return cast<u8>(const 98)
        }

        fn fn_uint() -> u32
        {

          bb7:
            return cast<u32>(const 42)
        }

        fn fn_short() -> i16
        {
          locals {
            %1: i32
          }

          bb4:
            %1 = - const 7
            return cast<i16>(%1)
        }

        fn fn_int() -> i32
        {
          locals {
            %2: i32
          }

          bb6:
            %2 = - const 1
            return %2
        }

        fn fn_float() -> f32
        {

          bb12:
            return cast<f32>(const 3.14)
        }

        fn fn_llong() -> i64
        {
          locals {
            %3: i32
          }

          bb10:
            %3 = - const 3000000000
            return cast<i64>(%3)
        }

        fn fn_long() -> i32
        {

          bb8:
            return cast<i32>(const 100000)
        }

        fn fn_ushort() -> u16
        {

          bb5:
            return cast<u16>(const 14)
        }

        fn fn_ullong() -> u64
        {

          bb11:
            return cast<u64>(const 4000000000)
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
        insta::assert_snapshot!(mir_dump, @r"
        type %t0 = i32

        global @x: i32 = const zero

        fn main() -> i32
        {

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
        insta::assert_snapshot!(output, @"
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
            %x = cast<i32>(const 10)
            return %x
        }
        ");
    }

    #[test]
    fn test_mir_generation_for_self_referential_struct() {
        let source = r#"
            int main() {
                struct S { struct S *p; int x; } s;
                s.x = 0;
                s.p = &s;
                return s.p->p->p->p->p->x;
            }
        "#;
        let mir_dump = setup_mir(source);
        insta::assert_snapshot!(mir_dump, @r"
        type %t0 = i32
        type %t1 = struct S { p: %t2, x: %t0 }
        type %t2 = ptr<%t1>

        fn main() -> i32
        {
          locals {
            %s: %t1
          }

          bb1:
            %s.field_1 = cast<i32>(const 0)
            %s.field_0 = addr_of(%s)
            return deref(deref(deref(deref(deref(%s.field_0).field_0).field_0).field_0).field_0).field_1
        }
        ");
    }

    #[test]
    fn test_mir_generation_for_self_referential_union() {
        let source = r#"
            int main() {
                union U { union U *p; int x; } u;
                u.x = 0;
                u.p = &u;
                return u.p->p->p->p->p->x;
            }
        "#;
        let mir_dump = setup_mir(source);
        insta::assert_snapshot!(mir_dump, @r"
        type %t0 = i32
        type %t1 = union U { p: %t2, x: %t0 }
        type %t2 = ptr<%t1>

        fn main() -> i32
        {
          locals {
            %u: %t1
          }

          bb1:
            %u.field_1 = cast<i32>(const 0)
            %u.field_0 = addr_of(%u)
            return deref(deref(deref(deref(deref(%u.field_0).field_0).field_0).field_0).field_0).field_1
        }
        ");
    }

    #[test]
    fn test_external_function_call() {
        let source = r#"
            int strlen(char *);

            int main()
            {
                char *steins;

                steins = "gate";
                return strlen(steins) - 4;
            }
        "#;

        let mir_dump = setup_mir(source);
        insta::assert_snapshot!(mir_dump, @r#"
        type %t0 = i32
        type %t1 = ptr<%t2>
        type %t2 = i8
        type %t3 = [5]%t2
        type %t4 = fn(%t1) -> %t0

        global @.L.str0: [5]i8 = const "gate"

        fn main() -> i32
        {
          locals {
            %steins: ptr<i8>
            %3: i32
            %4: i32
          }

          bb1:
            %steins = cast<ptr<i8>>(const @.L.str0)
            %3 = call strlen(%steins)
            %4 = %3 - cast<i32>(const 4)
            return %4
        }

        extern fn strlen(%param0: ptr<i8>) -> i32
        "#);
    }

    #[test]
    fn test_array_to_pointer_decay_in_function_call() {
        let source = r#"
            int printf(const char* format);

            int main()
            {
                return printf("Hello, World!\n");
            }
        "#;

        let mir_dump = setup_mir(source);
        insta::assert_snapshot!(mir_dump, @r#"
        type %t0 = i32
        type %t1 = ptr<%t2>
        type %t2 = i8
        type %t3 = fn(%t1) -> %t0
        type %t4 = [16]%t2

        global @.L.str0: [16]i8 = const "Hello, World!\n"

        fn main() -> i32
        {
          locals {
            %2: i32
          }

          bb1:
            %2 = call printf(cast<ptr<i8>>(const @.L.str0))
            return %2
        }

        extern fn printf(%param0: ptr<i8>) -> i32
        "#);
    }

    #[test]
    fn test_array_to_pointer_decay_in_variadic_function_call() {
        let source = r#"
            int printf(const char* format, ...);

            int main()
            {
                return printf("Value: %d, %s\n", 42, "test");
            }
        "#;

        let mir_dump = setup_mir(source);
        insta::assert_snapshot!(mir_dump, @r#"
        type %t0 = i32
        type %t1 = ptr<%t2>
        type %t2 = i8
        type %t3 = fn(%t1) -> %t0
        type %t4 = [16]%t2
        type %t5 = [5]%t2

        global @.L.str0: [16]i8 = const "Value: %d, %s\n"
        global @.L.str1: [5]i8 = const "test"

        fn main() -> i32
        {
          locals {
            %2: i32
          }

          bb1:
            %2 = call printf(cast<ptr<i8>>(const @.L.str0), const 42, const @.L.str1)
            return %2
        }

        extern fn printf(%param0: ptr<i8>) -> i32
        "#);
    }

    #[test]
    fn test_increment_decrement() {
        let source = r#"
            int main()
            {
                int okabe = 1;
                int rintaro = okabe++;
                int kyouma = ++rintaro;

                int hohohin = kyouma--;
                int kanggoru = --hohohin;

                return kanggoru;
            }
        "#;

        let mir_dump = setup_mir(source);
        insta::assert_snapshot!(mir_dump, @r"
        type %t0 = i32

        fn main() -> i32
        {
          locals {
            %okabe: i32
            %rintaro: i32
            %3: i32
            %4: i32
            %kyouma: i32
            %6: i32
            %hohohin: i32
            %8: i32
            %9: i32
            %kanggoru: i32
            %11: i32
          }

          bb1:
            %okabe = cast<i32>(const 1)
            %3 = %okabe
            %4 = %okabe + const 1
            %okabe = %4
            %rintaro = %3
            %6 = %rintaro + const 1
            %rintaro = %6
            %kyouma = %6
            %8 = %kyouma
            %9 = %kyouma + const -1
            %kyouma = %9
            %hohohin = %8
            %11 = %hohohin + const -1
            %hohohin = %11
            %kanggoru = %11
            return %kanggoru
        }
        ");
    }

    #[test]
    fn test_simple_goto() {
        let source = r#"
            int main() {
                goto end;
                return 1;
            end:
                return 0;
            }
        "#;
        let mir_dump = setup_mir(source);
        insta::assert_snapshot!(mir_dump, @r"
        type %t0 = i32

        fn main() -> i32
        {

          bb1:
            br bb2

          bb2:
            return cast<i32>(const 0)
        }
        ");
    }

    #[test]
    fn test_deref_after_cast() {
        let source = r#"
            int main() {
                void *p;
                int x;
                x = 2;
                p = &x;
                if (*((int*)p) != 2)
                    return 1;
                return 0;
            }
        "#;

        let mir_dump = setup_mir(source);
        insta::assert_snapshot!(mir_dump, @r"
        type %t0 = i32
        type %t1 = ptr<%t2>
        type %t2 = void
        type %t3 = ptr<%t0>

        fn main() -> i32
        {
          locals {
            %p: ptr<void>
            %x: i32
            %3: i32
          }

          bb1:
            %x = cast<i32>(const 2)
            %p = cast<ptr<void>>(addr_of(%x))
            %3 = deref(cast<ptr<i32>>(%p)) != cast<i32>(const 2)
            cond_br %3, bb2, bb3

          bb2:
            return cast<i32>(const 1)

          bb3:
            br bb4

          bb4:
            return cast<i32>(const 0)
        }
        ");
    }

    #[test]
    fn test_function_pointer_in_struct() {
        let source = r#"
            struct S
            {
                int (*fptr)();
            };

            int
            foo()
            {
                return 0;
            }

            int
            main()
            {
                struct S v;
                v.fptr = foo;
                return v.fptr();
            }
        "#;

        // Just verify it lowers to MIR without panic
        let _ = setup_mir(source);
    }

    #[test]
    fn test_incomplete_record_type() {
        let source = r#"
            typedef struct I FILE;
            extern struct I *p;
            int main() {
                return 0;
            }
        "#;

        let mir_dump = setup_mir(source);
        insta::assert_snapshot!(mir_dump, @r"
        type %t0 = i32
        type %t1 = ptr<%t2>
        type %t2 = struct I {  }

        global @p: ptr<%t2> = const zero

        fn main() -> i32
        {

          bb1:
            return cast<i32>(const 0)
        }
        ");
    }
    #[test]
    fn test_anonymous_struct_union_field_indices() {
        let source = r#"
            typedef struct {
                int a;
                union {
                    int b1;
                    int b2;
                };
                struct { union { struct { int c; }; }; };
                struct {
                    int d;
                };
            } s;

            int main()
            {
                s v;
                v.a = 1;
                v.b1 = 2;
                v.c = 3;
                v.d = 4;
                return 0;
            }
        "#;

        let mir_dump = setup_mir(source);
        insta::assert_snapshot!(mir_dump, @"
        type %t0 = i32
        type %t1 = struct anonymous { a: %t0, __anon_1: %t2, __anon_2: %t3, __anon_3: %t6 }
        type %t2 = union anonymous { b1: %t0, b2: %t0 }
        type %t3 = struct anonymous { __anon_0: %t4 }
        type %t4 = union anonymous { __anon_0: %t5 }
        type %t5 = struct anonymous { c: %t0 }
        type %t6 = struct anonymous { d: %t0 }

        fn main() -> i32
        {
          locals {
            %v: %t1
          }

          bb1:
            %v.field_0 = cast<i32>(const 1)
            %v.field_1.field_0 = cast<i32>(const 2)
            %v.field_2.field_0.field_0.field_0 = cast<i32>(const 3)
            %v.field_3.field_0 = cast<i32>(const 4)
            return cast<i32>(const 0)
        }
        ");
    }
}
