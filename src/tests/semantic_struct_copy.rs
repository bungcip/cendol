use super::semantic_common::setup_mir;

#[test]
fn test_struct_copy_init() {
    let source = r#"
        struct Wrap {
            void *func;
        };
        int global;
        void inc_global (void) { global++; }
        struct Wrap global_wrap[] = {
            ((struct Wrap) {inc_global}),
            inc_global,
        };
        int main() { return 0; }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @r"
    type %t0 = i32
    type %t1 = void
    type %t2 = struct Wrap { func: %t3 }
    type %t3 = ptr<%t1>
    type %t4 = [2]%t2
    type %t5 = fn() -> %t1

    global @global: i32 = const zero
    global @.L.str0: %t2 = const struct_literal { 0: const inc_global }
    global @global_wrap: [2]%t2 = const array_literal [const struct_literal { 0: const inc_global }, const struct_literal { 0: const inc_global }]

    fn main() -> i32
    {

      bb2:
        return const 0
    }

    fn inc_global() -> void
    {

      bb1:
        @global = @global + const 1
        return
    }
    ");
}
