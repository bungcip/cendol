use crate::tests::parser_utils::*;

#[test]
fn test_pragma_in_struct() {
    insta::assert_debug_snapshot!(setup_declaration(
        "
        struct S {
            #pragma GCC visibility push(hidden)
            int a;
            #pragma GCC visibility pop
            #pragma pack(push, 1)
            int b;
            #pragma pack(pop)
            int c;
        };
    "
    ));
}
