use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_pass;

#[test]
fn test_sizeof_vla_supported() {
    run_pass(
        r#"
        int main() {
            int n = 10;
            char arr[n];
            int size = sizeof(arr);
            return 0;
        }
        "#,
        CompilePhase::EmitObject,
    );
}

#[test]
fn test_sizeof_array_constant_expression() {
    run_pass(
        r#"
        int main() {
            char a[10];
            char b[20];
            char c[sizeof(a) + sizeof(b)];
            return 0;
        }
        "#,
        CompilePhase::EmitObject,
    );
}

#[test]
fn test_sizeof_string_literal_constant_expression() {
    run_pass(
        r#"
        #define LUA_SIGNATURE "\x1bLua"
        #define LUAC_DATA "\x19\x93\r\n\x1a\n"

        int main() {
            char buff[sizeof(LUA_SIGNATURE) + sizeof(LUAC_DATA)];
            return 0;
        }
        "#,
        CompilePhase::EmitObject,
    );
}
