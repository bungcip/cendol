use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::*;

#[test]
fn test_pp_digraphs_basic() {
    // <:  -> [
    // :>  -> ]
    // <%  -> {
    // %>  -> }
    run_pass(
        r#"
        int main() <%
            int arr<:5:>;
            return 0;
        %>
        "#,
        CompilePhase::Parse,
    );
}

#[test]
fn test_pp_digraph_directive() {
    // %:  -> #
    run_pass(
        r#"
        %:define FOO 42
        int x = FOO;
        "#,
        CompilePhase::Parse,
    );
}

#[test]
fn test_pp_digraph_pasting() {
    // %:%: -> ##
    run_pass(
        r#"
        #define GLUE(a, b) a %:%: b
        int GLUE(x, 1) = 42;
        "#,
        CompilePhase::Parse,
    );
}

#[test]
fn test_pp_digraph_hash_hash_mixed() {
    run_pass(
        r#"
        #define GLUE1(a, b) a ## b
        #define GLUE2(a, b) a %:%: b
        int GLUE1(var, 1) = 1;
        int GLUE2(var, 2) = 2;
        "#,
        CompilePhase::Parse,
    );
}

#[test]
fn test_pp_digraph_all() {
    run_pass(
        r#"
        %:define STR(x) %:x
        const char *s = STR(hello);

        int main() <%
            int a<:2:> = <% 1, 2 %>;
            return 0;
        %>
        "#,
        CompilePhase::Parse,
    );
}

#[test]
fn test_pp_digraph_skipping() {
    run_pass(
        r#"
        #if 0
        %:define FAKE
        #endif

        %:if 0
        #define ALSO_FAKE
        %:endif

        int x = 0;
        "#,
        CompilePhase::Parse,
    );
}
