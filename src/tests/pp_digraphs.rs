use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::*;

#[test]
fn test_digraph_basic() {
    run_pass(
        r#"
        int main() <%
            int arr<:5:> = <% 1, 2, 3, 4, 5 %>;
            return arr<:0:> - 1;
        %>
        "#,
        CompilePhase::Cranelift,
    );
}

#[test]
fn test_digraph_hash() {
    run_pass(
        r#"
        %:define X 1
        int main() {
            return X - 1;
        }
        "#,
        CompilePhase::Cranelift,
    );
}

#[test]
fn test_digraph_hashhash() {
    run_pass(
        r#"
        #define GLUE(a, b) a %:%: b
        int main() {
            int xy = 42;
            return GLUE(x, y) - 42;
        }
        "#,
        CompilePhase::Cranelift,
    );
}
