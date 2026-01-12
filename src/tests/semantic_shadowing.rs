use super::semantic_common::run_full_pass;

#[test]
fn test_nested_scope_shadowing() {
    run_full_pass(
        r#"
        typedef struct s s;
        struct s {
            int x;
        };

        int main() {
            struct s s;
            s.x = 1;
            {
                int s = 2;
                if (s != 2) return 1;
            }
            return s.x - 1;
        }
        "#,
    );
}
