#[cfg(test)]
mod tests {
    use crate::driver::artifact::CompilePhase;
    use crate::tests::test_utils::run_pass;

    #[test]
    fn test_generic_selection_lvalue() {
        run_pass(
            r#"
        int main() {
            int x = 0;
            _Generic(0, int: x, default: x) = 10;
            if (x != 10) return 1;
            return 0;
        }
        "#,
            CompilePhase::Mir,
        );
    }

    #[test]
    fn test_generic_selection_lvalue_struct() {
        run_pass(
            r#"
        struct S { int a; };
        int main() {
            struct S s = {0};
            _Generic(0, int: s, default: s).a = 10;
            if (s.a != 10) return 1;
            return 0;
        }
        "#,
            CompilePhase::Mir,
        );
    }
}
