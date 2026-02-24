#[cfg(test)]
mod tests {
    use crate::driver::artifact::CompilePhase;
    use crate::tests::test_utils::{run_pass, run_pass_with_diagnostic};

    #[test]
    fn warns_on_large_enum_constant() {
        let source = "enum T { A = 4294967296LL };";
        run_pass_with_diagnostic(
            source,
            CompilePhase::Mir,
            "enumerator value 4294967296 for 'A' is not representable as 'int'",
            1,
            10,
        );
    }

    #[test]
    fn accepts_boundary_enum_constants() {
        let source = "
            enum T {
                MAX_INT = 2147483647,
                MIN_INT = -2147483648
            };
        ";
        run_pass(source, CompilePhase::Mir);
    }

    #[test]
    fn warns_on_overflow_next_value() {
        let source = "enum T { A = 2147483647, B };";
        run_pass_with_diagnostic(
            source,
            CompilePhase::Mir,
            "enumerator value 2147483648 for 'B' is not representable as 'int'",
            1,
            26,
        );
    }

    #[test]
    fn warns_on_underflow_large_negative() {
        let source = "enum T { A = -2147483649LL };";
        run_pass_with_diagnostic(
            source,
            CompilePhase::Mir,
            "enumerator value -2147483649 for 'A' is not representable as 'int'",
            1,
            10,
        );
    }

    #[test]
    fn warns_on_extreme_i64_values() {
        let source = "enum T { A = 9223372036854775807LL };";
        run_pass_with_diagnostic(
            source,
            CompilePhase::Mir,
            "enumerator value 9223372036854775807 for 'A' is not representable as 'int'",
            1,
            10,
        );
    }
}
