use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_semantic_popcount() {
    run_pass("int main() { return __builtin_popcount(42); }", CompilePhase::Mir);
    run_pass("int main() { return __builtin_popcountl(42L); }", CompilePhase::Mir);
    run_pass("int main() { return __builtin_popcountll(42LL); }", CompilePhase::Mir);
}

#[test]
fn test_semantic_clz() {
    run_pass("int main() { return __builtin_clz(42); }", CompilePhase::Mir);
    run_pass("int main() { return __builtin_clzl(42L); }", CompilePhase::Mir);
    run_pass("int main() { return __builtin_clzll(42LL); }", CompilePhase::Mir);
}

#[test]
fn test_semantic_ctz() {
    run_pass("int main() { return __builtin_ctz(42); }", CompilePhase::Mir);
    run_pass("int main() { return __builtin_ctzl(42L); }", CompilePhase::Mir);
    run_pass("int main() { return __builtin_ctzll(42LL); }", CompilePhase::Mir);
}

#[test]
fn test_semantic_bitwise_invalid_type() {
    run_fail_with_message(
        "int main() { return __builtin_popcount(42.0); }",
        "type mismatch: expected integer type, found double",
    );
    run_fail_with_message(
        "int main() { return __builtin_clz(\"hello\"); }",
        "type mismatch: expected integer type, found char*",
    );
}
