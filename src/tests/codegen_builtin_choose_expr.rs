use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_pass;

#[test]
fn test_codegen_choose_expr_basic() {
    let source = "
        extern int putchar(int);
        int main() {
            __builtin_choose_expr(1, putchar('A'), putchar('B'));
            __builtin_choose_expr(0, putchar('C'), putchar('D'));
            return 0;
        }
    ";
    // We can't easily check output here without a full runtime test,
    // but we can at least ensure it compiles to MIR without issues.
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_codegen_choose_expr_side_effects() {
    let source = "
        int main() {
            int x = 0;
            int y = __builtin_choose_expr(1, x = 10, x = 20);
            if (x != 10) return 1;

            int z = __builtin_choose_expr(0, x = 30, x = 40);
            if (x != 40) return 2;

            return 0;
        }
    ";
    run_pass(source, CompilePhase::Mir);
}
