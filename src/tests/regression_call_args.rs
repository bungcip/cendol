//! Regression test for ICE with call arguments node visiting
//!
//! This test ensures that complex expressions in function arguments
//! are correctly visited by the semantic analyzer and do not cause
//! "ident not have resolved type" panics.

use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils;

#[test]
fn test_complex_call_args_visiting() {
    let source = r#"
void *calloc(long unsigned int nmemb, long unsigned int size);

int N;
int *t;

int
chk(int x, int y)
{
        int i;
        int r;

        for (r=i=0; i<8; i++) {
                r = r + t[x + 8*i];
                r = r + t[i + 8*y];
                if (x+i < 8 & y+i < 8)
                        r = r + t[x+i + 8*(y+i)];
                if (x+i < 8 & y-i >= 0)
                        r = r + t[x+i + 8*(y-i)];
                if (x-i >= 0 & y+i < 8)
                        r = r + t[x-i + 8*(y+i)];
                if (x-i >= 0 & y-i >= 0)
                        r = r + t[x-i + 8*(y-i)];
        }
        return r;
}

int
go(int n, int x, int y)
{
        if (n == 8) {
                N++;
                return 0;
        }
        for (; y<8; y++) {
                for (; x<8; x++)
                        if (chk(x, y) == 0) {
                                t[x + 8*y]++;
                                go(n+1, x, y);
                                t[x + 8*y]--;
                        }
                x = 0;
        }
	return 0;
}

int
main()
{
        t = calloc(64, sizeof(int));
        go(0, 0, 0);
        if(N != 92)
		return 1;
        return 0;
}
"#;

    let (driver, _res) = test_utils::run_pipeline(source, CompilePhase::Mir);

    // If we reach here without panic, the test passes.
    // We can also check that there are no errors.
    let diagnostics = driver.get_diagnostics();
    assert!(
        !diagnostics
            .iter()
            .any(|d| d.level == crate::diagnostic::DiagnosticLevel::Error),
        "Compilation failed with errors: {:?}",
        diagnostics
    );
}
