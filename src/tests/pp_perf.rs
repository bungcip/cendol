use crate::tests::pp_common::setup_preprocessor_test_with_diagnostics;
use std::time::Instant;

#[test]
fn test_macro_expansion_perf() {
    let src = r#"
#define M1(x) x x
#define M2(x) M1(x) M1(x)
#define M3(x) M2(x) M2(x)
#define M4(x) M3(x) M3(x)
#define M5(x) M4(x) M4(x)
#define M6(x) M5(x) M5(x)
#define M7(x) M6(x) M6(x)
#define M8(x) M7(x) M7(x)
#define M9(x) M8(x) M8(x)
#define M10(x) M9(x) M9(x)

M10(TOKEN)
"#;

    let start = Instant::now();
    let iterations = 200;
    for _ in 0..iterations {
        let _ = setup_preprocessor_test_with_diagnostics(src, None).unwrap();
    }
    let duration = start.elapsed();
    println!("\nMacro expansion performance ({} iterations): {:?}", iterations, duration);
}
