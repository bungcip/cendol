use crate::driver::artifact::CompilePhase;
use crate::tests::codegen_common::run_c_code_exit_status;
use crate::tests::test_utils::run_pass_with_diagnostic_message;

#[test]
fn test_init_range_index_advancement() {
    let source = r#"
    int main() {
        int a[5] = { [0 ... 2] = 1, 2, 3 };
        // a[0]=1, a[1]=1, a[2]=1, a[3]=2, a[4]=3
        if (a[0] != 1) return 1;
        if (a[1] != 1) return 2;
        if (a[2] != 1) return 3;
        if (a[3] != 2) return 4;
        if (a[4] != 3) return 5;
        return 0;
    }
    "#;
    assert_eq!(run_c_code_exit_status(source), 0);
}

#[test]
fn test_init_range_excess_elements() {
    let source = r#"
    int main() {
        int a[2] = { [0 ... 1] = 1, 2 }; // Warning: index 2 is out of bounds
        return 0;
    }
    "#;
    run_pass_with_diagnostic_message(source, CompilePhase::Mir, "excess elements");
}

#[test]
fn test_init_range_deduce_size() {
    let source = r#"
    int a[] = { [0 ... 2] = 1, 10 };
    int main() {
        if (sizeof(a) != 4 * sizeof(int)) return 1;
        if (a[3] != 10) return 2;
        return 0;
    }
    "#;
    assert_eq!(run_c_code_exit_status(source), 0);
}

#[test]
fn test_init_range_nested_aggregate_override() {
    let source = r#"
    struct S { int x; int y[3]; };
    int main() {
        struct S a[5] = {
            [0 ... 4].x = 1,
            [0 ... 4].y[0 ... 2] = 2,
            [2 ... 3].y[1 ... 2] = 3
        };
        for (int i = 0; i < 5; i++) {
            if (a[i].x != 1) return 100 + i;
            if (i == 2 || i == 3) {
                if (a[i].y[0] != 2) return 200 + i;
                if (a[i].y[1] != 3) return 300 + i;
                if (a[i].y[2] != 3) return 400 + i;
            } else {
                if (a[i].y[0] != 2) return 500 + i;
                if (a[i].y[1] != 2) return 600 + i;
                if (a[i].y[2] != 2) return 700 + i;
            }
        }
        return 0;
    }
    "#;
    assert_eq!(run_c_code_exit_status(source), 0);
}
