use crate::tests::codegen_common::run_c_code_exit_status;
use crate::tests::test_utils::run_fail_with_message;

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
        int a[2] = { [0 ... 1] = 1, 2 }; // Error: index 2 is out of bounds
        return 0;
    }
    "#;
    run_fail_with_message(source, "excess elements");
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
