//! tests for struct and union member access
use insta::assert_yaml_snapshot;
use cendol::test_utils::compile_and_run;

#[test]
fn test_struct_member_access() {
    let c_program = r#"
    struct Point {
        int x;
        int y;
    };

    int main() {
        struct Point p;
        p.x = 10;
        p.y = 20;
        return p.x + p.y;
    }
    "#;
    let result = compile_and_run(c_program, "struct_member_access");
    assert_yaml_snapshot!("struct_member_access", result.unwrap());
}

#[test]
fn test_union_member_access() {
    let c_program = r#"
    union Data {
        int i;
        float f;
    };

    int main() {
        union Data d;
        d.i = 10;
        return d.i;
    }
    "#;
    let result = compile_and_run(c_program, "union_member_access");
    assert_yaml_snapshot!("union_member_access", result.unwrap());
}

#[test]
fn test_pointer_member_access() {
    let c_program = r#"
    struct Point {
        int x;
        int y;
    };

    int main() {
        struct Point p;
        struct Point *ptr = &p;
        ptr->x = 10;
        ptr->y = 20;
        return ptr->x + ptr->y;
    }
    "#;
    let result = compile_and_run(c_program, "pointer_member_access");
    assert_yaml_snapshot!("pointer_member_access", result.unwrap());
}
