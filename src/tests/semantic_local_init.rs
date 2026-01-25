use super::semantic_common::setup_mir;

#[test]
fn test_local_array_designator_simple() {
    let source = r#"
        int main() {
            int a[5] = {[1] = 10, [3] = 30};
            return 0;
        }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @r"
    type %t0 = i32
    type %t1 = [5]%t0

    fn main() -> i32
    {
      locals {
        %a: [5]i32
      }

      bb1:
        %a = [const zero, const 10, const zero, const 30, const zero]
        return const 0
    }
    ");
}

#[test]
fn test_local_array_designator_out_of_order() {
    let source = r#"
        int main() {
            int a[5] = {[3] = 30, [1] = 10};
            return 0;
        }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @r"
    type %t0 = i32
    type %t1 = [5]%t0

    fn main() -> i32
    {
      locals {
        %a: [5]i32
      }

      bb1:
        %a = [const zero, const 10, const zero, const 30, const zero]
        return const 0
    }
    ");
}

#[test]
fn test_local_struct_designator_simple() {
    let source = r#"
        struct S { int x; int y; };
        int main() {
            struct S s = {.y = 2, .x = 1};
            return 0;
        }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @r"
    type %t0 = i32
    type %t1 = struct S { x: %t0, y: %t0 }

    fn main() -> i32
    {
      locals {
        %s: %t1
      }

      bb1:
        %s = struct{1: const 2, 0: const 1}
        return const 0
    }
    ");
}

#[test]
fn test_local_mixed_array_struct_designators() {
    let source = r#"
        struct S { int arr[3]; int val; };
        int main() {
            struct S s = { .val = 99, .arr = {[1] = 10} };
            return 0;
        }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @r"
    type %t0 = i32
    type %t1 = struct S { arr: %t2, val: %t0 }
    type %t2 = [3]%t0

    fn main() -> i32
    {
      locals {
        %s: %t1
        %2: [3]i32
      }

      bb1:
        %2 = [const zero, const 10, const zero]
        %s = struct{1: const 99, 0: %2}
        return const 0
    }
    ");
}

#[test]
fn test_local_nested_array_init() {
    let source = r#"
        int main() {
            int grid[2][2] = { {1, 2}, {3, 4} };
            return 0;
        }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @r"
    type %t0 = i32
    type %t1 = [2]%t0
    type %t2 = [2]%t1

    fn main() -> i32
    {
      locals {
        %grid: [2][2]i32
        %2: [2]i32
        %3: [2]i32
      }

      bb1:
        %2 = [const 1, const 2]
        %3 = [const 3, const 4]
        %grid = [%2, %3]
        return const 0
    }
    ");
}

#[test]
fn test_local_nested_array_init_with_designators() {
    let source = r#"
        int main() {
            int grid[2][2] = { [1] = {[0] = 3, [1] = 4}, [0] = {1, 2} };
            return 0;
        }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @r"
    type %t0 = i32
    type %t1 = [2]%t0
    type %t2 = [2]%t1

    fn main() -> i32
    {
      locals {
        %grid: [2][2]i32
        %2: [2]i32
        %3: [2]i32
      }

      bb1:
        %2 = [const 3, const 4]
        %3 = [const 1, const 2]
        %grid = [%3, %2]
        return const 0
    }
    ");
}

#[test]
fn test_local_partial_init_implicit_zero() {
    let source = r#"
        struct S { int x; int y; int z; };
        int main() {
            struct S s = { .y = 5 };
            // x and z should be implicitly zeroed
            return 0;
        }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @r"
    type %t0 = i32
    type %t1 = struct S { x: %t0, y: %t0, z: %t0 }

    fn main() -> i32
    {
      locals {
        %s: %t1
      }

      bb1:
        %s = struct{1: const 5}
        return const 0
    }
    ");
}
