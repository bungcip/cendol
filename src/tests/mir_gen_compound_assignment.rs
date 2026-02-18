use super::semantic_common::setup_mir;

#[test]
fn test_compound_assignment_truncation() {
    let source = r#"
        typedef unsigned char uint8_t;
        typedef unsigned long long uint64_t;

        struct foo {
            uint8_t a;
        };

        uint64_t test8(struct foo *f, uint64_t val) {
            return (f->a += val);
        }
    "#;

    let mir_dump = setup_mir(source);

    // We expect:
    // 1. Addition of f->a (promoted) + val -> result (u64)
    // 2. Truncation of result to u8 (LHS type)
    // 3. Assignment of truncated result to f->a
    // 4. Conversion of truncated result back to u64 (for return)

    insta::assert_snapshot!(mir_dump, @r"
    type %t0 = u64
    type %t1 = struct foo { a: %t2 }
    type %t2 = u8
    type %t3 = ptr<%t1>
    type %t4 = i32

    fn test8(%param0: ptr<%t1>, %param1: u64) -> u64
    {
      locals {
        %3: u64
      }

      bb1:
        %3 = cast<u64>(cast<i32>(deref(%param0).field_0)) + %param1
        deref(%param0).field_0 = cast<u8>(%3)
        return cast<u64>(cast<u8>(cast<u64>(cast<u8>(%3))))
    }
    ");
}

#[test]
fn test_compound_assignment_truncation_16() {
    let source = r#"
        typedef unsigned short uint16_t;
        typedef unsigned long long uint64_t;

        struct foo {
            uint16_t b;
        };

        uint64_t test16(struct foo *f, uint64_t val) {
            return (f->b += val);
        }
    "#;

    let mir_dump = setup_mir(source);
    insta::assert_snapshot!(mir_dump, @r"
    type %t0 = u64
    type %t1 = struct foo { b: %t2 }
    type %t2 = u16
    type %t3 = ptr<%t1>
    type %t4 = i32

    fn test16(%param0: ptr<%t1>, %param1: u64) -> u64
    {
      locals {
        %3: u64
      }

      bb1:
        %3 = cast<u64>(cast<i32>(deref(%param0).field_0)) + %param1
        deref(%param0).field_0 = cast<u16>(%3)
        return cast<u64>(cast<u16>(cast<u64>(cast<u16>(%3))))
    }
    ");
}

#[test]
fn test_compound_assignment_truncation_32() {
    let source = r#"
        typedef unsigned int uint32_t;
        typedef unsigned long long uint64_t;

        struct foo {
            uint32_t c;
        };

        uint64_t test32(struct foo *f, uint64_t val) {
            return (f->c += val);
        }
    "#;

    // For u32 + u64 -> u64. Truncate to u32.
    let mir_dump = setup_mir(source);
    insta::assert_snapshot!(mir_dump, @r"
    type %t0 = u64
    type %t1 = struct foo { c: %t2 }
    type %t2 = u32
    type %t3 = ptr<%t1>

    fn test32(%param0: ptr<%t1>, %param1: u64) -> u64
    {
      locals {
        %3: u64
      }

      bb1:
        %3 = cast<u64>(deref(%param0).field_0) + %param1
        deref(%param0).field_0 = cast<u32>(%3)
        return cast<u64>(cast<u32>(cast<u64>(cast<u32>(%3))))
    }
    ");
}
