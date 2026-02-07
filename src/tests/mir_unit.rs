//! Direct unit tests for MIR types and utility methods

use crate::ast::NameId;
use crate::mir::{BinaryFloatOp, BinaryIntOp, MirArrayLayout, MirRecordLayout, MirType, TypeId};

#[test]
fn test_binary_int_op_is_comparison() {
    // Comparison operations
    assert!(BinaryIntOp::Eq.is_comparison());
    assert!(BinaryIntOp::Ne.is_comparison());
    assert!(BinaryIntOp::Lt.is_comparison());
    assert!(BinaryIntOp::Le.is_comparison());
    assert!(BinaryIntOp::Gt.is_comparison());
    assert!(BinaryIntOp::Ge.is_comparison());

    // Non-comparison operations
    assert!(!BinaryIntOp::Add.is_comparison());
    assert!(!BinaryIntOp::Sub.is_comparison());
    assert!(!BinaryIntOp::Mul.is_comparison());
    assert!(!BinaryIntOp::Div.is_comparison());
    assert!(!BinaryIntOp::Mod.is_comparison());
    assert!(!BinaryIntOp::BitAnd.is_comparison());
    assert!(!BinaryIntOp::BitOr.is_comparison());
    assert!(!BinaryIntOp::BitXor.is_comparison());
    assert!(!BinaryIntOp::LShift.is_comparison());
    assert!(!BinaryIntOp::RShift.is_comparison());
}

#[test]
fn test_binary_float_op_is_comparison() {
    // Comparison operations
    assert!(BinaryFloatOp::Eq.is_comparison());
    assert!(BinaryFloatOp::Ne.is_comparison());
    assert!(BinaryFloatOp::Lt.is_comparison());
    assert!(BinaryFloatOp::Le.is_comparison());
    assert!(BinaryFloatOp::Gt.is_comparison());
    assert!(BinaryFloatOp::Ge.is_comparison());

    // Non-comparison operations
    assert!(!BinaryFloatOp::Add.is_comparison());
    assert!(!BinaryFloatOp::Sub.is_comparison());
    assert!(!BinaryFloatOp::Mul.is_comparison());
    assert!(!BinaryFloatOp::Div.is_comparison());
}

#[test]
fn test_mir_type_is_signed() {
    // Signed types
    assert!(MirType::I8.is_signed());
    assert!(MirType::I16.is_signed());
    assert!(MirType::I32.is_signed());
    assert!(MirType::I64.is_signed());

    // Unsigned types
    assert!(!MirType::U8.is_signed());
    assert!(!MirType::U16.is_signed());
    assert!(!MirType::U32.is_signed());
    assert!(!MirType::U64.is_signed());
    assert!(!MirType::Bool.is_signed());

    // Other types
    assert!(!MirType::Void.is_signed());
    assert!(!MirType::F32.is_signed());
    assert!(!MirType::F64.is_signed());
}

#[test]
fn test_mir_type_is_pointer() {
    // Pointer type
    let ptr_type = MirType::Pointer {
        pointee: TypeId::new(1).unwrap(),
    };
    assert!(ptr_type.is_pointer());

    // Non-pointer types
    assert!(!MirType::I32.is_pointer());
    assert!(!MirType::F64.is_pointer());
    assert!(!MirType::Void.is_pointer());
    assert!(!MirType::Bool.is_pointer());
}

#[test]
fn test_mir_type_is_float() {
    // Float types
    assert!(MirType::F32.is_float());
    assert!(MirType::F64.is_float());
    assert!(MirType::F80.is_float());
    assert!(MirType::F128.is_float());

    // Non-float types
    assert!(!MirType::I32.is_float());
    assert!(!MirType::U64.is_float());
    assert!(!MirType::Bool.is_float());
    assert!(!MirType::Void.is_float());
}

#[test]
fn test_mir_type_is_aggregate() {
    // Aggregate types
    let record_type = MirType::Record {
        name: NameId::new("TestStruct".to_string()),
        field_types: vec![],
        field_names: vec![],
        is_union: false,
        layout: MirRecordLayout {
            size: 0,
            alignment: 1,
            field_offsets: vec![],
        },
    };
    assert!(record_type.is_aggregate());

    let array_type = MirType::Array {
        element: TypeId::new(1).unwrap(),
        size: 10,
        layout: MirArrayLayout {
            size: 40,
            align: 4,
            stride: 4,
        },
    };
    assert!(array_type.is_aggregate());

    // Non-aggregate types
    assert!(!MirType::I32.is_aggregate());
    assert!(!MirType::F64.is_aggregate());
    assert!(!MirType::Bool.is_aggregate());
    assert!(!MirType::Void.is_aggregate());
}

#[test]
fn test_mir_type_is_int() {
    // Integer types
    assert!(MirType::I8.is_int());
    assert!(MirType::I16.is_int());
    assert!(MirType::I32.is_int());
    assert!(MirType::I64.is_int());
    assert!(MirType::U8.is_int());
    assert!(MirType::U16.is_int());
    assert!(MirType::U32.is_int());
    assert!(MirType::U64.is_int());
    assert!(MirType::Bool.is_int());

    // Non-integer types
    assert!(!MirType::F32.is_int());
    assert!(!MirType::F64.is_int());
    assert!(!MirType::F80.is_int());
    assert!(!MirType::F128.is_int());
    assert!(!MirType::Void.is_int());
}

#[test]
fn test_mir_type_width() {
    // 8-bit types
    assert_eq!(MirType::I8.width(), 8);
    assert_eq!(MirType::U8.width(), 8);
    assert_eq!(MirType::Bool.width(), 8);

    // 16-bit types
    assert_eq!(MirType::I16.width(), 16);
    assert_eq!(MirType::U16.width(), 16);

    // 32-bit types
    assert_eq!(MirType::I32.width(), 32);
    assert_eq!(MirType::U32.width(), 32);
    assert_eq!(MirType::F32.width(), 32);

    // 64-bit types
    assert_eq!(MirType::I64.width(), 64);
    assert_eq!(MirType::U64.width(), 64);
    assert_eq!(MirType::F64.width(), 64);

    // 128-bit types
    assert_eq!(MirType::F80.width(), 128);
    assert_eq!(MirType::F128.width(), 128);

    // Pointer (64-bit assumed)
    let ptr_type = MirType::Pointer {
        pointee: TypeId::new(1).unwrap(),
    };
    assert_eq!(ptr_type.width(), 64);

    // Types without intrinsic width
    assert_eq!(MirType::Void.width(), 0);

    let record_type = MirType::Record {
        name: NameId::new("TestStruct".to_string()),
        field_types: vec![],
        field_names: vec![],
        is_union: false,
        layout: MirRecordLayout {
            size: 0,
            alignment: 1,
            field_offsets: vec![],
        },
    };
    assert_eq!(record_type.width(), 0);
}

#[test]
fn test_mir_type_predicates_combinations() {
    // Test combinations to ensure predicates are exclusive where expected

    // Signed integers should be int but not float
    assert!(MirType::I32.is_signed());
    assert!(MirType::I32.is_int());
    assert!(!MirType::I32.is_float());
    assert!(!MirType::I32.is_pointer());
    assert!(!MirType::I32.is_aggregate());

    // Unsigned integers should be int but not signed
    assert!(!MirType::U32.is_signed());
    assert!(MirType::U32.is_int());
    assert!(!MirType::U32.is_float());
    assert!(!MirType::U32.is_pointer());
    assert!(!MirType::U32.is_aggregate());

    // Float types
    assert!(!MirType::F64.is_signed());
    assert!(!MirType::F64.is_int());
    assert!(MirType::F64.is_float());
    assert!(!MirType::F64.is_pointer());
    assert!(!MirType::F64.is_aggregate());

    // Pointer types
    let ptr = MirType::Pointer {
        pointee: TypeId::new(1).unwrap(),
    };
    assert!(!ptr.is_signed());
    assert!(!ptr.is_int());
    assert!(!ptr.is_float());
    assert!(ptr.is_pointer());
    assert!(!ptr.is_aggregate());

    // Array types
    let arr = MirType::Array {
        element: TypeId::new(1).unwrap(),
        size: 5,
        layout: MirArrayLayout {
            size: 20,
            align: 4,
            stride: 4,
        },
    };
    assert!(!arr.is_signed());
    assert!(!arr.is_int());
    assert!(!arr.is_float());
    assert!(!arr.is_pointer());
    assert!(arr.is_aggregate());
}
