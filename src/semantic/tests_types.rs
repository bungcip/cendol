use super::ArraySizeType;
use super::type_registry::TypeRegistry;
use super::types::{TypeClass, TypeRef};

#[test]
fn test_typeref_encoding_primitive() {
    // BASE=1, CLASS=Builtin, PTR=0, ARR=0
    let t = TypeRef::new(1, TypeClass::Builtin, 0, 0).expect("Should create builtin");
    assert_eq!(t.base(), 1);
    assert_eq!(t.class(), TypeClass::Builtin);
    assert_eq!(t.pointer_depth(), 0);
    assert_eq!(t.array_len(), None);
    assert!(t.is_builtin());
    assert!(!t.is_pointer());
    assert!(!t.is_array());
    assert!(!t.is_inline_pointer());
    assert!(!t.is_registry_pointer());
}

#[test]
fn test_typeref_encoding_inline_ptr() {
    // BASE=10, CLASS=Pointer, PTR=2, ARR=0 (int**)
    let t = TypeRef::new(10, TypeClass::Pointer, 2, 0).expect("Should create inline pointer");
    assert_eq!(t.base(), 10);
    assert_eq!(t.class(), TypeClass::Pointer);
    assert_eq!(t.pointer_depth(), 2);
    assert!(t.is_pointer());
    assert!(t.is_inline_pointer());
    assert!(!t.is_registry_pointer());
}

#[test]
fn test_typeref_encoding_registry_ptr() {
    // BASE=100, CLASS=Pointer, PTR=0, ARR=0 (int**** stored in registry)
    let t = TypeRef::new(100, TypeClass::Pointer, 0, 0).expect("Should create registry pointer");
    assert_eq!(t.base(), 100);
    assert_eq!(t.class(), TypeClass::Pointer);
    assert_eq!(t.pointer_depth(), 0);
    assert!(t.is_pointer());
    assert!(!t.is_inline_pointer());
    assert!(t.is_registry_pointer());
}

#[test]
fn test_typeref_encoding_inline_array() {
    // BASE=20, CLASS=Array, PTR=0, ARR=10 (int[10])
    let t = TypeRef::new(20, TypeClass::Array, 0, 10).expect("Should create inline array");
    assert_eq!(t.base(), 20);
    assert_eq!(t.class(), TypeClass::Array);
    assert_eq!(t.array_len(), Some(10));
    assert!(t.is_array());
    assert!(t.is_inline_array());
    assert!(!t.is_registry_array());
}

#[test]
fn test_typeref_encoding_registry_array() {
    // BASE=500, CLASS=Array, PTR=0, ARR=0 (int[100] stored in registry)
    let t = TypeRef::new(500, TypeClass::Array, 0, 0).expect("Should create registry array");
    assert_eq!(t.base(), 500);
    assert_eq!(t.class(), TypeClass::Array);
    assert_eq!(t.array_len(), None);
    assert!(t.is_array());
    assert!(!t.is_inline_array());
    assert!(t.is_registry_array());
}

#[test]
fn test_typeref_invalid_combinations() {
    // Builtin with pointer
    assert!(TypeRef::new(1, TypeClass::Builtin, 1, 0).is_none());
    // Pointer with array
    assert!(TypeRef::new(1, TypeClass::Pointer, 1, 5).is_none());
    // Array with pointer
    assert!(TypeRef::new(1, TypeClass::Array, 1, 5).is_none());
    // Pointer with depth > 3
    assert!(TypeRef::new(1, TypeClass::Pointer, 4, 0).is_none());
    // Array with size > 31
    assert!(TypeRef::new(1, TypeClass::Array, 0, 32).is_none());
}

#[test]
fn test_typeregistry_inline_logic() {
    let mut reg = TypeRegistry::new();
    let int_ty = reg.type_int;
    assert!(int_ty.is_builtin());

    // int* (Inline)
    let p1 = reg.pointer_to(int_ty);
    assert_eq!(p1.class(), TypeClass::Pointer);
    assert_eq!(p1.pointer_depth(), 1);
    assert_eq!(p1.base(), int_ty.base()); // Base is int
    assert!(p1.is_inline_pointer());

    // int** (Inline)
    let p2 = reg.pointer_to(p1);
    assert_eq!(p2.class(), TypeClass::Pointer);
    assert_eq!(p2.pointer_depth(), 2);
    assert_eq!(p2.base(), int_ty.base());
    assert!(p2.is_inline_pointer());

    // int*** (Inline)
    let p3 = reg.pointer_to(p2);
    assert_eq!(p3.class(), TypeClass::Pointer);
    assert_eq!(p3.pointer_depth(), 3);
    assert_eq!(p3.base(), int_ty.base());

    // int**** (Registry)
    let p4 = reg.pointer_to(p3);
    assert_eq!(p4.class(), TypeClass::Pointer);
    assert_eq!(p4.pointer_depth(), 0); // Registry pointer
    assert!(p4.is_registry_pointer());
    // Base of p4 is the index in registry where Type::Pointer{pointee: int***} is stored.
    // We can't easily assert the index value, but it should differ from int_ty.base().
    assert_ne!(p4.base(), int_ty.base());

    // int***** (Inline, base = int****)
    let p5 = reg.pointer_to(p4);
    assert_eq!(p5.class(), TypeClass::Pointer);
    assert_eq!(p5.pointer_depth(), 1);
    assert_eq!(p5.base(), p4.base()); // Base is the registry pointer type
}

#[test]
fn test_typeregistry_array_logic() {
    let mut reg = TypeRegistry::new();
    let int_ty = reg.type_int;

    // int[10] (Inline)
    let a1 = reg.array_of(int_ty, ArraySizeType::Constant(10));
    assert_eq!(a1.class(), TypeClass::Array);
    assert_eq!(a1.array_len(), Some(10));
    assert_eq!(a1.base(), int_ty.base());
    assert!(a1.is_inline_array());

    // int[100] (Registry)
    let a2 = reg.array_of(int_ty, ArraySizeType::Constant(100));
    assert_eq!(a2.class(), TypeClass::Array);
    assert_eq!(a2.array_len(), None); // Registry array
    assert!(a2.is_registry_array());
    assert_ne!(a2.base(), int_ty.base());

    // int*[5] (Registry - because int* doesn't have an index)
    // Wait, check logic again.
    // int* is Inline Pointer (Base=Int, Ptr=1).
    // array_of checks if elem is Simple (Ptr=0, Arr=0).
    // int* is NOT Simple.
    // So int*[5] must be Registry Array.
    let p1 = reg.pointer_to(int_ty); // int*
    let ap1 = reg.array_of(p1, ArraySizeType::Constant(5));
    assert_eq!(ap1.class(), TypeClass::Array);
    assert_eq!(ap1.array_len(), None); // Registry array
    assert!(ap1.is_registry_array());

    // int[10]* (Registry Pointer)
    // int[10] is Inline Array (Base=Int, Arr=10). Not Simple.
    // So pointer_to(int[10]) must be Registry Pointer.
    let pa1 = reg.pointer_to(a1);
    assert_eq!(pa1.class(), TypeClass::Pointer);
    assert_eq!(pa1.pointer_depth(), 0); // Registry pointer
    assert!(pa1.is_registry_pointer());
}

#[test]
fn test_reconstruct_type() {
    let mut reg = TypeRegistry::new();
    let int_ty = reg.type_int;

    // Reconstruct int*
    let p1 = reg.pointer_to(int_ty);
    let cow_p1 = reg.get(p1);
    if let crate::semantic::TypeKind::Pointer { pointee } = cow_p1.kind {
        assert_eq!(pointee, int_ty);
    } else {
        panic!("Expected Pointer kind");
    }

    // Reconstruct int**
    let p2 = reg.pointer_to(p1);
    let cow_p2 = reg.get(p2);
    if let crate::semantic::TypeKind::Pointer { pointee } = cow_p2.kind {
        assert_eq!(pointee, p1);
    } else {
        panic!("Expected Pointer kind");
    }

    // Reconstruct int[10]
    let a1 = reg.array_of(int_ty, ArraySizeType::Constant(10));
    let cow_a1 = reg.get(a1);
    if let crate::semantic::TypeKind::Array { element_type, size } = &cow_a1.kind {
        assert_eq!(*element_type, int_ty);
        if let ArraySizeType::Constant(sz) = size {
            assert_eq!(*sz, 10);
        } else {
            panic!("Expected Constant size");
        }
    } else {
        panic!("Expected Array kind");
    }
}
