use super::semantic_common::{setup_lowering, setup_mir};
use crate::ast::NameId;
use crate::driver::artifact::CompilePhase;
use crate::semantic::ArraySizeType;
use crate::semantic::type_registry::TypeRegistry;
use crate::semantic::types::{QualType, TypeClass, TypeRef};
use crate::tests::test_utils::{run_fail, run_pass, setup_diagnostics_output};

fn check_type(source: &str, expected: &str) {
    let (_ast, registry, symbol_table) = setup_lowering(source);
    let (entry, _) = symbol_table.lookup_symbol(NameId::from("x")).unwrap();
    let symbol = symbol_table.get_symbol(entry);
    assert_eq!(registry.display_qual_type(symbol.type_info), expected);
}

#[test]
fn test_long_unsigned_int() {
    check_type("long unsigned int x;", "unsigned long");
}

#[test]
fn test_unsigned_long_int() {
    check_type("unsigned long int x;", "unsigned long");
}

#[test]
fn test_long_int() {
    check_type("long int x;", "long");
}
#[test]
fn test_typeregistry_default() {
    let registry = crate::semantic::TypeRegistry::default();
    assert_eq!(registry.types.len(), 20); // dummy + 19 built-ins
}

#[test]
fn test_short_int() {
    check_type("short int x;", "short");
}

#[test]
fn test_unsigned_short_int() {
    check_type("unsigned short int x;", "unsigned short");
}

#[test]
fn test_long_long_int() {
    check_type("long long int x;", "long long");
}

#[test]
fn test_unsigned_long_long_int() {
    check_type("unsigned long long int x;", "unsigned long long");
}

#[test]
fn test_long_double() {
    check_type("long double x;", "long double");
}

#[test]
fn test_long_const_long() {
    check_type("long const long x;", "const long long");
}

#[test]
fn test_unsigned_long_const_long() {
    check_type("unsigned long const long x;", "const unsigned long long");
}

#[test]
fn test_restrict_array_of_pointers() {
    let code = r#"
        int main() {
            int x;
            int * restrict arr[10];
            arr[0] = &x;
        }
    "#;
    run_pass(code, CompilePhase::Mir);
}

#[test]
fn test_signed_int() {
    let code = "typedef signed int int32_t; int main() { int32_t x = 0; return 0; }";
    run_pass(code, CompilePhase::Mir);
}

#[test]
fn test_signed_long() {
    let code = "typedef signed long int64_t; int main() { int64_t l = 0; return 0; }";
    run_pass(code, CompilePhase::Mir);
}

#[test]
fn test_signed_char() {
    let code = "signed char c = 'a'; int main() { return 0; }";
    run_pass(code, CompilePhase::Mir);
}

#[test]
fn test_unsigned_int() {
    let code = "unsigned int x = 0; int main() { return 0; }";
    run_pass(code, CompilePhase::Mir);
}

// Semantic validation tests for incomplete types.
#[test]
fn rejects_sizeof_on_incomplete_struct() {
    let source = r#"
        struct S;
        int main() {
            int x = sizeof(struct S);
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output, @r"
    Diagnostics count: 1

    Level: Error
    Message: Invalid application of 'sizeof' to an incomplete type
    Span: SourceSpan(source_id=SourceId(2), start=60, end=76)
    ");
}

#[test]
fn rejects_function_returning_incomplete_type() {
    let source = r#"
        struct S;
        struct S foo();
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output, @r"
    Diagnostics count: 1

    Level: Error
    Message: function has incomplete return type
    Span: SourceSpan(source_id=SourceId(2), start=27, end=42)
    ");
}

#[test]
fn rejects_sizeof_on_incomplete_array() {
    let source = r#"
        extern int arr[];
        int main() {
            int x = sizeof(arr);
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output, @r"
    Diagnostics count: 1

    Level: Error
    Message: Invalid application of 'sizeof' to an incomplete type
    Span: SourceSpan(source_id=SourceId(2), start=68, end=79)
    ");
}

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
    let mut reg = TypeRegistry::new(target_lexicon::Triple::host());
    let int_ty = reg.type_int;
    assert!(int_ty.is_builtin());

    // int* (Inline)
    let p1 = reg.pointer_to(QualType::unqualified(int_ty));
    assert_eq!(p1.class(), TypeClass::Pointer);
    assert_eq!(p1.pointer_depth(), 1);
    assert_eq!(p1.base(), int_ty.base()); // Base is int
    assert!(p1.is_inline_pointer());

    // int** (Inline)
    let p2 = reg.pointer_to(QualType::unqualified(p1));
    assert_eq!(p2.class(), TypeClass::Pointer);
    assert_eq!(p2.pointer_depth(), 2);
    assert_eq!(p2.base(), int_ty.base());
    assert!(p2.is_inline_pointer());

    // int*** (Inline)
    let p3 = reg.pointer_to(QualType::unqualified(p2));
    assert_eq!(p3.class(), TypeClass::Pointer);
    assert_eq!(p3.pointer_depth(), 3);
    assert_eq!(p3.base(), int_ty.base());

    // int**** (Registry)
    let p4 = reg.pointer_to(QualType::unqualified(p3));
    assert_eq!(p4.class(), TypeClass::Pointer);
    assert_eq!(p4.pointer_depth(), 0); // Registry pointer
    assert!(p4.is_inline_pointer() == false);
    // Base of p4 is the index in registry where Type::Pointer{pointee: int***} is stored.
    // We can't easily assert the index value, but it should differ from int_ty.base().
    assert_ne!(p4.base(), int_ty.base());

    // int***** (Inline, base = int****)
    let p5 = reg.pointer_to(QualType::unqualified(p4));
    assert_eq!(p5.class(), TypeClass::Pointer);
    assert_eq!(p5.pointer_depth(), 1);
    assert_eq!(p5.base(), p4.base()); // Base is the registry pointer type
}

#[test]
fn test_typeregistry_array_logic() {
    let mut reg = TypeRegistry::new(target_lexicon::Triple::host());
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
    assert!(a2.is_inline_array() == false);
    assert_ne!(a2.base(), int_ty.base());

    // int*[5] (Registry - because int* doesn't have an index)
    let p1 = reg.pointer_to(QualType::unqualified(int_ty)); // int*
    let ap1 = reg.array_of(p1, ArraySizeType::Constant(5));
    assert_eq!(ap1.class(), TypeClass::Array);
    assert_eq!(ap1.array_len(), None); // Registry array
    assert!(ap1.is_inline_array() == false);

    // int[10]* (Registry Pointer)
    // int[10] is Inline Array (Base=Int, Arr=10). Not Simple.
    // So pointer_to(int[10]) must be Registry Pointer.
    let pa1 = reg.pointer_to(QualType::unqualified(a1));
    assert_eq!(pa1.class(), TypeClass::Pointer);
    assert_eq!(pa1.pointer_depth(), 0); // Registry pointer
    assert!(pa1.is_inline_pointer() == false);
}

#[test]
fn test_reconstruct_type() {
    let mut reg = TypeRegistry::new(target_lexicon::Triple::host());
    let int_ty = reg.type_int;

    // Reconstruct int*
    let p1 = reg.pointer_to(QualType::unqualified(int_ty));
    let cow_p1 = reg.get(p1);
    if let crate::semantic::TypeKind::Pointer { pointee } = cow_p1.kind {
        assert_eq!(pointee.ty(), int_ty);
    } else {
        panic!("Expected Pointer kind");
    }

    // Reconstruct int**
    let p2 = reg.pointer_to(QualType::unqualified(p1));
    let cow_p2 = reg.get(p2);
    if let crate::semantic::TypeKind::Pointer { pointee } = cow_p2.kind {
        assert_eq!(pointee.ty(), p1);
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

#[test]
fn test_typeregistry_pointer_canonicalization() {
    let mut reg = TypeRegistry::new(target_lexicon::Triple::host());
    let int_ty = reg.type_int;

    // Test 1: Canonicalization of inline pointers
    let p1 = reg.pointer_to(QualType::unqualified(int_ty));
    let p2 = reg.pointer_to(QualType::unqualified(int_ty));
    assert_eq!(p1, p2, "int* should be canonicalized");

    let p3 = reg.pointer_to(QualType::unqualified(p1)); // int**
    let p4 = reg.pointer_to(QualType::unqualified(p1)); // int**
    assert_eq!(p3, p4, "int** should be canonicalized");

    // Test 2: Canonicalization of registry pointers with qualified pointees
    let const_int = QualType::new(int_ty, crate::semantic::types::TypeQualifiers::CONST);
    let p_const_int1 = reg.pointer_to(const_int);
    let p_const_int2 = reg.pointer_to(const_int);
    assert_eq!(p_const_int1, p_const_int2, "const int* should be canonicalized");

    let volatile_int = QualType::new(int_ty, crate::semantic::types::TypeQualifiers::VOLATILE);
    let p_volatile_int1 = reg.pointer_to(volatile_int);
    let p_volatile_int2 = reg.pointer_to(volatile_int);
    assert_eq!(
        p_volatile_int1, p_volatile_int2,
        "volatile int* should be canonicalized"
    );

    let const_volatile_int = QualType::new(
        int_ty,
        crate::semantic::types::TypeQualifiers::CONST | crate::semantic::types::TypeQualifiers::VOLATILE,
    );
    let p_const_volatile_int1 = reg.pointer_to(const_volatile_int);
    let p_const_volatile_int2 = reg.pointer_to(const_volatile_int);
    assert_eq!(
        p_const_volatile_int1, p_const_volatile_int2,
        "const volatile int* should be canonicalized"
    );

    // Test 3: Different qualified pointees should produce different pointers
    assert_ne!(
        p_const_int1, p_volatile_int1,
        "const int* should differ from volatile int*"
    );
    assert_ne!(
        p_const_int1, p_const_volatile_int1,
        "const int* should differ from const volatile int*"
    );
    assert_ne!(
        p_volatile_int1, p_const_volatile_int1,
        "volatile int* should differ from const volatile int*"
    );
}

#[test]
fn test_complex_type_canonicalization() {
    let mut reg = TypeRegistry::new(target_lexicon::Triple::host());
    let int_ty = reg.type_int;

    // Test: Create a complex type
    let c1 = reg.complex_type(int_ty);

    // Test: Create the same complex type again (should be canonicalized)
    let c2 = reg.complex_type(int_ty);
    assert_eq!(c1, c2, "_Complex int should be canonicalized");

    // Verify Display output
    let output = reg.display_type(c1);
    assert_eq!(output, "_Complex int");
}

#[test]
fn test_anonymous_struct_member_access() {
    run_pass(
        r#"
        struct outer {
            int a;
            struct {
                int b;
                int c;
            };
            int d;
        };

        int main() {
            struct outer s;
            s.a = 1;
            s.b = 2;
            s.c = 3;
            s.d = 4;
            return 0;
        }
    "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_anonymous_struct_name_conflict() {
    run_fail(
        r#"
        struct outer {
            int a;
            struct {
                int b;
                int c;
            };
            int b;
        };
    "#,
        CompilePhase::SemanticLowering,
    );
}

#[test]
fn test_anonymous_struct_initialization() {
    run_pass(
        r#"
        struct outer {
            int a;
            struct {
                int b;
                int c;
            };
            int d;
        };

        int main() {
            struct outer s = {1, 2, 3, 4};
            return 0;
        }
    "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_anonymous_union_name_conflict() {
    run_fail(
        r#"
        struct outer {
            int a;
            union {
                int b;
                float c;
            };
            int c;
        };
    "#,
        CompilePhase::SemanticLowering,
    );
}

#[test]
fn test_anonymous_union_member_access() {
    run_pass(
        r#"
        struct outer {
            int a;
            union {
                int b;
                float c;
            };
            int d;
        };

        int main() {
            struct outer s;
            s.a = 1;
            s.b = 2;
            s.c = 3.0f;
            s.d = 4;
            return 0;
        }
    "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_struct_copy_init() {
    let source = r#"
        struct Wrap {
            void *func;
        };
        int global;
        void inc_global (void) { global++; }
        struct Wrap global_wrap[] = {
            ((struct Wrap) {inc_global}),
            inc_global,
        };
        int main() { return 0; }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @r"
    type %t0 = i32
    type %t1 = void
    type %t2 = struct Wrap { func: %t3 }
    type %t3 = ptr<%t1>
    type %t4 = [2]%t2
    type %t5 = fn() -> %t1

    global @global: i32 = const zero
    global @.L.str0: %t2 = const struct_literal { 0: const inc_global }
    global @global_wrap: [2]%t2 = const array_literal [const struct_literal { 0: const inc_global }, const struct_literal { 0: const inc_global }]

    fn main() -> i32
    {

      bb2:
        return const 0
    }

    fn inc_global() -> void
    {

      bb1:
        @global = @global + const 1
        return
    }
    ");
}

#[test]
fn test_type_registry_display_builtins() {
    use crate::semantic::type_registry::TypeRegistry;
    use crate::semantic::types::BuiltinType;
    use target_lexicon::Triple;

    let reg = TypeRegistry::new(Triple::host());

    let cases = [
        (BuiltinType::Void, "void"),
        (BuiltinType::Bool, "_Bool"),
        (BuiltinType::Char, "char"),
        (BuiltinType::SChar, "signed char"),
        (BuiltinType::UChar, "unsigned char"),
        (BuiltinType::Short, "short"),
        (BuiltinType::UShort, "unsigned short"),
        (BuiltinType::Int, "int"),
        (BuiltinType::UInt, "unsigned int"),
        (BuiltinType::Long, "long"),
        (BuiltinType::ULong, "unsigned long"),
        (BuiltinType::LongLong, "long long"),
        (BuiltinType::ULongLong, "unsigned long long"),
        (BuiltinType::Float, "float"),
        (BuiltinType::Double, "double"),
        (BuiltinType::LongDouble, "long double"),
        (BuiltinType::Signed, "signed"),
        (BuiltinType::VaList, "__builtin_va_list"),
        (BuiltinType::Complex, "_Complex (marker)"),
    ];

    for (builtin, expected) in cases {
        let ty = reg.get_builtin_type(builtin);
        assert_eq!(reg.display_type(ty), expected, "Failed for {:?}", builtin);
    }
}
