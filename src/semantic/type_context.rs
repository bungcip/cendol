//! TypeContext
//!
//! Arena + canonicalization layer for semantic types.
//! All TypeRef creation and mutation MUST go through this context.

use hashbrown::HashMap;
use serde::Serialize;
use std::num::NonZeroU32;

use crate::ast::{ArraySizeType, EnumConstant, FunctionParameter, NameId, StructMember, Type, TypeKind, TypeLayout};

/// Opaque reference to a canonical type.
/// Internally index + 1 (NonZeroU32 for niche optimization).
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Serialize)]
pub struct TypeRef(NonZeroU32);

impl TypeRef {
    #[inline]
    pub fn new(n: u32) -> Option<Self> {
        NonZeroU32::new(n).map(TypeRef)
    }

    #[inline]
    pub fn index(self) -> usize {
        (self.0.get() - 1) as usize
    }

    #[inline]
    pub fn get(self) -> u32 {
        self.0.get()
    }
}

/// Central arena & factory for semantic types.
///
/// Invariants:
/// - All TypeRef come from this context
/// - Types are never removed
/// - Canonical types are reused when possible
pub struct TypeContext {
    pub types: Vec<Type>,

    // --- Canonicalization caches ---
    pointer_cache: HashMap<TypeRef, TypeRef>,
    #[allow(unused)]
    array_cache: HashMap<(TypeRef, ArraySizeType), TypeRef>,
    function_cache: HashMap<FnSigKey, TypeRef>,

    // --- Common builtin types ---
    pub type_void: TypeRef,
    pub type_bool: TypeRef,
    pub type_int: TypeRef,
    pub type_char: TypeRef,
    pub type_double: TypeRef,
    pub type_error: TypeRef,
}

impl TypeContext {
    /// Create a new TypeContext with builtin types initialized.
    pub fn new() -> Self {
        TypeContext {
            types: Vec::new(),
            pointer_cache: HashMap::new(),
            array_cache: HashMap::new(),
            function_cache: HashMap::new(),

            // temporary placeholders, overwritten below
            type_void: dummy(),
            type_bool: dummy(),
            type_int: dummy(),
            type_char: dummy(),
            type_double: dummy(),
            type_error: dummy(),
        }
    }

    pub fn create_builtin(&mut self) {
        self.type_void = self.alloc(Type::new(TypeKind::Void));
        self.type_bool = self.alloc(Type::new(TypeKind::Bool));
        self.type_int = self.alloc(Type::new(TypeKind::Int { is_signed: true }));
        self.type_char = self.alloc(Type::new(TypeKind::Char { is_signed: true }));
        self.type_double = self.alloc(Type::new(TypeKind::Double { is_long_double: false }));
        self.type_error = self.alloc(Type::new(TypeKind::Error));
    }

    /// DEPRECATED: Add a type to the AST and return its reference
    pub(crate) fn push_type(&mut self, ty: Type) -> TypeRef {
        let index = self.types.len() as u32 + 1;
        self.types.push(ty);
        TypeRef::new(index).expect("TypeRef overflow")
    }

    /// DEPRECATED: Get a type by its reference
    pub fn get_type(&self, index: TypeRef) -> &Type {
        let idx = (index.get() - 1) as usize;
        if idx >= self.types.len() {
            panic!(
                "Type index {} out of bounds: types vector has {} elements",
                index.get(),
                self.types.len()
            );
        }
        &self.types[idx]
    }

    /// Allocate a new canonical type and return its TypeRef.
    fn alloc(&mut self, ty: Type) -> TypeRef {
        let idx = self.types.len() as u32 + 1;
        let nz = NonZeroU32::new(idx).unwrap();
        self.types.push(ty);
        TypeRef(nz)
    }

    /// Immutable access to a type.
    #[inline]
    #[allow(unused)]
    pub fn get(&self, r: TypeRef) -> &Type {
        &self.types[r.index()]
    }

    /// Mutable access to a type (ONLY for completion).
    #[inline]
    #[allow(unused)]
    pub fn get_mut(&mut self, r: TypeRef) -> &mut Type {
        &mut self.types[r.index()]
    }

    // ============================================================
    // Canonical type constructors
    // ============================================================
    #[allow(unused)]
    pub fn pointer_to(&mut self, base: TypeRef) -> TypeRef {
        if let Some(&ptr) = self.pointer_cache.get(&base) {
            return ptr;
        }

        let ptr = self.alloc(Type::new(TypeKind::Pointer { pointee: base }));
        self.pointer_cache.insert(base, ptr);
        ptr
    }

    // pub fn array_of(&mut self, elem: TypeRef, size: ArraySizeType) -> TypeRef {
    //     let key = (elem, size.clone());
    //     if let Some(&arr) = self.array_cache.get(&key) {
    //         return arr;
    //     }

    //     let arr = self.alloc(Type::new(TypeKind::Array {
    //         element_type: elem,
    //         size,
    //     }));
    //     self.array_cache.insert(key, arr);
    //     arr
    // }

    #[allow(unused)]
    pub fn function_type(
        &mut self,
        return_type: TypeRef,
        params: Vec<FunctionParameter>,
        is_variadic: bool,
    ) -> TypeRef {
        let key = FnSigKey {
            return_type,
            params: params.iter().map(|p| p.param_type).collect(),
            is_variadic,
        };

        if let Some(&f) = self.function_cache.get(&key) {
            return f;
        }

        let f = self.alloc(Type::new(TypeKind::Function {
            return_type,
            parameters: params,
            is_variadic,
        }));

        self.function_cache.insert(key, f);
        f
    }

    // ============================================================
    // Record / enum handling (two-phase)
    // ============================================================
    #[allow(unused)]
    pub fn new_record(&mut self, tag: Option<NameId>, is_union: bool) -> TypeRef {
        self.alloc(Type::new(TypeKind::Record {
            tag,
            members: Vec::new(),
            is_complete: false,
            is_union,
        }))
    }

    #[allow(unused)]
    pub fn complete_record(&mut self, record: TypeRef, members: Vec<StructMember>, layout: Option<TypeLayout>) {
        let ty = self.get_mut(record);
        match &mut ty.kind {
            TypeKind::Record {
                is_complete,
                members: slot,
                ..
            } => {
                *slot = members;
                *is_complete = true;
                ty.layout = layout;
            }
            _ => unreachable!("complete_record on non-record"),
        }
    }

    #[allow(unused)]
    pub fn new_enum(&mut self, tag: Option<NameId>, base_type: TypeRef) -> TypeRef {
        self.alloc(Type::new(TypeKind::Enum {
            tag,
            base_type,
            enumerators: Vec::new(),
            is_complete: false,
        }))
    }

    #[allow(unused)]
    pub fn complete_enum(&mut self, enum_ty: TypeRef, enumerators: Vec<EnumConstant>, layout: Option<TypeLayout>) {
        let ty = self.get_mut(enum_ty);
        match &mut ty.kind {
            TypeKind::Enum {
                is_complete,
                enumerators: slot,
                ..
            } => {
                *slot = enumerators;
                *is_complete = true;
                ty.layout = layout;
            }
            _ => unreachable!("complete_enum on non-enum"),
        }
    }
}

// ================================================================
// Helper types
// ================================================================

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct FnSigKey {
    return_type: TypeRef,
    params: Vec<TypeRef>,
    is_variadic: bool,
}

fn dummy() -> TypeRef {
    // Temporary placeholder before real initialization
    TypeRef(NonZeroU32::new(1).unwrap())
}
