//! Type Registry
//!
//! Arena + canonicalization layer for semantic types.
//! All TypeRef creation and mutation MUST go through this context.

use crate::{ast::NameId, semantic::QualType};
use hashbrown::HashMap;

use super::{
    ArraySizeType, EnumConstant, FunctionParameter, StructMember, Type, TypeKind, TypeLayout, TypeQualifiers, TypeRef,
};

/// Central arena & factory for semantic types.
///
/// Invariants:
/// - All TypeRef come from this context
/// - Types are never removed
/// - Canonical types are reused when possible
pub struct TypeRegistry {
    pub types: Vec<Type>,

    // --- Canonicalization caches ---
    pointer_cache: HashMap<TypeRef, TypeRef>,
    array_cache: HashMap<(TypeRef, ArraySizeType), TypeRef>,
    function_cache: HashMap<FnSigKey, TypeRef>,

    // --- Common builtin types ---
    pub type_void: TypeRef,
    pub type_bool: TypeRef,
    pub type_short: TypeRef,
    pub type_short_unsigned: TypeRef,
    pub type_int: TypeRef,
    pub type_int_unsigned: TypeRef,
    pub type_long: TypeRef,
    pub type_long_unsigned: TypeRef,
    pub type_long_long: TypeRef,
    pub type_long_long_unsigned: TypeRef,
    pub type_char: TypeRef,
    pub type_char_unsigned: TypeRef,
    pub type_float: TypeRef,
    pub type_double: TypeRef,
    pub type_long_double: TypeRef,
    pub type_error: TypeRef,
}

impl TypeRegistry {
    /// Create a new TypeRegistry with builtin types initialized.
    pub fn new() -> Self {
        TypeRegistry {
            types: Vec::new(),
            pointer_cache: HashMap::new(),
            array_cache: HashMap::new(),
            function_cache: HashMap::new(),

            // temporary placeholders, overwritten below
            type_void: dummy(),
            type_bool: dummy(),
            type_int: dummy(),
            type_int_unsigned: dummy(),
            type_short: dummy(),
            type_long: dummy(),
            type_long_long: dummy(),
            type_char: dummy(),
            type_short_unsigned: dummy(),
            type_char_unsigned: dummy(),
            type_long_unsigned: dummy(),
            type_long_long_unsigned: dummy(),
            type_float: dummy(),
            type_double: dummy(),
            type_long_double: dummy(),
            type_error: dummy(),
        }
    }

    pub fn create_builtin(&mut self) {
        self.type_void = self.alloc(Type::new(TypeKind::Void));
        self.type_bool = self.alloc(Type::new(TypeKind::Bool));
        self.type_int = self.alloc(Type::new(TypeKind::Int { is_signed: true }));
        self.type_int_unsigned = self.alloc(Type::new(TypeKind::Int { is_signed: false }));
        self.type_short = self.alloc(Type::new(TypeKind::Short { is_signed: true }));
        self.type_short_unsigned = self.alloc(Type::new(TypeKind::Short { is_signed: false }));
        self.type_long = self.alloc(Type::new(TypeKind::Long {
            is_signed: true,
            is_long_long: false,
        }));
        self.type_long_unsigned = self.alloc(Type::new(TypeKind::Long {
            is_signed: false,
            is_long_long: false,
        }));
        self.type_long_long = self.alloc(Type::new(TypeKind::Long {
            is_signed: true,
            is_long_long: true,
        }));
        self.type_long_long_unsigned = self.alloc(Type::new(TypeKind::Long {
            is_signed: false,
            is_long_long: true,
        }));
        self.type_char = self.alloc(Type::new(TypeKind::Char { is_signed: true }));
        self.type_char_unsigned = self.alloc(Type::new(TypeKind::Char { is_signed: false }));
        self.type_float = self.alloc(Type::new(TypeKind::Float));
        self.type_double = self.alloc(Type::new(TypeKind::Double { is_long_double: false }));
        self.type_long_double = self.alloc(Type::new(TypeKind::Double { is_long_double: true }));
        self.type_error = self.alloc(Type::new(TypeKind::Error));
    }

    /// Allocate a new canonical type and return its TypeRef.
    fn alloc(&mut self, ty: Type) -> TypeRef {
        let idx = self.types.len() as u32 + 1;
        self.types.push(ty);
        TypeRef::new(idx).unwrap()
    }

    /// Immutable access to a type.
    #[inline]
    pub fn get(&self, r: TypeRef) -> &Type {
        &self.types[r.index()]
    }

    /// Mutable access to a type (ONLY for completion).
    #[inline]
    pub fn get_mut(&mut self, r: TypeRef) -> &mut Type {
        &mut self.types[r.index()]
    }

    // ============================================================
    // Canonical type constructors
    // ============================================================
    pub fn pointer_to(&mut self, base: TypeRef) -> TypeRef {
        if let Some(&ptr) = self.pointer_cache.get(&base) {
            return ptr;
        }

        let ptr = self.alloc(Type::new(TypeKind::Pointer { pointee: base }));
        self.pointer_cache.insert(base, ptr);
        ptr
    }

    pub fn array_of(&mut self, elem: TypeRef, size: ArraySizeType) -> TypeRef {
        let key = (elem, size.clone());
        if let Some(&arr) = self.array_cache.get(&key) {
            return arr;
        }

        let arr = self.alloc(Type::new(TypeKind::Array {
            element_type: elem,
            size,
        }));
        self.array_cache.insert(key, arr);
        arr
    }

    pub fn function_type(
        &mut self,
        return_type: TypeRef,
        params: Vec<FunctionParameter>,
        is_variadic: bool,
    ) -> TypeRef {
        let key = FnSigKey {
            return_type,
            params: params.iter().map(|p| p.param_type.ty).collect(), // canonical type only
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

    pub fn complex_type(&mut self, base_type: TypeRef) -> TypeRef {
        // TODO: cache it
        self.alloc(Type::new(TypeKind::Complex { base_type }))
    }

    // ============================================================
    // Record / enum handling (two-phase)
    // ============================================================
    pub fn new_record(&mut self, tag: Option<NameId>, is_union: bool) -> TypeRef {
        self.alloc(Type::new(TypeKind::Record {
            tag,
            members: Vec::new(),
            is_complete: false,
            is_union,
        }))
    }

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

    pub fn new_enum(&mut self, tag: Option<NameId>, base_type: TypeRef) -> TypeRef {
        self.alloc(Type::new(TypeKind::Enum {
            tag,
            base_type,
            enumerators: Vec::new(),
            is_complete: false,
        }))
    }

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

    pub fn decay(&mut self, qt: QualType) -> QualType {
        match &self.get(qt.ty).kind {
            TypeKind::Array { element_type, .. } => {
                let ptr = self.pointer_to(*element_type);
                QualType::new(ptr, qt.qualifiers)
            }
            TypeKind::Function { .. } => {
                let ptr = self.pointer_to(qt.ty); // TypeRef canonical
                QualType::new(ptr, qt.qualifiers)
            }
            _ => qt,
        }
    }

    pub fn strip_all(&self, qt: QualType) -> QualType {
        QualType::unqualified(qt.ty)
    }

    pub fn merge_qualifiers(&self, base: QualType, add: TypeQualifiers) -> QualType {
        QualType {
            ty: base.ty,
            qualifiers: base.qualifiers | add,
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
    TypeRef::new(1).unwrap()
}
