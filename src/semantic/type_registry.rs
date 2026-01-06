//! Type Registry
//!
//! Arena + canonicalization layer for semantic types.
//! All TypeRef creation and mutation MUST go through this context.

use crate::source_manager::SourceSpan;
use crate::{ast::NameId, diagnostic::SemanticError, semantic::QualType};
use hashbrown::{HashMap, HashSet};

use super::types::{FieldLayout, LayoutKind};
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
    complex_cache: HashMap<TypeRef, TypeRef>,

    // --- Layout computation tracking ---
    layout_in_progress: HashSet<TypeRef>,

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

impl Default for TypeRegistry {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeRegistry {
    /// Create a new TypeRegistry with builtin types initialized.
    pub fn new() -> Self {
        TypeRegistry {
            types: Vec::new(),
            pointer_cache: HashMap::new(),
            array_cache: HashMap::new(),
            function_cache: HashMap::new(),
            complex_cache: HashMap::new(),
            layout_in_progress: HashSet::new(),

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
        if let Some(&complex) = self.complex_cache.get(&base_type) {
            return complex;
        }

        let complex = self.alloc(Type::new(TypeKind::Complex { base_type }));
        self.complex_cache.insert(base_type, complex);
        complex
    }

    // ============================================================
    // Record / enum handling (two-phase)
    // ============================================================

    /// create new record type. this is still inclompete, need to call complete_record()
    /// to mark it as complete
    pub fn declare_record(&mut self, tag: Option<NameId>, is_union: bool) -> TypeRef {
        self.alloc(Type::new(TypeKind::Record {
            tag,
            members: Vec::new(),
            is_complete: false,
            is_union,
        }))
    }

    /// marks record as complete
    /// - does NOT compute layout
    /// - layout is computed lazily via ensure_layout
    pub fn complete_record(&mut self, record: TypeRef, members: Vec<StructMember>) {
        let ty = self.get_mut(record);
        match &mut ty.kind {
            TypeKind::Record {
                is_complete,
                members: slot,
                ..
            } => {
                *slot = members;
                *is_complete = true;
            }
            _ => unreachable!("complete_record on non-record"),
        }
    }

    /// create new enum type. this is still inclompete, need to call complete_enum()
    /// to mark it as complete
    pub fn declare_enum(&mut self, tag: Option<NameId>, base_type: TypeRef) -> TypeRef {
        self.alloc(Type::new(TypeKind::Enum {
            tag,
            base_type,
            enumerators: Vec::new(),
            is_complete: false,
        }))
    }

    pub fn complete_enum(&mut self, enum_ty: TypeRef, enumerators: Vec<EnumConstant>) {
        let ty = self.get_mut(enum_ty);
        match &mut ty.kind {
            TypeKind::Enum {
                is_complete,
                enumerators: slot,
                ..
            } => {
                *slot = enumerators;
                *is_complete = true;
            }
            _ => unreachable!("complete_enum on non-enum"),
        }
    }

    pub fn get_layout(&self, ty: TypeRef) -> &TypeLayout {
        let idx = ty.index();
        match self.types[idx].layout.as_ref() {
            Some(x) => x,
            None => panic!("ICE: TypeRef {ty} layout not computed. make sure layout is computed in previous phase"),
        }
    }

    pub fn get_array_layout(&self, ty: TypeRef) -> (u16, u16, TypeRef, u64) {
        let layout = self.get_layout(ty);
        match layout.kind {
            LayoutKind::Array { element, len } => (layout.size, layout.alignment, element, len),
            _ => panic!("ICE: layout is not array"),
        }
    }

    pub fn get_record_layout(&self, ty: TypeRef) -> (u16, u16, &[FieldLayout], bool) {
        let layout = self.get_layout(ty);
        match &layout.kind {
            LayoutKind::Record { fields, is_union } => (layout.size, layout.alignment, fields.as_ref(), *is_union),
            _ => panic!("ICE: layout is not record"),
        }
    }

    pub fn ensure_layout(&mut self, ty: TypeRef) -> Result<&TypeLayout, SemanticError> {
        let idx = ty.index();
        if self.types[idx].layout.is_some() {
            return Ok(self.types[idx].layout.as_ref().unwrap());
        }

        let layout = self.compute_layout(ty)?;
        self.types[idx].layout = Some(layout);

        Ok(self.types[idx].layout.as_ref().unwrap())
    }

    fn compute_layout(&mut self, ty: TypeRef) -> Result<TypeLayout, SemanticError> {
        // ensure_layout invariants:
        // - fails if type is incomplete
        // - caches result in Type.layout
        // - idempotent
        // - semantic-only layout (not MIR)

        // Check for recursive type definition
        if self.layout_in_progress.contains(&ty) {
            return Err(SemanticError::RecursiveType { ty });
        }

        // Get the type without mutability first to avoid borrow issues
        let type_kind = self.get(ty).kind.clone();

        // Mark this type as being computed
        self.layout_in_progress.insert(ty);

        let layout = match type_kind {
            TypeKind::Void => TypeLayout {
                size: 0,
                alignment: 1,
                kind: LayoutKind::Scalar,
            },

            TypeKind::Bool => TypeLayout {
                size: 1,
                alignment: 1,
                kind: LayoutKind::Scalar,
            },

            TypeKind::Char { .. } => TypeLayout {
                size: 1,
                alignment: 1,
                kind: LayoutKind::Scalar,
            },

            TypeKind::Short { .. } => TypeLayout {
                size: 2,
                alignment: 2,
                kind: LayoutKind::Scalar,
            },

            TypeKind::Int { .. } => TypeLayout {
                size: 4,
                alignment: 4,
                kind: LayoutKind::Scalar,
            },

            TypeKind::Long { .. } => {
                let (size, alignment) = (8, 8); // LP64 model
                TypeLayout {
                    size,
                    alignment,
                    kind: LayoutKind::Scalar,
                }
            }

            TypeKind::Float => TypeLayout {
                size: 4,
                alignment: 4,
                kind: LayoutKind::Scalar,
            },

            TypeKind::Double { is_long_double } => {
                let (size, alignment) = if is_long_double { (16, 16) } else { (8, 8) };
                TypeLayout {
                    size,
                    alignment,
                    kind: LayoutKind::Scalar,
                }
            }

            TypeKind::Complex { base_type } => {
                let base_layout = self.ensure_layout(base_type)?;
                TypeLayout {
                    size: base_layout.size * 2,
                    alignment: base_layout.alignment,
                    kind: LayoutKind::Scalar,
                }
            }

            TypeKind::Pointer { .. } => TypeLayout {
                size: 8, // 64-bit pointers
                alignment: 8,
                kind: LayoutKind::Scalar,
            },

            TypeKind::Array { element_type, size } => match size {
                ArraySizeType::Constant(len) => {
                    let element_layout = self.ensure_layout(element_type)?;
                    let total_size = element_layout.size as u64 * len as u64;
                    TypeLayout {
                        size: total_size as u16,
                        alignment: element_layout.alignment,
                        kind: LayoutKind::Array {
                            element: element_type,
                            len: len as u64,
                        },
                    }
                }
                ArraySizeType::Incomplete => {
                    return Err(SemanticError::UnsupportedFeature {
                        feature: "incomplete array type layout".to_string(),
                        span: SourceSpan::dummy(),
                    });
                }
                ArraySizeType::Variable(_) | ArraySizeType::Star => {
                    return Err(SemanticError::UnsupportedFeature {
                        feature: "variable length array type layout".to_string(),
                        span: SourceSpan::dummy(),
                    });
                }
            },

            TypeKind::Function { .. } => TypeLayout {
                size: 0,
                alignment: 1,
                kind: LayoutKind::Scalar,
            },

            TypeKind::Record {
                members,
                is_complete,
                is_union,
                ..
            } => {
                if !is_complete {
                    return Err(SemanticError::UnsupportedFeature {
                        feature: "incomplete record type layout".to_string(),
                        span: SourceSpan::dummy(),
                    });
                }

                self.compute_record_layout(&members, is_union)?
            }

            TypeKind::Enum {
                base_type, is_complete, ..
            } => {
                if !is_complete {
                    return Err(SemanticError::UnsupportedFeature {
                        feature: "incomplete enum type layout".to_string(),
                        span: SourceSpan::dummy(),
                    });
                }

                // Enum layout is the same as its base type
                self.ensure_layout(base_type)?.clone()
            }

            TypeKind::Error => {
                return Err(SemanticError::UnsupportedFeature {
                    feature: "layout computation for error type".to_string(),
                    span: SourceSpan::dummy(),
                });
            }
        };

        // Remove from in-progress set
        self.layout_in_progress.remove(&ty);

        Ok(layout)
    }

    fn compute_record_layout(&mut self, members: &[StructMember], is_union: bool) -> Result<TypeLayout, SemanticError> {
        let mut max_size = 0;
        let mut max_align = 1;
        let mut field_layouts = Vec::new();
        let mut offset = 0;

        if is_union {
            // Union layout: size = max field size, alignment = max field alignment
            for member in members {
                let member_layout = self.ensure_layout(member.member_type.ty)?;
                max_size = max_size.max(member_layout.size);
                max_align = max_align.max(member_layout.alignment);

                field_layouts.push(FieldLayout {
                    offset, // All union fields start at offset 0
                });
            }
        } else {
            // Struct layout: sequential field placement with padding
            for member in members {
                let member_layout = self.ensure_layout(member.member_type.ty)?;
                max_align = max_align.max(member_layout.alignment);

                // Add padding to align the field
                let padding = (member_layout.alignment - (offset % member_layout.alignment)) % member_layout.alignment;
                offset += padding;

                field_layouts.push(FieldLayout { offset });

                offset += member_layout.size;
            }

            // Add padding at the end to satisfy struct alignment
            max_size = (offset + max_align - 1) & !(max_align - 1);
        }

        Ok(TypeLayout {
            size: max_size,
            alignment: max_align,
            kind: LayoutKind::Record {
                fields: field_layouts,
                is_union,
            },
        })
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

    pub fn is_compatible(&self, a: QualType, b: QualType) -> bool {
        // C11 6.7.6.1p2: For two type names to be compatible, ...
        // This is a simplified check. A full implementation would handle
        // qualifiers, array sizes, function parameter compatibility, etc.
        a == b
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
