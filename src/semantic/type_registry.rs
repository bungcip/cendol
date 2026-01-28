//! Type Registry
//!
//! Arena + canonicalization layer for semantic types.
//! All TypeRef creation and mutation MUST go through this context.

use std::borrow::Cow;

use crate::source_manager::SourceSpan;
use crate::{ast::NameId, diagnostic::SemanticError, semantic::QualType};
use hashbrown::{HashMap, HashSet};
use target_lexicon::{Architecture, PointerWidth, Triple};

use super::types::TypeClass;
use super::types::{FieldLayout, LayoutKind};
use super::{
    ArraySizeType, BuiltinType, EnumConstant, FunctionParameter, StructMember, Type, TypeKind, TypeLayout,
    TypeQualifiers, TypeRef,
};

/// Central arena & factory for semantic types.
///
/// Invariants:
/// - All TypeRef come from this context
/// - Types are never removed
/// - Canonical types are reused when possible
pub struct TypeRegistry {
    pub target_triple: Triple,

    // Index 0 is dummy.
    // Index 1..16 are builtins.
    // Index 17+ are allocated types.
    pub types: Vec<Type>,

    // --- Canonicalization caches ---
    pointer_cache: HashMap<QualType, TypeRef>,
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
    pub type_schar: TypeRef,
    pub type_char_unsigned: TypeRef,
    pub type_float: TypeRef,
    pub type_double: TypeRef,
    pub type_long_double: TypeRef,
    pub type_void_ptr: TypeRef,
    pub type_signed: TypeRef,
    pub type_valist: TypeRef,
    pub type_error: TypeRef,
}

impl Default for TypeRegistry {
    fn default() -> Self {
        Self::new(Triple::host())
    }
}

impl TypeRegistry {
    /// Create a new TypeRegistry with builtin types initialized.
    pub(crate) fn new(target_triple: Triple) -> Self {
        let mut reg = TypeRegistry {
            target_triple,
            types: Vec::new(),
            pointer_cache: HashMap::new(),
            array_cache: HashMap::new(),
            function_cache: HashMap::new(),
            complex_cache: HashMap::new(),
            layout_in_progress: HashSet::new(),

            // temporary placeholders - will be overwritten by create_builtin
            type_void: TypeRef::dummy(),
            type_bool: TypeRef::dummy(),
            type_int: TypeRef::dummy(),
            type_int_unsigned: TypeRef::dummy(),
            type_short: TypeRef::dummy(),
            type_long: TypeRef::dummy(),
            type_long_long: TypeRef::dummy(),
            type_char: TypeRef::dummy(),
            type_schar: TypeRef::dummy(),
            type_short_unsigned: TypeRef::dummy(),
            type_char_unsigned: TypeRef::dummy(),
            type_long_unsigned: TypeRef::dummy(),
            type_long_long_unsigned: TypeRef::dummy(),
            type_float: TypeRef::dummy(),
            type_double: TypeRef::dummy(),
            type_long_double: TypeRef::dummy(),
            type_void_ptr: TypeRef::dummy(),
            type_signed: TypeRef::dummy(),
            type_valist: TypeRef::dummy(),
            type_error: TypeRef::dummy(),
        };

        // Initialize dummy at index 0
        reg.types.push(Type::new(TypeKind::Error));

        reg.create_builtin();
        reg
    }

    fn create_builtin(&mut self) {
        // Reset types to just dummy to ensure order
        self.types.truncate(1);

        // Must match BuiltinType enum values 1..16 sequentially

        // 1: Void
        self.type_void = self.alloc_builtin(TypeKind::Builtin(BuiltinType::Void));

        // 2: Bool
        self.type_bool = self.alloc_builtin(TypeKind::Builtin(BuiltinType::Bool));

        // 3: Char (signed)
        self.type_char = self.alloc_builtin(TypeKind::Builtin(BuiltinType::Char));

        // 4: SChar (explicit signed char)
        self.type_schar = self.alloc_builtin(TypeKind::Builtin(BuiltinType::SChar));

        // 5: UChar
        self.type_char_unsigned = self.alloc_builtin(TypeKind::Builtin(BuiltinType::UChar));

        // 6: Short
        self.type_short = self.alloc_builtin(TypeKind::Builtin(BuiltinType::Short));

        // 7: UShort
        self.type_short_unsigned = self.alloc_builtin(TypeKind::Builtin(BuiltinType::UShort));

        // 8: Int
        self.type_int = self.alloc_builtin(TypeKind::Builtin(BuiltinType::Int));

        // 9: UInt
        self.type_int_unsigned = self.alloc_builtin(TypeKind::Builtin(BuiltinType::UInt));

        // 10: Long
        self.type_long = self.alloc_builtin(TypeKind::Builtin(BuiltinType::Long));

        // 11: ULong
        self.type_long_unsigned = self.alloc_builtin(TypeKind::Builtin(BuiltinType::ULong));

        // 12: LongLong
        self.type_long_long = self.alloc_builtin(TypeKind::Builtin(BuiltinType::LongLong));

        // 13: ULongLong
        self.type_long_long_unsigned = self.alloc_builtin(TypeKind::Builtin(BuiltinType::ULongLong));

        // 14: Float
        self.type_float = self.alloc_builtin(TypeKind::Builtin(BuiltinType::Float));

        // 15: Double
        self.type_double = self.alloc_builtin(TypeKind::Builtin(BuiltinType::Double));

        // 16: LongDouble
        self.type_long_double = self.alloc_builtin(TypeKind::Builtin(BuiltinType::LongDouble));

        // 17: Signed (marker)
        self.type_signed = self.alloc_builtin(TypeKind::Builtin(BuiltinType::Signed));

        // 18: VaList
        self.type_valist = self.alloc_builtin(TypeKind::Builtin(BuiltinType::VaList));

        // Pre-calculate void*
        self.type_void_ptr = self.pointer_to(QualType::unqualified(self.type_void));

        // We can assert that the last allocated index was 18
        debug_assert_eq!(self.types.len() - 1, 18, "Builtin types allocation mismatch");
    }

    fn alloc_builtin(&mut self, kind: TypeKind) -> TypeRef {
        let ty = Type::new(kind);
        self.alloc(ty)
    }

    /// Allocate a new canonical type and return its TypeRef.
    fn alloc(&mut self, ty: Type) -> TypeRef {
        let idx = self.types.len() as u32;
        self.types.push(ty);
        let kind_ref = &self.types[idx as usize].kind;
        let class = kind_ref.to_class();

        TypeRef::new(idx, class, 0, 0).expect("TypeRef alloc failed")
    }

    /// Resolve a TypeRef to a Type.
    /// Returns Cow because inline types are constructed on the fly.
    #[inline]
    pub(crate) fn get(&self, r: TypeRef) -> Cow<'_, Type> {
        if r.is_inline_pointer() {
            // Reconstruct Pointer Type
            // We need to know the TypeRef of the pointee.
            let pointee = self.reconstruct_pointee(r);

            // Pointer layout is always fixed
            let layout = TypeLayout {
                size: 8,
                alignment: 8,
                kind: LayoutKind::Scalar,
            };

            Cow::Owned(Type {
                kind: TypeKind::Pointer {
                    pointee: QualType::unqualified(pointee),
                },
                layout: Some(layout),
            })
        } else if r.is_inline_array() {
            // Reconstruct Array Type
            let element = self.reconstruct_element(r);
            let len = r.array_len().unwrap() as u64;

            Cow::Owned(Type {
                kind: TypeKind::Array {
                    element_type: element,
                    size: ArraySizeType::Constant(len as usize),
                },
                layout: None,
            })
        } else {
            // Registry type
            Cow::Borrowed(&self.types[r.index()])
        }
    }

    /// Helper to get the pointee type if the given type is a pointer.
    pub(crate) fn get_pointee(&self, ty: TypeRef) -> Option<QualType> {
        if ty.is_inline_pointer() {
            Some(QualType::unqualified(self.reconstruct_pointee(ty)))
        } else {
            match &self.get(ty).kind {
                TypeKind::Pointer { pointee } => Some(*pointee),
                _ => None,
            }
        }
    }

    // Legacy support: mutable access only for completing records/enums
    #[inline]
    fn get_mut(&mut self, r: TypeRef) -> &mut Type {
        // Cannot mutate inline types
        if r.is_inline_pointer() || r.is_inline_array() {
            panic!("Cannot get_mut on inline type {:?}", r);
        }
        &mut self.types[r.index()]
    }

    fn reconstruct_pointee(&self, r: TypeRef) -> TypeRef {
        debug_assert!(r.is_inline_pointer());
        let depth = r.pointer_depth();
        if depth > 1 {
            // Decrement depth
            TypeRef::new(r.base(), r.class(), depth - 1, 0).unwrap()
        } else {
            // Depth becomes 0. Class becomes Class of Base.
            // Look up base in registry.
            let base_idx = r.base();
            let base_type = &self.types[base_idx as usize];
            let base_class = base_type.kind.to_class();
            TypeRef::new(base_idx, base_class, 0, 0).unwrap()
        }
    }

    fn reconstruct_element(&self, r: TypeRef) -> TypeRef {
        debug_assert!(r.is_inline_array());
        // Array becomes non-array (arr=0). Class becomes Class of Base.
        let base_idx = r.base();
        let base_type = &self.types[base_idx as usize];
        let base_class = base_type.kind.to_class();
        TypeRef::new(base_idx, base_class, 0, 0).unwrap()
    }

    // ============================================================
    // Canonical type constructors
    // ============================================================
    pub(crate) fn pointer_to(&mut self, base: QualType) -> TypeRef {
        // Try inline if unqualified
        if base.qualifiers().is_empty() {
            let base_ty = base.ty();
            // 1. If base is Inline Pointer (depth 1..2), we can increment depth (max 3).
            if base_ty.is_inline_pointer() {
                let depth = base_ty.pointer_depth();
                if depth < 3 {
                    return TypeRef::new(base_ty.base(), TypeClass::Pointer, depth + 1, 0).unwrap();
                }
            }

            // 2. If base is Simple (Ptr=0, Arr=0), we can make Inline Pointer depth 1.
            if base_ty.pointer_depth() == 0 && base_ty.array_len().is_none() {
                return TypeRef::new(base_ty.base(), TypeClass::Pointer, 1, 0).unwrap();
            }
        }

        // Fallback to Registry
        if let Some(&ptr) = self.pointer_cache.get(&base) {
            return ptr;
        }

        let ptr = self.alloc(Type::new(TypeKind::Pointer { pointee: base }));
        self.pointer_cache.insert(base, ptr);
        ptr
    }

    pub(crate) fn array_of(&mut self, elem: TypeRef, size: ArraySizeType) -> TypeRef {
        // Try inline
        if let ArraySizeType::Constant(len) = size
            && len <= 31
            && elem.pointer_depth() == 0
            && elem.array_len().is_none()
        {
            // Check if elem is Simple
            return TypeRef::new(elem.base(), TypeClass::Array, 0, len as u32).unwrap();
        }

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

    pub(crate) fn function_type(
        &mut self,
        return_type: TypeRef,
        params: Vec<FunctionParameter>,
        is_variadic: bool,
        is_noreturn: bool,
    ) -> TypeRef {
        let key = FnSigKey {
            return_type,
            params: params.iter().map(|p| p.param_type).collect(),
            is_variadic,
            is_noreturn,
        };

        if let Some(&f) = self.function_cache.get(&key) {
            return f;
        }

        let f = self.alloc(Type::new(TypeKind::Function {
            return_type,
            parameters: params,
            is_variadic,
            is_noreturn,
        }));

        self.function_cache.insert(key, f);
        f
    }

    pub(crate) fn complex_type(&mut self, base_type: TypeRef) -> TypeRef {
        if let Some(&complex) = self.complex_cache.get(&base_type) {
            return complex;
        }

        // Complex is usually stored in registry.
        let complex = self.alloc(Type::new(TypeKind::Complex { base_type }));
        self.complex_cache.insert(base_type, complex);
        complex
    }

    // ============================================================
    // Record / enum handling
    // ============================================================

    pub(crate) fn declare_record(&mut self, tag: Option<NameId>, is_union: bool) -> TypeRef {
        self.alloc(Type::new(TypeKind::Record {
            tag,
            members: Vec::new(),
            is_complete: false,
            is_union,
        }))
    }

    pub(crate) fn complete_record(&mut self, record: TypeRef, members: Vec<StructMember>) {
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

    pub(crate) fn declare_enum(&mut self, tag: Option<NameId>, base_type: TypeRef) -> TypeRef {
        self.alloc(Type::new(TypeKind::Enum {
            tag,
            base_type,
            enumerators: Vec::new(),
            is_complete: false,
        }))
    }

    pub(crate) fn complete_enum(&mut self, enum_ty: TypeRef, enumerators: Vec<EnumConstant>) {
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

    // ============================================================
    // Layout
    // ============================================================

    pub(crate) fn get_layout(&self, ty: TypeRef) -> Cow<'_, TypeLayout> {
        if ty.is_inline_pointer() {
            return Cow::Owned(TypeLayout {
                size: 8,
                alignment: 8,
                kind: LayoutKind::Scalar,
            });
        }

        if ty.is_inline_array() {
            let elem = self.reconstruct_element(ty);
            let elem_layout = self.get_layout(elem);
            let len = ty.array_len().unwrap() as u64;
            return Cow::Owned(TypeLayout {
                size: elem_layout.size * (len as u16), // Potential overflow if not careful, but C rules apply
                alignment: elem_layout.alignment,
                kind: LayoutKind::Array { element: elem, len },
            });
        }

        let idx = ty.index();
        match self.types[idx].layout.as_ref() {
            Some(x) => Cow::Borrowed(x),
            None => panic!("ICE: TypeRef {ty} layout not computed. make sure layout is computed in previous phase"),
        }
    }

    pub(crate) fn get_array_layout(&self, ty: TypeRef) -> (u16, u16, TypeRef, u64) {
        let layout = self.get_layout(ty);
        match layout.kind {
            LayoutKind::Array { element, len } => (layout.size, layout.alignment, element, len),
            _ => panic!("ICE: layout is not array"),
        }
    }

    pub(crate) fn get_record_layout(&self, ty: TypeRef) -> (u16, u16, Vec<FieldLayout>, bool) {
        let layout = self.get_layout(ty);
        match &layout.kind {
            LayoutKind::Record { fields, is_union } => (layout.size, layout.alignment, fields.clone(), *is_union),
            _ => panic!("ICE: layout is not record"),
        }
    }

    pub(crate) fn ensure_layout(&mut self, ty: TypeRef) -> Result<Cow<'_, TypeLayout>, SemanticError> {
        if ty.is_inline_pointer() {
            return Ok(Cow::Owned(TypeLayout {
                size: 8,
                alignment: 8,
                kind: LayoutKind::Scalar,
            }));
        }

        if ty.is_inline_array() {
            // Recursive check
            let elem = self.reconstruct_element(ty);
            let elem_layout = self.ensure_layout(elem)?; // returns Cow
            let len = ty.array_len().unwrap() as u64;
            let size = (elem_layout.size as u64 * len) as u16;

            return Ok(Cow::Owned(TypeLayout {
                size,
                alignment: elem_layout.alignment,
                kind: LayoutKind::Array { element: elem, len },
            }));
        }

        let idx = ty.index();
        if self.types[idx].layout.is_some() {
            return Ok(Cow::Borrowed(self.types[idx].layout.as_ref().unwrap()));
        }

        let layout = self.compute_layout(ty)?;
        self.types[idx].layout = Some(layout);

        Ok(Cow::Borrowed(self.types[idx].layout.as_ref().unwrap()))
    }

    fn compute_layout(&mut self, ty: TypeRef) -> Result<TypeLayout, SemanticError> {
        if self.layout_in_progress.contains(&ty) {
            return Err(SemanticError::RecursiveType { ty });
        }

        // We clone Kind to release borrow on self
        let type_kind = self.get(ty).kind.clone();

        self.layout_in_progress.insert(ty);

        let layout = match type_kind {
            TypeKind::Builtin(b) => match b {
                BuiltinType::Void => TypeLayout {
                    size: 0,
                    alignment: 1,
                    kind: LayoutKind::Scalar,
                },
                BuiltinType::Bool | BuiltinType::Char | BuiltinType::SChar | BuiltinType::UChar => TypeLayout {
                    size: 1,
                    alignment: 1,
                    kind: LayoutKind::Scalar,
                },
                BuiltinType::Short | BuiltinType::UShort => TypeLayout {
                    size: 2,
                    alignment: 2,
                    kind: LayoutKind::Scalar,
                },
                BuiltinType::Int | BuiltinType::UInt | BuiltinType::Float => TypeLayout {
                    size: 4,
                    alignment: 4,
                    kind: LayoutKind::Scalar,
                },
                BuiltinType::Long | BuiltinType::ULong => {
                    // long is usually pointer width
                    let size = match self.target_triple.pointer_width() {
                        Ok(PointerWidth::U16) => 2,
                        Ok(PointerWidth::U32) => 4,
                        Ok(PointerWidth::U64) => 8,
                        Err(_) => 8, // Default to 64-bit if unknown
                    };
                    TypeLayout {
                        size,
                        alignment: size,
                        kind: LayoutKind::Scalar,
                    }
                }
                BuiltinType::LongLong | BuiltinType::ULongLong | BuiltinType::Double => TypeLayout {
                    size: 8,
                    alignment: 8,
                    kind: LayoutKind::Scalar,
                },
                BuiltinType::LongDouble => {
                    let size = if self.target_triple.architecture == Architecture::X86_64 {
                        8
                    } else {
                        16
                    };
                    TypeLayout {
                        size,
                        alignment: size,
                        kind: LayoutKind::Scalar,
                    }
                }
                BuiltinType::Signed => TypeLayout {
                    size: 4,
                    alignment: 4,
                    kind: LayoutKind::Scalar,
                },
                BuiltinType::VaList => TypeLayout {
                    size: 24,
                    alignment: 8,
                    kind: LayoutKind::Record {
                        fields: vec![
                            FieldLayout { offset: 0 },
                            FieldLayout { offset: 4 },
                            FieldLayout { offset: 8 },
                            FieldLayout { offset: 16 },
                        ],
                        is_union: false,
                    },
                },
            },

            TypeKind::Pointer { .. } => {
                let size = match self.target_triple.pointer_width() {
                    Ok(PointerWidth::U16) => 2,
                    Ok(PointerWidth::U32) => 4,
                    Ok(PointerWidth::U64) => 8,
                    Err(_) => 8,
                };
                TypeLayout {
                    size,
                    alignment: size,
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
                _ => {
                    return Err(SemanticError::UnsupportedFeature {
                        feature: "incomplete/VLA array layout".to_string(),
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
                    // This is the correct error when sizeof is used on an incomplete type.
                    return Err(SemanticError::SizeOfIncompleteType {
                        ty,
                        // The span from the caller (e.g., the sizeof expression) is used,
                        // so a dummy span here is acceptable.
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
                self.ensure_layout(base_type)?.into_owned()
            }

            TypeKind::Error => {
                return Err(SemanticError::UnsupportedFeature {
                    feature: "error layout".to_string(),
                    span: SourceSpan::dummy(),
                });
            }
        };

        self.layout_in_progress.remove(&ty);
        Ok(layout)
    }

    fn compute_record_layout(&mut self, members: &[StructMember], is_union: bool) -> Result<TypeLayout, SemanticError> {
        let mut max_align = 1;
        let mut current_size = 0;
        let mut field_layouts = Vec::with_capacity(members.len());
        // For C11 6.7.2.1p18 flexible array check:
        // "the last element of a structure with more than one named member may have an incomplete array type"
        // But incomplete array types are NOT allowed in unions.
        // We will check validity as we iterate.
        // Note: The count of members might include anonymous struct/union members which are technically members.

        let member_count = members.len();

        for (i, member) in members.iter().enumerate() {
            let member_ty = member.member_type.ty();

            // Special handling for flexible array member (FAM)
            // Need to check if it is incomplete array
            // We can't use is_complete because that recurses. We check TypeKind directly.
            let is_incomplete_or_vla_array = if member_ty.is_inline_array() {
                false // inline array always has len
            } else {
                matches!(
                    self.get(member_ty).kind,
                    TypeKind::Array {
                        size: ArraySizeType::Incomplete | ArraySizeType::Variable(_),
                        ..
                    }
                )
            };

            if is_incomplete_or_vla_array {
                if is_union {
                    // Incomplete or VLA types not allowed in union
                    return Err(SemanticError::UnsupportedFeature {
                        feature: "incomplete/VLA array in union".to_string(),
                        span: member.span,
                    });
                }

                // Must be last member
                if i != member_count - 1 {
                    return Err(SemanticError::FlexibleArrayNotLast { span: member.span });
                }

                // Must have at least one other named member.
                // Or rather, "structure with more than one named member".
                // If this is the only member, it's invalid.
                if member_count < 2 {
                    return Err(SemanticError::FlexibleArrayInEmptyStruct { span: member.span });
                }

                // If valid FAM:
                // Size of structure is as if FAM was omitted.
                // But we must respect its alignment for the struct's alignment.
                // We need to get the element type to find alignment.
                let elem_ty = match &self.get(member_ty).kind {
                    TypeKind::Array { element_type, .. } => *element_type,
                    _ => unreachable!(),
                };
                let elem_layout = self.ensure_layout(elem_ty)?;

                max_align = max_align.max(elem_layout.alignment);

                // FAM has size 0 for layout purposes of the struct size,
                // but its offset is where it would start.
                // The standard says: "size of the structure is as if the flexible array member were omitted"
                // This means current_size stays as is (after padding for alignment of FAM? No, omitted means omitted).
                // "except that it may have more trailing padding than the omission would imply"
                // Usually this is interpreted as: sizeof(struct) = max(sizeof(struct_without_fam), offsetof(fam)).
                // Or simply: layout the FAM, but don't increment current_size by its size (which is unknown/0).
                // But we might need to add padding to current_size to reach FAM alignment?
                // "as if the flexible array member were omitted" implies we don't even add padding for it?
                // BUT "except that it may have more trailing padding".
                // Most compilers align the end of the struct to the alignment of the FAM.

                // Let's compute offset.
                let offset = (current_size + elem_layout.alignment - 1) & !(elem_layout.alignment - 1);
                field_layouts.push(FieldLayout { offset });

                // We do NOT update current_size with FAM size (which is effectively 0 or variable).
                // But we might update current_size to offset?
                // GCC: sizeof(struct { int x; int y[]; }) == 4.
                //      sizeof(struct { char c; int y[]; }) == 4 (aligned to 4).
                // So we do align current_size.
                current_size = offset;

                continue;
            }

            let layout = self.ensure_layout(member_ty)?;
            max_align = max_align.max(layout.alignment);

            if is_union {
                current_size = current_size.max(layout.size);
                field_layouts.push(FieldLayout { offset: 0 });
            } else {
                // Align current_size to member's alignment to find its offset
                let offset = (current_size + layout.alignment - 1) & !(layout.alignment - 1);
                field_layouts.push(FieldLayout { offset });
                current_size = offset + layout.size;
            }
        }

        // Final size is padded to the record's max alignment
        let final_size = (current_size + max_align - 1) & !(max_align - 1);

        Ok(TypeLayout {
            size: final_size,
            alignment: max_align,
            kind: LayoutKind::Record {
                fields: field_layouts,
                is_union,
            },
        })
    }

    pub(crate) fn decay(&mut self, qt: QualType, ptr_qualifiers: TypeQualifiers) -> QualType {
        let kind = self.get(qt.ty()).kind.clone();
        match kind {
            TypeKind::Array { element_type, .. } => {
                // Correct logic: Array of T decays to Pointer to T.
                // Qualifiers on Array apply to the element in the resulting pointer type.
                let elem_qt = QualType::new(element_type, qt.qualifiers());
                let ptr = self.pointer_to(elem_qt);
                // Apply the extracted pointer qualifiers (e.g. from static/const inside [])
                QualType::new(ptr, ptr_qualifiers)
            }
            TypeKind::Function { .. } => {
                let ptr = self.pointer_to(qt);
                QualType::new(ptr, ptr_qualifiers)
            }
            _ => qt,
        }
    }

    pub(crate) fn strip_all(&self, qt: QualType) -> QualType {
        QualType::unqualified(qt.ty())
    }

    pub(crate) fn merge_qualifiers(&self, base: QualType, add: TypeQualifiers) -> QualType {
        QualType::new(base.ty(), base.qualifiers() | add)
    }

    pub(crate) fn is_compatible(&self, a: QualType, b: QualType) -> bool {
        if a == b {
            return true;
        }

        if a.qualifiers() != b.qualifiers() {
            return false;
        }

        let ty_a_ref = a.ty();
        let ty_b_ref = b.ty();

        if ty_a_ref == ty_b_ref {
            return true;
        }

        let kind_a = self.get(ty_a_ref).kind.clone();
        let kind_b = self.get(ty_b_ref).kind.clone();

        match (kind_a, kind_b) {
            (
                TypeKind::Array {
                    element_type: elem_a,
                    size: size_a,
                },
                TypeKind::Array {
                    element_type: elem_b,
                    size: size_b,
                },
            ) => {
                if !self.is_compatible(QualType::unqualified(elem_a), QualType::unqualified(elem_b)) {
                    return false;
                }
                match (size_a, size_b) {
                    (ArraySizeType::Incomplete, _) => true,
                    (_, ArraySizeType::Incomplete) => true,
                    (ArraySizeType::Constant(sa), ArraySizeType::Constant(sb)) => sa == sb,
                    (ArraySizeType::Star, _) => true,
                    (_, ArraySizeType::Star) => true,
                    _ => false,
                }
            }
            (
                TypeKind::Function {
                    return_type: ret_a,
                    parameters: params_a,
                    is_variadic: var_a,
                    ..
                },
                TypeKind::Function {
                    return_type: ret_b,
                    parameters: params_b,
                    is_variadic: var_b,
                    ..
                },
            ) => {
                if var_a != var_b {
                    return false;
                }
                if !self.is_compatible(QualType::unqualified(ret_a), QualType::unqualified(ret_b)) {
                    return false;
                }
                if params_a.len() != params_b.len() {
                    return false;
                }
                for (p_a, p_b) in params_a.iter().zip(params_b.iter()) {
                    // Ignore top-level qualifiers on parameters
                    let type_a = QualType::unqualified(p_a.param_type.ty());
                    let type_b = QualType::unqualified(p_b.param_type.ty());
                    if !self.is_compatible(type_a, type_b) {
                        return false;
                    }
                }
                true
            }
            (TypeKind::Pointer { pointee: p_a }, TypeKind::Pointer { pointee: p_b }) => self.is_compatible(p_a, p_b),
            _ => false,
        }
    }

    pub(crate) fn is_complete(&self, ty: TypeRef) -> bool {
        if ty.is_inline_pointer() {
            return true;
        }
        if ty.is_inline_array() {
            // Array is complete if element is complete
            // But strict C says array valid if element type is complete (except local VLA which is complete at runtime allocation point?)
            // Here we just check element kind.
            let elem = self.reconstruct_element(ty);
            return self.is_complete(elem);
        }

        let kind = &self.types[ty.index()].kind;
        match kind {
            TypeKind::Record { is_complete, .. } => *is_complete,
            TypeKind::Enum { is_complete, .. } => *is_complete,
            TypeKind::Array { element_type, size } => {
                if let ArraySizeType::Incomplete = size {
                    return false;
                }
                self.is_complete(*element_type)
            }
            TypeKind::Builtin(BuiltinType::Void) => false,
            _ => true, // Scalars are always complete
        }
    }

    pub(crate) fn is_const_recursive(&self, qt: QualType) -> bool {
        if qt.is_const() {
            return true;
        }

        let ty_ref = qt.ty();
        if ty_ref.is_record()
            && let TypeKind::Record { members, .. } = &self.get(ty_ref).kind
        {
            for member in members {
                if self.is_const_recursive(member.member_type) {
                    return true;
                }
            }
        }
        false
    }

    pub(crate) fn display_qual_type(&self, qt: QualType) -> String {
        let quals = qt.qualifiers();
        let ty_str = self.display_type(qt.ty());
        if quals.is_empty() {
            ty_str
        } else {
            format!("{} {}", quals, ty_str)
        }
    }

    pub(crate) fn display_type(&self, ty: TypeRef) -> String {
        if ty.is_inline_pointer() {
            let pointee = self.reconstruct_pointee(ty);
            return format!("{}*", self.display_type(pointee));
        }

        if ty.is_inline_array() {
            let elem = self.reconstruct_element(ty);
            let len = ty.array_len().unwrap();
            return format!("{}[{}]", self.display_type(elem), len);
        }

        let type_kind = &self.types[ty.index()].kind;
        match type_kind {
            TypeKind::Builtin(b) => match b {
                BuiltinType::Void => "void".to_string(),
                BuiltinType::Bool => "_Bool".to_string(),
                BuiltinType::Char => "char".to_string(),
                BuiltinType::SChar => "signed char".to_string(),
                BuiltinType::UChar => "unsigned char".to_string(),
                BuiltinType::Short => "short".to_string(),
                BuiltinType::UShort => "unsigned short".to_string(),
                BuiltinType::Int => "int".to_string(),
                BuiltinType::UInt => "unsigned int".to_string(),
                BuiltinType::Long => "long".to_string(),
                BuiltinType::ULong => "unsigned long".to_string(),
                BuiltinType::LongLong => "long long".to_string(),
                BuiltinType::ULongLong => "unsigned long long".to_string(),
                BuiltinType::Float => "float".to_string(),
                BuiltinType::Double => "double".to_string(),
                BuiltinType::LongDouble => "long double".to_string(),
                BuiltinType::Signed => "signed".to_string(),
                BuiltinType::VaList => "__builtin_va_list".to_string(),
            },
            TypeKind::Complex { base_type } => format!("_Complex {}", self.display_type(*base_type)),
            TypeKind::Pointer { pointee } => format!("{}*", self.display_qual_type(*pointee)),
            TypeKind::Array { element_type, size } => {
                let elem_str = self.display_type(*element_type);
                match size {
                    ArraySizeType::Constant(len) => format!("{}[{}]", elem_str, len),
                    ArraySizeType::Variable(_) => format!("{}[*]", elem_str), // Using * for VLA for now or expr?
                    ArraySizeType::Incomplete => format!("{}[]", elem_str),
                    ArraySizeType::Star => format!("{}[*]", elem_str),
                }
            }
            TypeKind::Function {
                return_type,
                parameters,
                is_variadic,
                ..
            } => {
                let ret_str = self.display_type(*return_type);
                let params_str = parameters
                    .iter()
                    .map(|p| self.display_qual_type(p.param_type))
                    .collect::<Vec<_>>()
                    .join(", ");
                let var_str = if *is_variadic { ", ..." } else { "" };
                format!("{}({}{})", ret_str, params_str, var_str)
            }
            TypeKind::Record { tag, is_union, .. } => {
                let kind_str = if *is_union { "union" } else { "struct" };
                if let Some(tag_name) = tag {
                    format!("{} {}", kind_str, tag_name)
                } else {
                    format!("{} (anonymous)", kind_str)
                }
            }
            TypeKind::Enum { tag, .. } => {
                if let Some(tag_name) = tag {
                    format!("enum {}", tag_name)
                } else {
                    "enum (anonymous)".to_string()
                }
            }
            TypeKind::Error => "<error>".to_string(),
        }
    }
}

// ================================================================
// Helper types
// ================================================================

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct FnSigKey {
    return_type: TypeRef,
    params: Vec<QualType>,
    is_variadic: bool,
    is_noreturn: bool,
}
