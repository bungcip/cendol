//! Type Registry
//!
//! Arena + canonicalization layer for semantic types.
//! All TypeRef creation and mutation MUST go through this context.

use std::borrow::Cow;

use crate::source_manager::SourceSpan;
use crate::{ast::NameId, diagnostic::SemanticError, semantic::QualType};
use hashbrown::{HashMap, HashSet};
use target_lexicon::{PointerWidth, Triple};

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
    pub type_void_ptr: TypeRef,
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
            type_void: unsafe { TypeRef::from_raw_unchecked(1) },
            type_bool: unsafe { TypeRef::from_raw_unchecked(1) },
            type_int: unsafe { TypeRef::from_raw_unchecked(1) },
            type_int_unsigned: unsafe { TypeRef::from_raw_unchecked(1) },
            type_short: unsafe { TypeRef::from_raw_unchecked(1) },
            type_long: unsafe { TypeRef::from_raw_unchecked(1) },
            type_long_long: unsafe { TypeRef::from_raw_unchecked(1) },
            type_char: unsafe { TypeRef::from_raw_unchecked(1) },
            type_short_unsigned: unsafe { TypeRef::from_raw_unchecked(1) },
            type_char_unsigned: unsafe { TypeRef::from_raw_unchecked(1) },
            type_long_unsigned: unsafe { TypeRef::from_raw_unchecked(1) },
            type_long_long_unsigned: unsafe { TypeRef::from_raw_unchecked(1) },
            type_float: unsafe { TypeRef::from_raw_unchecked(1) },
            type_double: unsafe { TypeRef::from_raw_unchecked(1) },
            type_long_double: unsafe { TypeRef::from_raw_unchecked(1) },
            type_void_ptr: unsafe { TypeRef::from_raw_unchecked(1) },
            type_error: unsafe { TypeRef::from_raw_unchecked(1) },
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
        let _type_schar = self.alloc_builtin(TypeKind::Builtin(BuiltinType::SChar));

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

        // Pre-calculate void*
        self.type_void_ptr = self.pointer_to(self.type_void);

        // We can assert that the last allocated index was 16
        debug_assert_eq!(self.types.len() - 1, 16, "Builtin types allocation mismatch");
    }

    fn alloc_builtin(&mut self, kind: TypeKind) -> TypeRef {
        let ty = Type::new(kind);
        self.alloc_internal(ty)
    }

    /// Internal allocation without checks
    fn alloc_internal(&mut self, ty: Type) -> TypeRef {
        let idx = self.types.len() as u32;
        self.types.push(ty);
        // Builtins have pointer_depth=0, array_len=0.
        // Class is Builtin (0).
        // But wait, alloc_internal is also used for Record/Enum?
        // No, this is just helper.

        // We need to determine TypeClass from kind to construct TypeRef correctly.
        let kind_ref = &self.types[idx as usize].kind;
        let class = kind_ref.to_class();

        TypeRef::new(idx, class, 0, 0).expect("TypeRef alloc failed")
    }

    /// Allocate a new canonical type and return its TypeRef.
    fn alloc(&mut self, ty: Type) -> TypeRef {
        self.alloc_internal(ty)
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
                kind: TypeKind::Pointer { pointee },
                layout: Some(layout),
            })
        } else if r.is_inline_array() {
            // Reconstruct Array Type
            let element = self.reconstruct_element(r);
            let len = r.array_len().unwrap() as u64;

            // We need layout of element to compute array layout?
            // Since we return Cow<Type> which includes layout if possible.
            // But we can't easily compute element layout here without recursion/mutability if it's missing.
            // However, inline arrays usually have simple elements which might have layout.
            // But 'get' shouldn't side-effect (compute layout).
            // So we return None for layout, or look it up if available.

            // For now, let's leave layout None for constructed types in 'get',
            // relying on ensure_layout to compute it if needed.
            // Wait, ensure_layout logic needs to handle this.

            Cow::Owned(Type {
                kind: TypeKind::Array {
                    element_type: element,
                    size: ArraySizeType::Constant(len as usize),
                },
                layout: None, // Computed on demand
            })
        } else {
            // Registry type
            Cow::Borrowed(&self.types[r.index()])
        }
    }

    /// Helper to get the pointee type if the given type is a pointer.
    pub(crate) fn get_pointee(&self, ty: TypeRef) -> Option<TypeRef> {
        if ty.is_inline_pointer() {
            Some(self.reconstruct_pointee(ty))
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
    pub(crate) fn pointer_to(&mut self, base: TypeRef) -> TypeRef {
        // Try inline
        // 1. If base is Inline Pointer (depth 1..2), we can increment depth (max 3).
        if base.is_inline_pointer() {
            let depth = base.pointer_depth();
            if depth < 3 {
                return TypeRef::new(base.base(), TypeClass::Pointer, depth + 1, 0).unwrap();
            }
        }

        // 2. If base is Simple (Ptr=0, Arr=0), we can make Inline Pointer depth 1.
        // Simple means it has a valid registry index and no inline modifiers.
        // Checks: Ptr=0, Arr=0.
        if base.pointer_depth() == 0 && base.array_len().is_none() {
            // This covers Builtin, Record, Enum, RegistryPointer, RegistryArray.
            // All these have valid BASE index and are "simple" references to registry.
            return TypeRef::new(base.base(), TypeClass::Pointer, 1, 0).unwrap();
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
    ) -> TypeRef {
        let key = FnSigKey {
            return_type,
            params: params.iter().map(|p| p.param_type.ty()).collect(),
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
        // If inline, compute on the fly (or if we had a cache, use it).
        // For now, since ensure_layout might mutate, this is tricky.
        // But get_layout assumes layout IS computed.

        if ty.is_inline_pointer() {
            return Cow::Owned(TypeLayout {
                size: 8,
                alignment: 8,
                kind: LayoutKind::Scalar,
            });
        }

        if ty.is_inline_array() {
            // We assume it's computed if called via get_layout.
            // But we don't store it for inline arrays.
            // We must recompute.
            // Recomputing array layout requires element layout.
            // This suggests get_layout might need to look up element.
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
            // Need to return Cow::Borrowed, but self is borrowed as mut.
            // We can re-borrow immutable from types.
            // However, the borrow checker might complain if we return borrow derived from self
            // while we hold mut ref? No, standard borrow rules apply.
            // We can return reference to self.types[idx].layout
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
                BuiltinType::LongDouble => TypeLayout {
                    size: 16,
                    alignment: 16,
                    kind: LayoutKind::Scalar,
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

        for member in members {
            let layout = self.ensure_layout(member.member_type.ty())?;
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

    pub(crate) fn decay(&mut self, qt: QualType) -> QualType {
        let kind = self.get(qt.ty()).kind.clone();
        match kind {
            TypeKind::Array { element_type, .. } => {
                let ptr = self.pointer_to(element_type);
                QualType::new(ptr, qt.qualifiers())
            }
            TypeKind::Function { .. } => {
                let ptr = self.pointer_to(qt.ty());
                QualType::new(ptr, qt.qualifiers())
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
        a == b
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
            TypeKind::Array { element_type, .. } => self.is_complete(*element_type),
            TypeKind::Builtin(BuiltinType::Void) => false,
            _ => true, // Scalars are always complete
        }
    }

    pub(crate) fn is_const_recursive(&self, qt: QualType) -> bool {
        if qt.is_const() {
            return true;
        }

        let ty_ref = qt.ty();
        if ty_ref.is_record() {
            if let TypeKind::Record { members, .. } = &self.get(ty_ref).kind {
                for member in members {
                    if self.is_const_recursive(member.member_type) {
                        return true;
                    }
                }
            }
        }
        false
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
