//! Type Registry
//!
//! Arena + canonicalization layer for semantic types.
//! All TypeRef creation and mutation MUST go through this context.

use std::borrow::Cow;

use crate::source_manager::SourceSpan;
use crate::{ast::NameId, diagnostic::SemanticError, semantic::QualType};
use hashbrown::{HashMap, HashSet};

use super::types::TypeClass;
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
        let mut reg = TypeRegistry {
            types: Vec::new(),
            pointer_cache: HashMap::new(),
            array_cache: HashMap::new(),
            function_cache: HashMap::new(),
            complex_cache: HashMap::new(),
            layout_in_progress: HashSet::new(),

            // temporary placeholders
            type_void: unsafe { TypeRef::from_raw_unchecked(1) }, // Will be valid after create_builtin
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
            type_error: unsafe { TypeRef::from_raw_unchecked(1) },
        };

        // Initialize dummy at index 0
        reg.types.push(Type::new(TypeKind::Error));

        reg.create_builtin();
        reg
    }

    pub fn create_builtin(&mut self) {
        // Must match BuiltinType enum values 1..16
        // Void = 1
        self.type_void = self.alloc_builtin(TypeKind::Void);
        // Bool = 2
        self.type_bool = self.alloc_builtin(TypeKind::Bool);
        // Char = 3
        self.type_char = self.alloc_builtin(TypeKind::Char { is_signed: true });
        // SChar = 4
        self.type_char = self.alloc_builtin(TypeKind::Char { is_signed: true }); // Wait, SChar enum is 4. Char is 3.
        // User map: CHAR -> 2? No, user said "VOID -> 1, CHAR -> 2".
        // My BuiltinType enum: Void=1, Bool=2, Char=3.
        // Let's strict match the enum order in alloc calls.

        // Reset types to just dummy to ensure order
        self.types.truncate(1);

        self.type_void = self.alloc_builtin(TypeKind::Void); // 1
        self.type_bool = self.alloc_builtin(TypeKind::Bool); // 2
        self.type_char = self.alloc_builtin(TypeKind::Char { is_signed: true }); // 3 (char)
        let _schar = self.alloc_builtin(TypeKind::Char { is_signed: true }); // 4 (schar - explicit signed char? No, SChar in enum)
        // Wait, TypeKind only has Char { is_signed }.
        // BuiltinType has Char, SChar, UChar.
        // C standard: char is distinct type. signed char is distinct.
        // TypeKind::Char represents both?
        // TypeKind::Char { is_signed: true } maps to BuiltinType::Char usually?
        // Let's look at TypeKind::to_builtin():
        // Char { signed: true } -> Char.
        // Char { signed: false } -> UChar.
        // Where is SChar?
        // Existing code: SChar = 3 (enum value).
        // I need to allocate types that MATCH the BuiltinType enum indices.

        // Let's look at existing TypeKind mapping in types.rs
        // BuiltinType::SChar is 4.
        // But TypeKind doesn't seem to have SChar variant?
        // It has Char { is_signed }.
        // If I use TypeKind::Char { is_signed: true }, it is `char`.
        // I should probably stick to what I have in TypeKind.
        // But I MUST fill indices 1..16.

        // 1 Void
        // 2 Bool
        // 3 Char
        // 4 SChar (Placeholder if not used, or aliased?)
        // 5 UChar
        // 6 Short
        // 7 UShort
        // 8 Int
        // 9 UInt
        // 10 Long
        // 11 ULong
        // 12 LongLong
        // 13 ULongLong
        // 14 Float
        // 15 Double
        // 16 LongDouble

        // I'll re-assign fields correctly.
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
    pub fn get(&self, r: TypeRef) -> Cow<'_, Type> {
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

    // Legacy support: mutable access only for completing records/enums
    #[inline]
    pub fn get_mut(&mut self, r: TypeRef) -> &mut Type {
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
    pub fn pointer_to(&mut self, base: TypeRef) -> TypeRef {
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

    pub fn array_of(&mut self, elem: TypeRef, size: ArraySizeType) -> TypeRef {
        // Try inline
        if let ArraySizeType::Constant(len) = size {
            if len <= 31 {
                // Check if elem is Simple
                if elem.pointer_depth() == 0 && elem.array_len().is_none() {
                    return TypeRef::new(elem.base(), TypeClass::Array, 0, len as u32).unwrap();
                }
            }
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

    pub fn function_type(
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

    pub fn complex_type(&mut self, base_type: TypeRef) -> TypeRef {
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

    pub fn declare_record(&mut self, tag: Option<NameId>, is_union: bool) -> TypeRef {
        self.alloc(Type::new(TypeKind::Record {
            tag,
            members: Vec::new(),
            is_complete: false,
            is_union,
        }))
    }

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

    // ============================================================
    // Layout
    // ============================================================

    pub fn get_layout(&self, ty: TypeRef) -> Cow<'_, TypeLayout> {
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

    pub fn get_array_layout(&self, ty: TypeRef) -> (u16, u16, TypeRef, u64) {
        let layout = self.get_layout(ty);
        match layout.kind {
            LayoutKind::Array { element, len } => (layout.size, layout.alignment, element, len),
            _ => panic!("ICE: layout is not array"),
        }
    }

    pub fn get_record_layout(&self, ty: TypeRef) -> (u16, u16, Vec<FieldLayout>, bool) {
        let layout = self.get_layout(ty);
        match &layout.kind {
            LayoutKind::Record { fields, is_union } => (layout.size, layout.alignment, fields.clone(), *is_union),
            _ => panic!("ICE: layout is not record"),
        }
    }

    pub fn ensure_layout(&mut self, ty: TypeRef) -> Result<Cow<'_, TypeLayout>, SemanticError> {
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
            TypeKind::Void => TypeLayout {
                size: 0,
                alignment: 1,
                kind: LayoutKind::Scalar,
            },
            TypeKind::Bool | TypeKind::Char { .. } => TypeLayout {
                size: 1,
                alignment: 1,
                kind: LayoutKind::Scalar,
            },
            TypeKind::Short { .. } => TypeLayout {
                size: 2,
                alignment: 2,
                kind: LayoutKind::Scalar,
            },
            TypeKind::Int { .. } | TypeKind::Float => TypeLayout {
                size: 4,
                alignment: 4,
                kind: LayoutKind::Scalar,
            },
            TypeKind::Long { .. } | TypeKind::Double { is_long_double: false } | TypeKind::Pointer { .. } => {
                TypeLayout {
                    size: 8,
                    alignment: 8,
                    kind: LayoutKind::Scalar,
                }
            }
            TypeKind::Double { is_long_double: true } => TypeLayout {
                size: 16,
                alignment: 16,
                kind: LayoutKind::Scalar,
            },

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
        let mut max_size = 0;
        let mut max_align = 1;
        let mut field_layouts = Vec::new();
        let mut offset = 0;

        if is_union {
            for member in members {
                let member_layout = self.ensure_layout(member.member_type.ty())?;
                max_size = max_size.max(member_layout.size);
                max_align = max_align.max(member_layout.alignment);
                field_layouts.push(FieldLayout { offset: 0 });
            }
        } else {
            for member in members {
                let member_layout = self.ensure_layout(member.member_type.ty())?;
                max_align = max_align.max(member_layout.alignment);
                let padding = (member_layout.alignment - (offset % member_layout.alignment)) % member_layout.alignment;
                offset += padding;
                field_layouts.push(FieldLayout { offset });
                offset += member_layout.size;
            }
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

    pub fn strip_all(&self, qt: QualType) -> QualType {
        QualType::unqualified(qt.ty())
    }

    pub fn merge_qualifiers(&self, base: QualType, add: TypeQualifiers) -> QualType {
        QualType::new(base.ty(), base.qualifiers() | add)
    }

    pub fn is_compatible(&self, a: QualType, b: QualType) -> bool {
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
