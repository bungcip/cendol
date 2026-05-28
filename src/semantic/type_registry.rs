//! Type Registry
//!
//! Arena + canonicalization layer for semantic types.
//! All TypeRef creation and mutation MUST go through this context.

use std::borrow::Cow;
use std::sync::Arc;

use crate::{
    ast::{NameId, NodeRef},
    semantic::QualType,
};
use hashbrown::{HashMap, HashSet};
use smallvec::SmallVec;
use target_lexicon::{PointerWidth, Triple};

use super::types::TypeClass;
use super::types::{FieldLayout, LayoutKind};
use super::{
    ArraySizeType, BuiltinType, EnumConstant, FunctionParam, RecordMember, Type, TypeKind, TypeLayout, TypeQualifiers,
    TypeRef,
};
use crate::semantic::BuiltinFunctionKind;

/// Errors that can occur during type layout computation in the TypeRegistry.
/// These are internal type system errors without source location information.
/// The caller is responsible for adding span context when converting to diagnostics.
#[derive(Debug, Clone)]
pub(crate) enum TypeRegistryError {
    /// Recursive type definition detected during layout computation
    RecursiveType { ty: TypeRef },
    /// Sizeof applied to an incomplete type (void, incomplete struct/union, etc.)
    SizeOfIncompleteType { ty: TypeRef },
    /// Sizeof applied to a function type
    SizeOfFunctionType,
    /// Variably modified type as struct member (VLA)
    VlaAsStructMember,
    /// Incomplete/VLA array in union (FAM is only for structures)
    IncompleteArrayInUnion,
    /// Flexible array member is not the last member
    FlexibleArrayNotLast,
    /// Flexible array member in otherwise empty structure
    FlexibleArrayInEmptyStruct,
    /// Member has function type
    MemberHasFunctionType { name: NameId },
    /// Incomplete type used as struct member
    IncompleteMemberType { ty: QualType },
    /// Unsupported feature
    UnsupportedFeature { feature: &'static str },
}

impl TypeRegistryError {
    /// Convert this type registry error to a SemanticError with an optional span.
    /// This allows the TypeRegistry to remain decoupled from source location tracking
    /// while still providing rich error information to the semantic analyzer.
    pub(crate) fn to_semantic_kind(&self) -> super::errors::SemanticError {
        use super::errors::SemanticError;
        match self {
            TypeRegistryError::RecursiveType { ty } => SemanticError::RecursiveType { ty: *ty },
            TypeRegistryError::SizeOfIncompleteType { ty } => SemanticError::SizeOfIncompleteType { ty: *ty },
            TypeRegistryError::SizeOfFunctionType => SemanticError::SizeOfFunctionType,
            TypeRegistryError::VlaAsStructMember => SemanticError::UnsupportedFeature {
                feature: "variably modified type (VLA) as struct member",
            },
            TypeRegistryError::IncompleteArrayInUnion => SemanticError::UnsupportedFeature {
                feature: "incomplete/VLA array in union",
            },
            TypeRegistryError::FlexibleArrayNotLast => SemanticError::FlexibleArrayNotLast,
            TypeRegistryError::FlexibleArrayInEmptyStruct => SemanticError::FlexibleArrayInEmptyStruct,
            TypeRegistryError::MemberHasFunctionType { name } => SemanticError::MemberHasFunctionType { name: *name },
            TypeRegistryError::IncompleteMemberType { ty } => SemanticError::IncompleteType { ty: *ty },
            TypeRegistryError::UnsupportedFeature { feature } => SemanticError::UnsupportedFeature { feature },
        }
    }
}

/// Central arena & factory for semantic types.
///
/// Invariants:
/// - All TypeRef come from this context
/// - Types are never removed
/// - Canonical types are reused when possible
#[derive(Clone)]
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
    pub type_complex_marker: TypeRef,
    pub type_nullptr_t: TypeRef,
    pub type_complex_float: TypeRef,
    pub type_complex_double: TypeRef,
    pub type_complex_long_double: TypeRef,
    pub type_error: TypeRef,
}

impl TypeRegistry {
    pub(crate) fn is_value_fitting(&self, val: i64, ty_ref: TypeRef) -> bool {
        // Bolt ⚡: Optimization: use ty_ref property checks before calling get().
        // This avoids Cow<Type> allocations for non-integer types (like pointers).
        if !ty_ref.is_integer() {
            return false;
        }

        let ty = self.get(ty_ref);
        let width = ty.width();
        if ty.is_signed() {
            let max = if width >= 64 {
                i64::MAX
            } else {
                (1i64 << (width - 1)) - 1
            };
            let min = if width >= 64 { i64::MIN } else { -(1i64 << (width - 1)) };
            val >= min && val <= max
        } else {
            if val < 0 {
                return false;
            }
            let max = if width >= 64 { u64::MAX } else { (1u64 << width) - 1 };
            (val as u64) <= max
        }
    }

    pub(crate) fn is_literal_fitting(&self, val: i64, ty_ref: TypeRef) -> bool {
        if val < 0 {
            // All literals are parsed as >= 0. If bits are negative in i64, it's [2^63, 2^64-1].
            // This only fits in 64-bit unsigned types.
            let ty = self.get(ty_ref);
            !ty.is_signed() && ty.is_int() && ty.width() >= 64
        } else {
            self.is_value_fitting(val, ty_ref)
        }
    }

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
            type_complex_marker: TypeRef::dummy(),
            type_nullptr_t: TypeRef::dummy(),
            type_complex_float: TypeRef::dummy(),
            type_complex_double: TypeRef::dummy(),
            type_complex_long_double: TypeRef::dummy(),
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
        self.type_void = self.alloc_builtin(BuiltinType::Void);

        // 2: Bool
        self.type_bool = self.alloc_builtin(BuiltinType::Bool);

        // 3: Char (signed)
        self.type_char = self.alloc_builtin(BuiltinType::Char);

        // 4: SChar (explicit signed char)
        self.type_schar = self.alloc_builtin(BuiltinType::SChar);

        // 5: UChar
        self.type_char_unsigned = self.alloc_builtin(BuiltinType::UChar);

        // 6: Short
        self.type_short = self.alloc_builtin(BuiltinType::Short);

        // 7: UShort
        self.type_short_unsigned = self.alloc_builtin(BuiltinType::UShort);

        // 8: Int
        self.type_int = self.alloc_builtin(BuiltinType::Int);

        // 9: UInt
        self.type_int_unsigned = self.alloc_builtin(BuiltinType::UInt);

        // 10: Long
        self.type_long = self.alloc_builtin(BuiltinType::Long);

        // 11: ULong
        self.type_long_unsigned = self.alloc_builtin(BuiltinType::ULong);

        // 12: LongLong
        self.type_long_long = self.alloc_builtin(BuiltinType::LongLong);

        // 13: ULongLong
        self.type_long_long_unsigned = self.alloc_builtin(BuiltinType::ULongLong);

        // 14: Float
        self.type_float = self.alloc_builtin(BuiltinType::Float);

        // 15: Double
        self.type_double = self.alloc_builtin(BuiltinType::Double);

        // 16: LongDouble
        self.type_long_double = self.alloc_builtin(BuiltinType::LongDouble);

        // 17: Signed (marker)
        self.type_signed = self.alloc_builtin(BuiltinType::Signed);

        // 18: VaList - on x86_64 SysV this is an array of 1 struct
        let valist_struct = self.alloc_builtin(BuiltinType::VaList);
        self.type_valist = self.array_of(valist_struct, ArraySizeType::Constant(1));

        // 19: Complex (marker)
        self.type_complex_marker = self.alloc_builtin(BuiltinType::Complex);

        // -- Allocated builtins (beyond the 1..19 sequence) --

        // nullptr_t
        self.type_nullptr_t = self.alloc(Type::new(TypeKind::NullptrT));

        // complex float
        self.type_complex_float = self.complex_type(self.type_float);
        // complex double
        self.type_complex_double = self.complex_type(self.type_double);
        // complex long double
        self.type_complex_long_double = self.complex_type(self.type_long_double);

        // Pre-calculate void*
        self.type_void_ptr = self.pointer_to(QualType::unqualified(self.type_void));

        // We can assert that the last allocated index was 25
        // (19 builtins + nullptr_t + 3 complex types = 23)
        debug_assert_eq!(self.types.len() - 1, 23, "Builtin types allocation mismatch");

        // Compute layouts for all builtins immediately
        // This prevents ICEs when code generation assumes builtins have layouts
        let builtins = [
            self.type_void,
            self.type_bool,
            self.type_char,
            self.type_schar,
            self.type_char_unsigned,
            self.type_short,
            self.type_short_unsigned,
            self.type_int,
            self.type_int_unsigned,
            self.type_long,
            self.type_long_unsigned,
            self.type_long_long,
            self.type_long_long_unsigned,
            self.type_float,
            self.type_double,
            self.type_long_double,
            self.type_signed,
            self.type_valist,
            self.type_complex_marker,
            self.type_nullptr_t,
            self.type_complex_float,
            self.type_complex_double,
            self.type_complex_long_double,
            self.type_void_ptr,
        ];

        for &ty in &builtins {
            let _ = self.ensure_layout(ty);
        }
    }

    fn alloc_builtin(&mut self, kind: BuiltinType) -> TypeRef {
        let ty = Type::new(TypeKind::Builtin(kind));
        self.alloc(ty)
    }

    pub(crate) fn get_builtin_type(&self, b: BuiltinType) -> TypeRef {
        match b {
            BuiltinType::Void => self.type_void,
            BuiltinType::Bool => self.type_bool,
            BuiltinType::Char => self.type_char,
            BuiltinType::SChar => self.type_schar,
            BuiltinType::UChar => self.type_char_unsigned,
            BuiltinType::Short => self.type_short,
            BuiltinType::UShort => self.type_short_unsigned,
            BuiltinType::Int => self.type_int,
            BuiltinType::UInt => self.type_int_unsigned,
            BuiltinType::Long => self.type_long,
            BuiltinType::ULong => self.type_long_unsigned,
            BuiltinType::LongLong => self.type_long_long,
            BuiltinType::ULongLong => self.type_long_long_unsigned,
            BuiltinType::Float => self.type_float,
            BuiltinType::Double => self.type_double,
            BuiltinType::LongDouble => self.type_long_double,
            BuiltinType::Signed => self.type_signed,
            BuiltinType::VaList => self.type_valist,
            BuiltinType::Complex => self.type_complex_marker,
        }
    }

    /// Allocate a new canonical type and return its TypeRef.
    fn alloc(&mut self, ty: Type) -> TypeRef {
        let idx = self.types.len() as u32;
        self.types.push(ty);
        let kind = &self.types[idx as usize].kind;
        let class = kind.to_class();

        TypeRef::new(idx, class, 0, 0).expect("TypeRef alloc failed")
    }

    pub(crate) fn auto_type(&mut self) -> TypeRef {
        self.alloc(Type::new(TypeKind::AutoType))
    }

    pub(crate) fn typeof_expr(&mut self, expr_node: NodeRef) -> TypeRef {
        self.alloc(Type::new(TypeKind::TypeofExpr(expr_node)))
    }

    pub(crate) fn typeof_unqual_expr(&mut self, expr_node: NodeRef) -> TypeRef {
        self.alloc(Type::new(TypeKind::TypeofUnqualExpr(expr_node)))
    }

    /// Get the unsigned version of a builtin integer type.
    pub(crate) fn get_unsigned_corresponding_type(&self, mut ty: TypeRef) -> TypeRef {
        loop {
            // Bolt ⚡: Optimization: First check for bitfield-encoded builtins (common case).
            if let Some(b) = ty.builtin() {
                return self.get_builtin_type(b.to_unsigned());
            }

            // Bolt ⚡: Use TypeClass for fast dispatch.
            // Builtins and aliases are the only candidates for integer conversion.
            match ty.class() {
                TypeClass::Builtin => {
                    if let TypeKind::Builtin(b) = &self.types[ty.index()].kind {
                        return self.get_builtin_type(b.to_unsigned());
                    }
                    return ty;
                }
                TypeClass::Alias => {
                    if let TypeKind::Alias(inner) = &self.types[ty.index()].kind {
                        ty = *inner;
                    } else {
                        return ty;
                    }
                }
                _ => return ty,
            }
        }
    }

    /// Resolve a TypeRef to a Type.
    /// Returns Cow because inline types are constructed on the fly.
    #[inline]
    pub(crate) fn get(&self, mut r: TypeRef) -> Cow<'_, Type> {
        // Bolt ⚡: Fast-path for non-alias terminal types in registry.
        // Terminal types (Builtin, Record, Enum, Complex, Function, registry-backed Pointers/Arrays)
        // represent the majority of types during analysis. Bypassing the loop/match for them
        // significantly reduces overhead in this hot path.
        if r.is_simple_index() && r.class() != TypeClass::Alias {
            return Cow::Borrowed(&self.types[r.index()]);
        }

        loop {
            // Bolt ⚡: Use TypeClass for fast dispatch.
            // This avoids redundant matches and property checks for terminal types.
            match r.class() {
                TypeClass::Pointer if r.is_inline_pointer() => {
                    let pointee = self.reconstruct_pointee(r);
                    return Cow::Owned(Type {
                        kind: TypeKind::Pointer {
                            pointee: QualType::unqualified(pointee),
                        },
                        layout: Some(TypeLayout {
                            size: 8,
                            alignment: 8,
                            kind: LayoutKind::Scalar,
                        }),
                    });
                }
                TypeClass::Array if r.is_inline_array() => {
                    let element = self.reconstruct_element(r);
                    let len = r.array_len().unwrap() as u64;
                    return Cow::Owned(Type {
                        kind: TypeKind::Array {
                            element_type: element,
                            size: ArraySizeType::Constant(len as usize),
                        },
                        layout: None,
                    });
                }
                TypeClass::Alias => {
                    // Bolt ⚡: Match on reference to avoid cloning the large TypeKind enum.
                    if let TypeKind::Alias(inner) = &self.types[r.index()].kind {
                        r = *inner;
                        continue;
                    }
                    return Cow::Borrowed(&self.types[r.index()]);
                }
                _ => return Cow::Borrowed(&self.types[r.index()]),
            }
        }
    }

    /// Helper to get the pointee type if the given type is a pointer.
    pub(crate) fn get_pointee(&self, mut ty: TypeRef) -> Option<QualType> {
        loop {
            // Bolt ⚡: Fast path for non-pointer types to avoid registry lookup and match.
            // Pointers and aliases (which might resolve to pointers) are the only candidates.
            let class = ty.class();
            if class != TypeClass::Pointer && class != TypeClass::Alias {
                return None;
            }

            if ty.is_inline_pointer() {
                return Some(QualType::unqualified(self.reconstruct_pointee(ty)));
            } else {
                let t = &self.types[ty.index()];
                // Bolt ⚡: Match on reference to avoid cloning the large TypeKind enum.
                if let TypeKind::Alias(inner) = &t.kind {
                    ty = *inner;
                    continue;
                }
                match &t.kind {
                    TypeKind::Pointer { pointee } => return Some(*pointee),
                    _ => return None,
                }
            }
        }
    }

    /// Check if a type is a structure with a flexible array member (FAM).
    /// C11 6.7.2.1p18: "the last element of a structure ... may have an incomplete array type"
    pub(crate) fn has_flexible_array_member(&self, ty: TypeRef) -> bool {
        if ty.is_pointer() || ty.is_array() {
            return false;
        }
        if ty.builtin().is_some() {
            return false;
        }

        match &self.types[ty.index()].kind {
            TypeKind::Alias(inner) => self.has_flexible_array_member(*inner),
            TypeKind::Record { members, is_union, .. } => {
                if *is_union {
                    // A union has a FAM if any of its members recursively has one.
                    members
                        .iter()
                        .any(|m| self.has_flexible_array_member(m.member_type.ty()))
                } else {
                    // A structure has a FAM if its last member is an incomplete array
                    // OR if any member recursively has a FAM (making the whole struct VM/illegal as member).
                    if let Some(last) = members.last()
                        && let TypeKind::Array {
                            size: ArraySizeType::Incomplete,
                            ..
                        } = &self.get(last.member_type.ty()).kind
                    {
                        return true;
                    }
                    // Recurse to see if any member has a FAM (nested)
                    members
                        .iter()
                        .any(|m| self.has_flexible_array_member(m.member_type.ty()))
                }
            }
            _ => false,
        }
    }

    pub(crate) fn is_char_type(&self, mut ty: TypeRef) -> bool {
        loop {
            // Bolt ⚡: Use TypeClass for fast dispatch to avoid redundant bitfield decoding.
            // This optimization reduces analysis time by skipping registry lookups for non-char types.
            match ty.class() {
                TypeClass::Builtin => {
                    if let Some(b) = BuiltinType::from_u32(ty.base()) {
                        return b.is_char();
                    }
                    // Fallback for registry-backed builtins (e.g. Error or synthetic types).
                    match &self.types[ty.index()].kind {
                        TypeKind::Builtin(b) => return b.is_char(),
                        _ => return false,
                    }
                }
                TypeClass::Alias => {
                    if let TypeKind::Alias(inner) = &self.types[ty.index()].kind {
                        ty = *inner;
                    } else {
                        return false;
                    }
                }
                _ => return false,
            }
        }
    }

    /// Helper to get the element type if the given type is an array.
    pub(super) fn get_array_element(&self, mut ty: TypeRef) -> Option<TypeRef> {
        loop {
            // Bolt ⚡: Fast path for non-array types to avoid registry lookup and match.
            let class = ty.class();
            if class != TypeClass::Array && class != TypeClass::Alias {
                return None;
            }

            if ty.is_inline_array() {
                return Some(self.reconstruct_element(ty));
            }

            // Bolt ⚡: Direct registry access avoids Cow<Type> allocations in hot loops.
            match &self.types[ty.index()].kind {
                TypeKind::Alias(inner) => ty = *inner,
                TypeKind::Array { element_type, .. } => return Some(*element_type),
                _ => return None,
            }
        }
    }

    pub(crate) fn is_function_type(&self, mut ty: TypeRef) -> bool {
        loop {
            // Bolt ⚡: Fast path to avoid registry lookup for non-function types.
            let class = ty.class();
            if class != TypeClass::Function && class != TypeClass::Alias {
                return false;
            }

            // Bolt ⚡: Direct registry access avoids Cow<Type> allocations.
            match &self.types[ty.index()].kind {
                TypeKind::Alias(inner) => ty = *inner,
                TypeKind::Function { .. } => return true,
                _ => return false,
            }
        }
    }

    pub(crate) fn is_noreturn_function(&self, mut ty: TypeRef) -> bool {
        loop {
            // Bolt ⚡: Fast path to avoid registry lookup for non-function types.
            let class = ty.class();
            if class != TypeClass::Function && class != TypeClass::Alias {
                return false;
            }

            // Bolt ⚡: Direct registry access avoids Cow<Type> allocations.
            match &self.types[ty.index()].kind {
                TypeKind::Alias(inner) => ty = *inner,
                TypeKind::Function { is_noreturn, .. } => return *is_noreturn,
                _ => return false,
            }
        }
    }

    pub(crate) fn get_complex_base(&self, mut ty: TypeRef) -> Option<TypeRef> {
        loop {
            // Bolt ⚡: Fast path to avoid registry lookup for non-complex types.
            let class = ty.class();
            if class != TypeClass::Complex && class != TypeClass::Alias {
                return None;
            }

            // Bolt ⚡: Direct registry access avoids Cow<Type> allocations.
            match &self.types[ty.index()].kind {
                TypeKind::Alias(inner) => ty = *inner,
                TypeKind::Complex { base_type } => return Some(*base_type),
                _ => return None,
            }
        }
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
    pub(crate) fn find_pointer_to(&self, base: QualType) -> Option<TypeRef> {
        if base.qualifiers().is_empty() {
            let base_ty = base.ty();
            if base_ty.is_inline_pointer() {
                let depth = base_ty.pointer_depth();
                if depth < 3 {
                    return TypeRef::new(base_ty.base(), TypeClass::Pointer, depth + 1, 0);
                }
            }
            if base_ty.pointer_depth() == 0 && base_ty.array_len().is_none() {
                return TypeRef::new(base_ty.base(), TypeClass::Pointer, 1, 0);
            }
        }
        self.pointer_cache.get(&base).copied()
    }

    pub(crate) fn find_decayed_type(&self, qt: QualType) -> Option<QualType> {
        if qt.is_array() {
            let elem = self.get_array_element(qt.ty())?;
            let ptr = self.find_pointer_to(QualType::unqualified(elem))?;
            Some(QualType::unqualified(ptr))
        } else if qt.is_function() {
            let ptr = self.find_pointer_to(qt)?;
            Some(QualType::unqualified(ptr))
        } else {
            Some(qt)
        }
    }

    pub(crate) fn find_composite_type(&self, a: QualType, b: QualType) -> Option<QualType> {
        if a == b {
            return Some(a);
        }

        if a.qualifiers() != b.qualifiers() {
            return None;
        }

        if a.ty() == b.ty() {
            return Some(a);
        }

        let ty_a = a.ty();
        let ty_b = b.ty();

        if let (Some(pa), Some(pb)) = (self.get_pointee(ty_a), self.get_pointee(ty_b)) {
            let composite_pointee = self.find_composite_type(pa, pb)?;
            let res_ty = self.find_pointer_to(composite_pointee)?;
            return Some(QualType::new(res_ty, a.qualifiers()));
        }

        if let (Some(ea), Some(eb)) = (self.get_array_element(ty_a), self.get_array_element(ty_b)) {
            let composite_elem = self.find_composite_type(QualType::unqualified(ea), QualType::unqualified(eb))?;
            let sa = if ty_a.is_inline_array() {
                ArraySizeType::Constant(ty_a.array_len().unwrap() as usize)
            } else {
                match &self.types[ty_a.index()].kind {
                    TypeKind::Array { size, .. } => *size,
                    _ => unreachable!(),
                }
            };
            let sb = if ty_b.is_inline_array() {
                ArraySizeType::Constant(ty_b.array_len().unwrap() as usize)
            } else {
                match &self.types[ty_b.index()].kind {
                    TypeKind::Array { size, .. } => *size,
                    _ => unreachable!(),
                }
            };

            let composite_size = match (sa, sb) {
                (ArraySizeType::Incomplete, s) => s,
                (s, ArraySizeType::Incomplete) => s,
                (ArraySizeType::Constant(sa), ArraySizeType::Constant(sb)) if sa == sb => ArraySizeType::Constant(sa),
                (ArraySizeType::Star, s) => s,
                (s, ArraySizeType::Star) => s,
                _ => return None,
            };

            let res_ty = self.find_array_type(composite_elem.ty(), composite_size)?;
            return Some(QualType::new(res_ty, a.qualifiers()));
        }

        let type_a = self.get(ty_a);
        let type_b = self.get(ty_b);

        match (&type_a.kind, &type_b.kind) {
            (
                TypeKind::Function {
                    return_type: ret_a,
                    parameters: params_a,
                    is_variadic: var_a,
                    is_noreturn: nor_a,
                },
                TypeKind::Function {
                    return_type: ret_b,
                    parameters: params_b,
                    is_variadic: var_b,
                    is_noreturn: nor_b,
                },
            ) => {
                if var_a != var_b || nor_a != nor_b {
                    return None;
                }
                let ret_composite =
                    self.find_composite_type(QualType::unqualified(*ret_a), QualType::unqualified(*ret_b))?;
                if params_a.len() != params_b.len() {
                    return None;
                }
                let mut composite_params = Vec::new();
                for (p_a, p_b) in params_a.iter().zip(params_b.iter()) {
                    let p_composite = self.find_composite_type(p_a.param_type, p_b.param_type)?;
                    composite_params.push(p_composite);
                }
                let key = FnSigKey {
                    return_type: ret_composite.ty(),
                    params: composite_params.iter().copied().collect(),
                    is_variadic: *var_a,
                    is_noreturn: *nor_a,
                };
                let f = self.function_cache.get(&key).copied()?;
                Some(QualType::new(f, a.qualifiers()))
            }
            _ => None,
        }
    }

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
        if let Some(arr) = self.find_array_type(elem, size) {
            return arr;
        }

        let key = (elem, size);
        let arr = self.alloc(Type::new(TypeKind::Array {
            element_type: elem,
            size,
        }));
        self.array_cache.insert(key, arr);
        arr
    }
    pub(crate) fn find_array_type(&self, elem: TypeRef, size: ArraySizeType) -> Option<TypeRef> {
        // Try inline (only for length 1..31, 0 is used for registry-backed arrays)
        if let ArraySizeType::Constant(len) = size
            && (1..=31).contains(&len)
            && elem.pointer_depth() == 0
            && elem.array_len().is_none()
        {
            // Check if elem is Simple
            return Some(TypeRef::new(elem.base(), TypeClass::Array, 0, len as u32).unwrap());
        }

        let key = (elem, size);
        self.array_cache.get(&key).copied()
    }

    pub(crate) fn function_type(
        &mut self,
        return_type: TypeRef,
        params: Vec<FunctionParam>,
        is_variadic: bool,
        is_noreturn: bool,
    ) -> TypeRef {
        // Bolt ⚡: Collect into SmallVec to avoid heap allocation for the lookup key
        // in the common case (<= 8 parameters).
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
            parameters: Arc::from(params),
            is_variadic,
            is_noreturn,
        }));

        self.function_cache.insert(key, f);
        f
    }

    pub(crate) fn builtin_function_type(&mut self, name: BuiltinFunctionKind) -> TypeRef {
        let q = |ty: TypeRef| QualType::unqualified(ty);
        let p = |ty: TypeRef| FunctionParam {
            param_type: QualType::unqualified(ty),
            name: None,
            storage: None,
        };
        let pq = |qty: QualType| FunctionParam {
            param_type: qty,
            name: None,
            storage: None,
        };

        let (params, ret_ty, is_variadic, is_noreturn) = match name {
            BuiltinFunctionKind::Nanf | BuiltinFunctionKind::Nan => {
                let char_const = QualType::new(self.type_char, TypeQualifiers::CONST);
                let char_ptr = q(self.pointer_to(char_const));
                let ret = if name == BuiltinFunctionKind::Nanf {
                    self.type_float
                } else {
                    self.type_double
                };
                (vec![pq(char_ptr)], ret, false, false)
            }
            BuiltinFunctionKind::Inff
            | BuiltinFunctionKind::Inf
            | BuiltinFunctionKind::HugeValf
            | BuiltinFunctionKind::HugeVal => {
                let ret = if matches!(name, BuiltinFunctionKind::Inff | BuiltinFunctionKind::HugeValf) {
                    self.type_float
                } else {
                    self.type_double
                };
                (vec![], ret, false, false)
            }
            BuiltinFunctionKind::Signbit | BuiltinFunctionKind::SignbitF | BuiltinFunctionKind::SignbitL => {
                let param_ty = match name {
                    BuiltinFunctionKind::SignbitF => self.type_float,
                    BuiltinFunctionKind::Signbit => self.type_double,
                    _ => self.type_long_double,
                };
                (vec![p(param_ty)], self.type_int, false, false)
            }
            kind @ (BuiltinFunctionKind::Popcount
            | BuiltinFunctionKind::PopcountL
            | BuiltinFunctionKind::PopcountLL
            | BuiltinFunctionKind::Clz
            | BuiltinFunctionKind::ClzL
            | BuiltinFunctionKind::ClzLL
            | BuiltinFunctionKind::Ctz
            | BuiltinFunctionKind::CtzL
            | BuiltinFunctionKind::CtzLL
            | BuiltinFunctionKind::Ffs
            | BuiltinFunctionKind::FfsL
            | BuiltinFunctionKind::FfsLL) => {
                let param_ty = match kind {
                    BuiltinFunctionKind::Clz | BuiltinFunctionKind::Ctz | BuiltinFunctionKind::Popcount => {
                        self.type_int_unsigned
                    }
                    BuiltinFunctionKind::ClzL | BuiltinFunctionKind::CtzL | BuiltinFunctionKind::PopcountL => {
                        self.type_long_unsigned
                    }
                    BuiltinFunctionKind::ClzLL | BuiltinFunctionKind::CtzLL | BuiltinFunctionKind::PopcountLL => {
                        self.type_long_long_unsigned
                    }
                    BuiltinFunctionKind::Ffs => self.type_int,
                    BuiltinFunctionKind::FfsL => self.type_long,
                    BuiltinFunctionKind::FfsLL => self.type_long_long,
                    _ => unreachable!("ICE: unexpected bitwise builtin {:?}", kind),
                };
                (vec![p(param_ty)], self.type_int, false, false)
            }
            BuiltinFunctionKind::Bswap16 | BuiltinFunctionKind::Bswap32 | BuiltinFunctionKind::Bswap64 => {
                let ty = match name {
                    BuiltinFunctionKind::Bswap16 => self.type_short_unsigned,
                    BuiltinFunctionKind::Bswap32 => self.type_int_unsigned,
                    _ => self.type_long_long_unsigned,
                };
                (vec![p(ty)], ty, false, false)
            }
            kind @ (BuiltinFunctionKind::FabsF | BuiltinFunctionKind::Fabs | BuiltinFunctionKind::FabsL) => {
                let ty = match kind {
                    BuiltinFunctionKind::FabsF => self.type_float,
                    BuiltinFunctionKind::Fabs => self.type_double,
                    _ => self.type_long_double,
                };
                (vec![p(ty)], ty, false, false)
            }
            BuiltinFunctionKind::Alloca => (vec![p(self.type_long_unsigned)], self.type_void_ptr, false, false),
            BuiltinFunctionKind::Expect => {
                let long = self.type_long;
                (vec![p(long), p(long)], long, false, false)
            }
            BuiltinFunctionKind::ConstantP => (vec![], self.type_int, true, false),
            BuiltinFunctionKind::Unreachable | BuiltinFunctionKind::Trap => (vec![], self.type_void, false, true),
            BuiltinFunctionKind::Prefetch => (vec![p(self.type_void_ptr)], self.type_void, true, false),
            BuiltinFunctionKind::FrameAddress => (vec![p(self.type_int_unsigned)], self.type_void_ptr, false, false),
            BuiltinFunctionKind::Pause => (vec![], self.type_void, false, false),
            BuiltinFunctionKind::Memcpy | BuiltinFunctionKind::Memmove => {
                let void_ptr = self.type_void_ptr;
                let const_void = QualType::new(self.type_void, TypeQualifiers::CONST);
                let const_void_ptr = q(self.pointer_to(const_void));
                let size_t = self.type_long_unsigned;

                (
                    vec![pq(q(void_ptr)), pq(const_void_ptr), p(size_t)],
                    void_ptr,
                    false,
                    false,
                )
            }
            BuiltinFunctionKind::Memset => {
                let void_ptr = self.type_void_ptr;
                let size_t = self.type_long_unsigned;
                (
                    vec![pq(q(void_ptr)), p(self.type_int), p(size_t)],
                    void_ptr,
                    false,
                    false,
                )
            }
            BuiltinFunctionKind::Memcmp => {
                let const_void = QualType::new(self.type_void, TypeQualifiers::CONST);
                let const_void_ptr = q(self.pointer_to(const_void));
                let size_t = self.type_long_unsigned;
                (
                    vec![pq(const_void_ptr), pq(const_void_ptr), p(size_t)],
                    self.type_int,
                    false,
                    false,
                )
            }
            BuiltinFunctionKind::VaStart => (vec![p(self.type_void_ptr)], self.type_void, true, false),
            BuiltinFunctionKind::VaEnd => (vec![p(self.type_void_ptr)], self.type_void, false, false),
            BuiltinFunctionKind::VaCopy => {
                let vp = self.type_void_ptr;
                (vec![p(vp), p(vp)], self.type_void, false, false)
            }
            BuiltinFunctionKind::AtomicLoadN
            | BuiltinFunctionKind::AtomicStoreN
            | BuiltinFunctionKind::AtomicExchangeN
            | BuiltinFunctionKind::AtomicCompareExchangeN
            | BuiltinFunctionKind::AtomicFetchAdd
            | BuiltinFunctionKind::AtomicFetchSub
            | BuiltinFunctionKind::AtomicFetchAnd
            | BuiltinFunctionKind::AtomicFetchOr
            | BuiltinFunctionKind::AtomicFetchXor => (vec![], self.type_void_ptr, true, false),
            BuiltinFunctionKind::Complex => {
                let d = self.type_double;
                (vec![p(d), p(d)], self.type_complex_double, false, false)
            }
        };

        self.function_type(ret_ty, params, is_variadic, is_noreturn)
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

    /// Look up a previously created complex type without allocating.
    /// Returns `None` if the complex type hasn't been created yet.
    pub(crate) fn find_complex_type(&self, base_type: TypeRef) -> Option<TypeRef> {
        self.complex_cache.get(&base_type).copied()
    }

    // ============================================================
    // Record / enum handling
    // ============================================================

    pub(super) fn declare_record(&mut self, tag: Option<NameId>, is_union: bool) -> TypeRef {
        self.alloc(Type::new(TypeKind::Record {
            tag,
            members: Arc::from([]),
            is_complete: false,
            is_union,
            packing: None,
            alignment: None,
        }))
    }

    pub(crate) fn complete_record(
        &mut self,
        record: TypeRef,
        members: Arc<[RecordMember]>,
        packing: Option<u32>,
        alignment: Option<u16>,
    ) {
        let ty = &mut self.types[record.index()];
        match &mut ty.kind {
            TypeKind::Record {
                is_complete,
                members: slot,
                packing: packing_slot,
                alignment: alignment_slot,
                ..
            } => {
                *slot = members;
                *is_complete = true;
                *packing_slot = packing;
                *alignment_slot = alignment;
            }
            _ => unreachable!("complete_record on non-record"),
        }
    }

    pub(super) fn declare_enum(&mut self, tag: Option<NameId>, base_type: TypeRef, has_fixed: bool) -> TypeRef {
        self.alloc(Type::new(TypeKind::Enum {
            tag,
            base_type,
            enumerators: Arc::from([]),
            is_complete: false,
            has_fixed_underlying_type: has_fixed,
        }))
    }

    pub(super) fn complete_enum(
        &mut self,
        enum_ty: TypeRef,
        enumerators: Arc<[EnumConstant]>,
        base_type: TypeRef,
        has_fixed: bool,
    ) {
        let ty = &mut self.types[enum_ty.index()];
        match &mut ty.kind {
            TypeKind::Enum {
                is_complete,
                enumerators: slot,
                base_type: base_slot,
                has_fixed_underlying_type: fixed_slot,
                ..
            } => {
                *slot = enumerators;
                *base_slot = base_type;
                *is_complete = true;
                *fixed_slot = has_fixed;
            }
            _ => unreachable!("complete_enum on non-enum"),
        }
    }

    // ============================================================
    // Layout
    // ============================================================

    pub(crate) fn get_layout(&self, mut ty: TypeRef) -> Cow<'_, TypeLayout> {
        loop {
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
                    size: elem_layout.size * len, // Potential overflow if not careful, but C rules apply
                    alignment: elem_layout.alignment,
                    kind: LayoutKind::Array { element: elem, len },
                });
            }

            let idx = ty.index();
            let repr = &self.types[idx];
            // Bolt ⚡: Match on reference to avoid cloning the large TypeKind enum.
            if let TypeKind::Alias(inner) = &repr.kind {
                ty = *inner;
            } else {
                match repr.layout.as_ref() {
                    Some(x) => return Cow::Borrowed(x),
                    None => {
                        panic!("ICE: TypeRef {ty} layout not computed. make sure layout is computed in previous phase")
                    }
                }
            }
        }
    }

    /// Safe version of get_layout that returns None instead of panicking when layout is missing.
    /// Used during lowering phase when layouts may not yet be computed.
    pub(super) fn try_get_layout(&self, mut ty: TypeRef) -> Option<Cow<'_, TypeLayout>> {
        loop {
            if ty.is_inline_pointer() {
                return Some(Cow::Owned(TypeLayout {
                    size: 8,
                    alignment: 8,
                    kind: LayoutKind::Scalar,
                }));
            }

            if ty.is_inline_array() {
                let elem = self.reconstruct_element(ty);
                let elem_layout = self.try_get_layout(elem)?;
                let len = ty.array_len().unwrap() as u64;
                return Some(Cow::Owned(TypeLayout {
                    size: elem_layout.size * len,
                    alignment: elem_layout.alignment,
                    kind: LayoutKind::Array { element: elem, len },
                }));
            }

            let idx = ty.index();
            let repr = &self.types[idx];
            // Bolt ⚡: Match on reference to avoid cloning the large TypeKind enum.
            if let TypeKind::Alias(inner) = &repr.kind {
                ty = *inner;
            } else {
                if let Some(layout) = repr.layout.as_ref() {
                    return Some(Cow::Borrowed(layout));
                }

                // Fallback for types that don't need mutation to compute
                return match &repr.kind {
                    TypeKind::Builtin(b) => match b {
                        BuiltinType::Void => None,
                        BuiltinType::Bool | BuiltinType::Char | BuiltinType::SChar | BuiltinType::UChar => {
                            Some(Cow::Owned(TypeLayout {
                                size: 1,
                                alignment: 1,
                                kind: LayoutKind::Scalar,
                            }))
                        }
                        BuiltinType::Short | BuiltinType::UShort => Some(Cow::Owned(TypeLayout {
                            size: 2,
                            alignment: 2,
                            kind: LayoutKind::Scalar,
                        })),
                        BuiltinType::Int | BuiltinType::UInt | BuiltinType::Float => Some(Cow::Owned(TypeLayout {
                            size: 4,
                            alignment: 4,
                            kind: LayoutKind::Scalar,
                        })),
                        BuiltinType::Long | BuiltinType::ULong => {
                            let size = match self.target_triple.pointer_width() {
                                Ok(target_lexicon::PointerWidth::U16) => 2,
                                Ok(target_lexicon::PointerWidth::U32) => 4,
                                Ok(target_lexicon::PointerWidth::U64) => 8,
                                Err(_) => 8,
                            };
                            Some(Cow::Owned(TypeLayout {
                                size,
                                alignment: size as u16,
                                kind: LayoutKind::Scalar,
                            }))
                        }
                        BuiltinType::LongLong | BuiltinType::ULongLong | BuiltinType::Double => {
                            Some(Cow::Owned(TypeLayout {
                                size: 8,
                                alignment: 8,
                                kind: LayoutKind::Scalar,
                            }))
                        }
                        BuiltinType::LongDouble => Some(Cow::Owned(TypeLayout {
                            size: 16,
                            alignment: 16,
                            kind: LayoutKind::Scalar,
                        })),
                        BuiltinType::Signed => Some(Cow::Owned(TypeLayout {
                            size: 4,
                            alignment: 4,
                            kind: LayoutKind::Scalar,
                        })),
                        BuiltinType::VaList => Some(Cow::Owned(TypeLayout {
                            size: 24,
                            alignment: 8,
                            kind: LayoutKind::Scalar,
                        })), // x86_64 sysv va_list is 24 bytes
                        BuiltinType::Complex => None, // Complex layout handled via TypeKind::Complex
                    },
                    TypeKind::Pointer { .. } => Some(Cow::Owned(TypeLayout {
                        size: 8,
                        alignment: 8,
                        kind: LayoutKind::Scalar,
                    })),
                    TypeKind::Array {
                        element_type,
                        size: ArraySizeType::Constant(len),
                    } => {
                        let elem_layout = self.try_get_layout(*element_type)?;
                        Some(Cow::Owned(TypeLayout {
                            size: elem_layout.size * (*len as u64),
                            alignment: elem_layout.alignment,
                            kind: LayoutKind::Array {
                                element: *element_type,
                                len: *len as u64,
                            },
                        }))
                    }
                    TypeKind::Complex { base_type } => {
                        let base_layout = self.try_get_layout(*base_type)?;
                        Some(Cow::Owned(TypeLayout {
                            size: base_layout.size * 2,
                            alignment: base_layout.alignment,
                            kind: LayoutKind::Scalar,
                        }))
                    }
                    _ => None,
                };
            }
        }
    }

    pub(crate) fn get_array_layout(&self, ty: TypeRef) -> (u64, u64, TypeRef, u64) {
        let layout = self.get_layout(ty);
        match layout.kind {
            LayoutKind::Array { element, len } => (layout.size, layout.alignment as u64, element, len),
            _ => panic!("ICE: layout is not array"),
        }
    }

    pub(crate) fn ensure_layout(&mut self, ty: TypeRef) -> Result<Cow<'_, TypeLayout>, TypeRegistryError> {
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
            let size = elem_layout.size * len;

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

    fn compute_layout(&mut self, ty: TypeRef) -> Result<TypeLayout, TypeRegistryError> {
        if self.layout_in_progress.contains(&ty) {
            return Err(TypeRegistryError::RecursiveType { ty });
        }

        self.layout_in_progress.insert(ty);
        let result = self.compute_layout_internal(ty);
        self.layout_in_progress.remove(&ty);
        result
    }

    fn compute_layout_internal(&mut self, ty: TypeRef) -> Result<TypeLayout, TypeRegistryError> {
        // Bolt ⚡: Optimization: Extract only necessary metadata from TypeKind
        // to avoid cloning the full enum (which contains Arc pointers and is large).
        // This releases the borrow on self early.
        let task = {
            let type_info = self.get(ty);
            match &type_info.kind {
                TypeKind::Builtin(b) => LayoutTask::Builtin(*b),
                TypeKind::Pointer { .. } => LayoutTask::Pointer,
                TypeKind::Complex { base_type } => LayoutTask::Complex(*base_type),
                TypeKind::Array { element_type, size } => match size {
                    ArraySizeType::Constant(len) => LayoutTask::Array(*element_type, *len),
                    _ => LayoutTask::Unsupported("incomplete/VLA array layout"),
                },
                TypeKind::Function { .. } => LayoutTask::Function,
                TypeKind::Record {
                    members,
                    is_complete,
                    is_union,
                    packing,
                    alignment,
                    ..
                } => {
                    if !is_complete {
                        LayoutTask::Incomplete
                    } else {
                        LayoutTask::Record(Arc::clone(members), *is_union, *packing, *alignment)
                    }
                }
                TypeKind::Enum { base_type, .. } => LayoutTask::Enum(*base_type),
                TypeKind::Alias(inner) => LayoutTask::Alias(*inner),
                TypeKind::AutoType => LayoutTask::Unsupported("__auto_type layout"),
                TypeKind::TypeofExpr(_) => LayoutTask::Unsupported("typeof expr layout"),
                TypeKind::TypeofUnqualExpr(_) => LayoutTask::Unsupported("typeof_unqual expr layout"),
                TypeKind::NullptrT => LayoutTask::NullptrT,
                TypeKind::Error => LayoutTask::Unsupported("error layout"),
            }
        };

        let layout = match task {
            LayoutTask::Builtin(b) => match b {
                BuiltinType::Void => {
                    return Err(TypeRegistryError::SizeOfIncompleteType { ty });
                }
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
                        alignment: size as u16,
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
                BuiltinType::Signed => TypeLayout {
                    size: 4,
                    alignment: 4,
                    kind: LayoutKind::Scalar,
                },
                BuiltinType::VaList => TypeLayout {
                    size: 24,
                    alignment: 8,
                    kind: LayoutKind::RecordFields {
                        fields: Arc::from([
                            FieldLayout {
                                offset: 0,
                                bit_width: None,
                                bit_offset: None,
                                storage_size: 4,
                            },
                            FieldLayout {
                                offset: 4,
                                bit_width: None,
                                bit_offset: None,
                                storage_size: 4,
                            },
                            FieldLayout {
                                offset: 8,
                                bit_width: None,
                                bit_offset: None,
                                storage_size: 8,
                            },
                            FieldLayout {
                                offset: 16,
                                bit_width: None,
                                bit_offset: None,
                                storage_size: 8,
                            },
                        ]),
                    },
                },
                BuiltinType::Complex => {
                    return Err(TypeRegistryError::UnsupportedFeature {
                        feature: "Complex builtin type (marker only)",
                    });
                }
            },

            LayoutTask::Pointer => {
                let size = match self.target_triple.pointer_width() {
                    Ok(PointerWidth::U16) => 2,
                    Ok(PointerWidth::U32) => 4,
                    Ok(PointerWidth::U64) => 8,
                    Err(_) => 8,
                };
                TypeLayout {
                    size,
                    alignment: size as u16,
                    kind: LayoutKind::Scalar,
                }
            }

            LayoutTask::Complex(base_type) => {
                let base_layout = self.ensure_layout(base_type)?;
                TypeLayout {
                    size: base_layout.size * 2,
                    alignment: base_layout.alignment,
                    kind: LayoutKind::Scalar,
                }
            }

            LayoutTask::Array(element_type, len) => {
                let element_layout = self.ensure_layout(element_type)?;
                let total_size = element_layout.size * len as u64;
                TypeLayout {
                    size: total_size,
                    alignment: element_layout.alignment,
                    kind: LayoutKind::Array {
                        element: element_type,
                        len: len as u64,
                    },
                }
            }

            LayoutTask::Function => {
                return Err(TypeRegistryError::SizeOfFunctionType);
            }

            LayoutTask::Record(members, is_union, packing, alignment) => {
                self.compute_record_layout(&members, is_union, packing, alignment)?
            }

            LayoutTask::Enum(base_type) => self.ensure_layout(base_type)?.into_owned(),

            LayoutTask::Alias(inner) => self.ensure_layout(inner)?.into_owned(),
            LayoutTask::Incomplete => {
                return Err(TypeRegistryError::SizeOfIncompleteType { ty });
            }
            LayoutTask::Unsupported(feature) => {
                return Err(TypeRegistryError::UnsupportedFeature { feature });
            }
            LayoutTask::NullptrT => {
                let ptr_size = self.target_triple.pointer_width().unwrap().bytes() as u64;
                TypeLayout {
                    size: ptr_size,
                    alignment: ptr_size as u16,
                    kind: LayoutKind::Scalar,
                }
            }
        };

        Ok(layout)
    }

    fn compute_record_layout(
        &mut self,
        members: &[RecordMember],
        is_union: bool,
        packing: Option<u32>,
        alignment: Option<u16>,
    ) -> Result<TypeLayout, TypeRegistryError> {
        let mut max_align = alignment.unwrap_or(1);
        let mut current_size = 0;
        let mut field_layouts = Vec::with_capacity(members.len());

        let mut current_unit_offset: Option<u64> = None;
        let mut current_unit_bit_offset = 0;
        let mut current_unit_size = 0;
        // For C11 6.7.2.1p18 flexible array check:
        // "the last element of a structure with more than one named member may have an incomplete array type"
        // But incomplete array types are NOT allowed in unions.
        // We will check validity as we iterate.
        // Note: The count of members might include anonymous struct/union members which are technically members.

        let member_count = members.len();

        for (i, member) in members.iter().enumerate() {
            let member_ty = member.member_type.ty();

            if self.is_variably_modified(member_ty) {
                // C11 6.7.2.1p9: "A member of a structure or union shall not have a variably modified type."
                // This includes both direct VLAs, pointers to VLAs, and even variably-modified FAMs.
                return Err(TypeRegistryError::VlaAsStructMember);
            }

            // Special handling for flexible array member (FAM)
            // Need to check if it is incomplete array
            // We can't use is_complete because that recurses. We check TypeKind directly.
            // Bolt ⚡: Optimized to match on reference to avoid cloning ArraySizeType.
            let type_info = self.get(member_ty);
            if let TypeKind::Array { element_type, size } = &type_info.kind
                && matches!(size, ArraySizeType::Incomplete)
            {
                let elem_ty = *element_type;
                drop(type_info);
                if is_union {
                    // Incomplete types not allowed in union (FAM is only for structures)
                    return Err(TypeRegistryError::IncompleteArrayInUnion);
                }

                // Must be last member
                if i != member_count - 1 {
                    return Err(TypeRegistryError::FlexibleArrayNotLast);
                }

                // Must have at least one other named member.
                // Or rather, "structure with more than one named member".
                // If this is the only member, it's invalid.
                if member_count < 2 {
                    return Err(TypeRegistryError::FlexibleArrayInEmptyStruct);
                }

                // If valid FAM:
                // Size of structure is as if FAM was omitted.
                // But we must respect its alignment for the struct's alignment.
                // We need to get the element type to find alignment.
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
                let align_u64 = elem_layout.alignment as u64;
                let offset = (current_size + align_u64 - 1) & !(align_u64 - 1);
                field_layouts.push(FieldLayout {
                    offset,
                    bit_width: None,
                    bit_offset: None,
                    storage_size: 0, // FAM has no storage size in this context
                });

                // We do NOT update current_size with FAM size (which is effectively 0 or variable).
                // But we might update current_size to offset?
                // GCC: sizeof(struct { int x; int y[]; }) == 4.
                //      sizeof(struct { char c; int y[]; }) == 4 (aligned to 4).
                // So we do align current_size.
                current_size = offset;

                continue;
            }
            drop(type_info);

            let layout = match self.ensure_layout(member_ty) {
                Ok(l) => l,
                Err(e) => {
                    let new_e = match e {
                        TypeRegistryError::SizeOfIncompleteType { .. } => TypeRegistryError::IncompleteMemberType {
                            ty: QualType::unqualified(member_ty),
                        },
                        TypeRegistryError::SizeOfFunctionType => {
                            if let Some(name) = member.name {
                                TypeRegistryError::MemberHasFunctionType { name }
                            } else {
                                e
                            }
                        }
                        _ => e,
                    };
                    return Err(new_e);
                }
            };
            let mut member_align = layout.alignment;
            if member.is_packed {
                member_align = 1;
            }
            if let Some(req_align) = member.alignment {
                member_align = member_align.max(req_align);
            }
            if let Some(p) = packing {
                member_align = member_align.min(p as u16);
            }

            let is_unnamed_bitfield = member.name.is_none() && member.bit_field_size.is_some();

            if !is_unnamed_bitfield {
                max_align = max_align.max(member_align);
            }

            if is_union {
                // For unions with unnamed bitfields, compute size based on bits needed
                if let Some(bits) = member.bit_field_size {
                    let bytes_needed = ((bits as u64) + 7) >> 3;
                    current_size = current_size.max(bytes_needed);
                } else {
                    current_size = current_size.max(layout.size);
                }
                field_layouts.push(FieldLayout {
                    offset: 0,
                    bit_width: member.bit_field_size,
                    bit_offset: if member.bit_field_size.is_some() { Some(0) } else { None },
                    storage_size: layout.size,
                });
            } else if let Some(bits) = member.bit_field_size {
                if bits == 0 {
                    // Force alignment to next storage unit based on type's natural alignment
                    let natural_align = layout.alignment as u64;
                    current_size = (current_size + natural_align - 1) & !(natural_align - 1);
                    current_unit_offset = None;
                    current_unit_bit_offset = 0;
                    current_unit_size = 0;
                    field_layouts.push(FieldLayout {
                        offset: current_size,
                        bit_width: Some(0),
                        bit_offset: Some(0),
                        storage_size: layout.size,
                    });
                } else {
                    // For unnamed bit-fields, they don't affect alignment of subsequent members
                    // but they do take up some space in the struct

                    let can_cross_boundary = packing == Some(1);
                    let mut fits = false;
                    if let Some(unit_offset) = current_unit_offset {
                        let new_unit_size = current_unit_size.max(layout.size);
                        let align_mask = (member_align as u64) - 1;

                        // Rule: a bit-field must entirely reside in a storage unit of its type.
                        // This means it cannot cross a boundary of its alignment.
                        let mut bit_offset = current_unit_bit_offset;
                        // DEBUG
                        if bits > 0 {
                            // println!("DEBUG: bitfield size {} align {} offset {} unit_offset {}", bits, member_align, bit_offset, unit_offset);
                        }

                        let align_bits = (member_align as u64) * 8;
                        if !can_cross_boundary && bit_offset % align_bits != 0 {
                            let next_align = bit_offset.div_ceil(align_bits) * align_bits;
                            if bit_offset + (bits as u64) > next_align {
                                // Crosses boundary, must align
                                bit_offset = next_align;
                            }
                        }

                        if (unit_offset & align_mask) == 0
                            && (can_cross_boundary || bit_offset + (bits as u64) <= new_unit_size * 8)
                        {
                            fits = true;
                            let mut actual_bit_offset = bit_offset;
                            let mut actual_unit_offset = unit_offset;

                            if can_cross_boundary && actual_bit_offset >= 8 {
                                let bytes = actual_bit_offset / 8;
                                actual_unit_offset += bytes;
                                actual_bit_offset %= 8;
                            }

                            current_unit_offset = Some(actual_unit_offset);
                            current_unit_bit_offset = actual_bit_offset;
                            current_unit_size = new_unit_size;

                            let field_storage_size = if can_cross_boundary {
                                let bits_needed = actual_bit_offset + (bits as u64);
                                let mut s = 1;
                                while s < new_unit_size && (s * 8) < bits_needed {
                                    s *= 2;
                                }
                                s
                            } else {
                                new_unit_size
                            };

                            field_layouts.push(FieldLayout {
                                offset: actual_unit_offset,
                                bit_width: Some(bits),
                                bit_offset: Some(actual_bit_offset as u16),
                                storage_size: field_storage_size,
                            });

                            current_unit_bit_offset += bits as u64;

                            if can_cross_boundary {
                                current_size = current_size
                                    .max(actual_unit_offset + (actual_bit_offset + bits as u64).div_ceil(8));
                            } else {
                                current_size = current_size.max(actual_unit_offset + current_unit_size);
                            }
                        }
                    }

                    if !fits {
                        let align_u64 = member_align as u64;
                        let offset = (current_size + align_u64 - 1) & !(align_u64 - 1);

                        let field_storage_size = if can_cross_boundary {
                            let mut s = 1;
                            while s < layout.size && (s * 8) < (bits as u64) {
                                s *= 2;
                            }
                            s
                        } else {
                            layout.size
                        };

                        field_layouts.push(FieldLayout {
                            offset,
                            bit_width: Some(bits),
                            bit_offset: Some(0),
                            storage_size: field_storage_size,
                        });

                        if can_cross_boundary {
                            current_size = offset + (bits as u64).div_ceil(8);
                        } else {
                            current_size = offset + layout.size;
                        }

                        current_unit_offset = Some(offset);
                        current_unit_bit_offset = bits as u64;
                        current_unit_size = layout.size;
                    }
                }
            } else {
                // Not a bitfield, reset bitfield unit
                current_unit_offset = None;
                current_unit_bit_offset = 0;
                current_unit_size = 0;

                let align_u64 = member_align as u64;
                let offset = (current_size + align_u64 - 1) & !(align_u64 - 1);
                field_layouts.push(FieldLayout {
                    offset,
                    bit_width: None,
                    bit_offset: None,
                    storage_size: layout.size,
                });
                current_size = offset + layout.size;
            }
        }

        // Final size is padded to the record's max alignment
        let align_u64 = max_align as u64;
        let final_size = (current_size + align_u64 - 1) & !(align_u64 - 1);

        Ok(TypeLayout {
            size: final_size,
            alignment: max_align,
            kind: LayoutKind::RecordFields {
                fields: Arc::from(field_layouts),
            },
        })
    }

    pub(crate) fn decay(&mut self, qt: QualType, ptr_qualifiers: TypeQualifiers) -> QualType {
        let ty = qt.ty();

        // Bolt ⚡: Optimization: use fast-path helpers to check for array/function types.
        // This avoids expensive Cow<Type> allocations via self.get(ty) for every decay.
        if let Some(element_type) = self.get_array_element(ty) {
            // Correct logic: Array of T decays to Pointer to T.
            // Qualifiers on Array apply to the element in the resulting pointer type.
            let elem_qt = QualType::new(element_type, qt.qualifiers());
            let ptr = self.pointer_to(elem_qt);
            // Apply the extracted pointer qualifiers (e.g. from static/const inside [])
            return QualType::new(ptr, ptr_qualifiers);
        }

        if self.is_function_type(ty) {
            let ptr = self.pointer_to(qt);
            return QualType::new(ptr, ptr_qualifiers);
        }

        qt
    }

    pub(super) fn canonical_qual_type(&self, qt: QualType) -> QualType {
        let mut ty = qt.ty();

        // Bolt ⚡: Fast path for non-alias types.
        // Pointers, arrays, builtins, records, and enums are terminal types
        // that do not require an alias resolution loop.
        if ty.class() != crate::semantic::types::TypeClass::Alias {
            return qt;
        }

        // All inline types are non-alias terminal types, handled above.
        // Registry aliases can be recursive (typedef to another typedef).
        // Bolt ⚡: Match on reference to avoid cloning the large TypeKind enum.
        while let TypeKind::Alias(inner) = &self.types[ty.index()].kind {
            ty = *inner;
        }
        QualType::new(ty, qt.qualifiers())
    }

    pub(crate) fn is_compatible(&self, mut a: QualType, mut b: QualType) -> bool {
        // Bolt ⚡: Early exit for identical types before performing canonicalization.
        if a == b {
            return true;
        }

        a = self.canonical_qual_type(a);
        b = self.canonical_qual_type(b);

        if a == b {
            return true;
        }

        if a.qualifiers() != b.qualifiers() {
            return false;
        }

        let ty_a = a.ty();
        let ty_b = b.ty();

        if ty_a == ty_b {
            return true;
        }

        // nullptr_t is implicitly compatible with pointer types in standard contexts
        // (but strict type equivalence usually distinguishes them. We handle nullptr_t
        // implicitly converting to any pointer type in Analyzer)

        // Bolt ⚡: Fast path for pointers to avoid self.get() and Cow<Type> overhead.
        let pa = self.get_pointee(ty_a);
        let pb = self.get_pointee(ty_b);
        if pa.is_some() || pb.is_some() {
            return if let (Some(pa), Some(pb)) = (pa, pb) {
                self.is_compatible(pa, pb)
            } else {
                false
            };
        }

        // Bolt ⚡: Fast path for arrays to avoid self.get() and Cow<Type> overhead.
        let ea = self.get_array_element(ty_a);
        let eb = self.get_array_element(ty_b);
        if ea.is_some() || eb.is_some() {
            return if let (Some(ea), Some(eb)) = (ea, eb) {
                if !self.is_compatible(QualType::unqualified(ea), QualType::unqualified(eb)) {
                    return false;
                }

                // For array compatibility, we need to compare their sizes.
                // Inline arrays are always constant size; registry arrays can be complex.
                let sa = if ty_a.is_inline_array() {
                    ArraySizeType::Constant(ty_a.array_len().unwrap() as usize)
                } else {
                    match &self.types[ty_a.index()].kind {
                        TypeKind::Array { size, .. } => *size,
                        _ => unreachable!(),
                    }
                };

                let sb = if ty_b.is_inline_array() {
                    ArraySizeType::Constant(ty_b.array_len().unwrap() as usize)
                } else {
                    match &self.types[ty_b.index()].kind {
                        TypeKind::Array { size, .. } => *size,
                        _ => unreachable!(),
                    }
                };

                match (sa, sb) {
                    (ArraySizeType::Incomplete, _) => true,
                    (_, ArraySizeType::Incomplete) => true,
                    (ArraySizeType::Constant(sa_val), ArraySizeType::Constant(sb_val)) => sa_val == sb_val,
                    (ArraySizeType::Star, _) => true,
                    (_, ArraySizeType::Star) => true,
                    (ArraySizeType::Variable(_), _) => true,
                    (_, ArraySizeType::Variable(_)) => true,
                }
            } else {
                false
            };
        }

        // Bolt ⚡: Optimized handle for enums using direct registry access.
        // C11 6.7.2.2p4: "Each enumerated type shall be compatible with ... an integer type."
        // GCC and many other compilers are permissive with enum compatibility, especially
        // regarding signedness of the underlying type. We allow an enum to be compatible
        // with any integer type of the same size.
        // However, different enum types are NOT compatible with each other (non-transitivity).
        if ty_a.is_enum() {
            return !ty_b.is_enum() && b.is_integer() && self.get_layout(ty_a).size == self.get_layout(ty_b).size;
        }
        if ty_b.is_enum() {
            return !ty_a.is_enum() && a.is_integer() && self.get_layout(ty_a).size == self.get_layout(ty_b).size;
        }

        // Fallback for registry-only types (Functions, Records).
        // Since these are never inline, self.get() returns Cow::Borrowed which is cheap.
        let type_a = self.get(ty_a);
        let type_b = self.get(ty_b);

        match (&type_a.kind, &type_b.kind) {
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
                if !self.is_compatible(QualType::unqualified(*ret_a), QualType::unqualified(*ret_b)) {
                    return false;
                }
                if params_a.len() != params_b.len() {
                    return false;
                }
                for (p_a, p_b) in params_a.iter().zip(params_b.iter()) {
                    // Ignore top-level qualifiers on parameters (C11 6.7.6.3p15)
                    // Note: strip_for_parameter() preserves _Atomic.
                    let type_a = p_a.param_type.strip_for_parameter();
                    let type_b = p_b.param_type.strip_for_parameter();
                    if !self.is_compatible(type_a, type_b) {
                        return false;
                    }
                }
                true
            }
            _ => false,
        }
    }

    pub(super) fn composite_type(&mut self, a: QualType, b: QualType) -> Option<QualType> {
        if a == b {
            return Some(a);
        }

        if a.qualifiers() != b.qualifiers() {
            return None;
        }

        if a.ty() == b.ty() {
            return Some(a);
        }

        let ty_a = a.ty();
        let ty_b = b.ty();

        // Bolt ⚡: Fast path for pointers.
        if let (Some(pa), Some(pb)) = (self.get_pointee(ty_a), self.get_pointee(ty_b)) {
            return self.composite_pointer_type(a, pa, pb);
        }

        // Bolt ⚡: Fast path for arrays.
        if let (Some(ea), Some(eb)) = (self.get_array_element(ty_a), self.get_array_element(ty_b)) {
            return self.composite_array_type(a, ty_a, ty_b, ea, eb);
        }

        // Fallback for registry-only types (Functions, Records, Enums).
        let type_a = self.get(ty_a);
        let type_b = self.get(ty_b);

        match (&type_a.kind, &type_b.kind) {
            (TypeKind::Function { .. }, TypeKind::Function { .. }) => {
                let type_a = type_a.into_owned();
                let type_b = type_b.into_owned();
                self.composite_function_type(a, &type_a, &type_b)
            }
            _ => {
                if self.is_compatible(a, b) {
                    Some(a)
                } else {
                    None
                }
            }
        }
    }

    fn composite_pointer_type(&mut self, a: QualType, pa: QualType, pb: QualType) -> Option<QualType> {
        let composite_pointee = self.composite_type(pa, pb)?;
        let res_ty = self.pointer_to(composite_pointee);
        Some(QualType::new(res_ty, a.qualifiers()))
    }

    fn composite_array_type(
        &mut self,
        a: QualType,
        ty_a: TypeRef,
        ty_b: TypeRef,
        ea: TypeRef,
        eb: TypeRef,
    ) -> Option<QualType> {
        let composite_elem = self.composite_type(QualType::unqualified(ea), QualType::unqualified(eb))?;

        let sa = if ty_a.is_inline_array() {
            ArraySizeType::Constant(ty_a.array_len().unwrap() as usize)
        } else {
            match &self.types[ty_a.index()].kind {
                TypeKind::Array { size, .. } => *size,
                _ => unreachable!(),
            }
        };

        let sb = if ty_b.is_inline_array() {
            ArraySizeType::Constant(ty_b.array_len().unwrap() as usize)
        } else {
            match &self.types[ty_b.index()].kind {
                TypeKind::Array { size, .. } => *size,
                _ => unreachable!(),
            }
        };

        let composite_size = match (sa, sb) {
            (ArraySizeType::Incomplete, s) => s,
            (s, ArraySizeType::Incomplete) => s,
            (ArraySizeType::Constant(sa), ArraySizeType::Constant(sb)) if sa == sb => ArraySizeType::Constant(sa),
            (ArraySizeType::Star, s) => s,
            (s, ArraySizeType::Star) => s,
            _ => return None,
        };

        let res_ty = self.array_of(composite_elem.ty(), composite_size);
        Some(QualType::new(res_ty, a.qualifiers()))
    }

    fn composite_function_type(&mut self, a: QualType, type_a: &Type, type_b: &Type) -> Option<QualType> {
        let (ret_a, params_a, var_a, noreturn_a) = match &type_a.kind {
            TypeKind::Function {
                return_type,
                parameters,
                is_variadic,
                is_noreturn,
            } => (*return_type, parameters, *is_variadic, *is_noreturn),
            _ => unreachable!(),
        };
        let (ret_b, params_b, var_b, noreturn_b) = match &type_b.kind {
            TypeKind::Function {
                return_type,
                parameters,
                is_variadic,
                is_noreturn,
            } => (*return_type, parameters, *is_variadic, *is_noreturn),
            _ => unreachable!(),
        };

        if var_a != var_b {
            return None;
        }

        let composite_ret = self.composite_type(QualType::unqualified(ret_a), QualType::unqualified(ret_b))?;
        if params_a.len() != params_b.len() {
            return None;
        }

        let mut composite_params = Vec::with_capacity(params_a.len());
        for (p_a, p_b) in params_a.iter().zip(params_b.iter()) {
            // C11 6.7.6.3p15: strip qualifiers for compatibility check
            let type_a = p_a.param_type.strip_for_parameter();
            let type_b = p_b.param_type.strip_for_parameter();
            let cp = self.composite_type(type_a, type_b)?;

            composite_params.push(FunctionParam {
                param_type: cp,
                name: p_b.name.or(p_a.name),
                storage: p_b.storage.or(p_a.storage),
            });
        }

        let res_ty = self.function_type(composite_ret.ty(), composite_params, var_a, noreturn_a || noreturn_b);
        Some(QualType::new(res_ty, a.qualifiers()))
    }

    pub(crate) fn is_complete(&self, mut ty: TypeRef) -> bool {
        loop {
            // Bolt ⚡: Use TypeClass for fast dispatch to avoid redundant bitfield decoding.
            // This optimization reduces analysis time by providing early exits for common complete types.
            match ty.class() {
                TypeClass::Pointer => return true,
                TypeClass::Array => {
                    if ty.array_len().is_some() {
                        return true;
                    }
                    if let TypeKind::Array { element_type, size } = &self.types[ty.index()].kind {
                        if matches!(size, ArraySizeType::Incomplete) {
                            return false;
                        }
                        ty = *element_type;
                    } else {
                        return true;
                    }
                }
                TypeClass::Builtin => {
                    if let Some(b) = BuiltinType::from_u32(ty.base()) {
                        return b != BuiltinType::Void;
                    }
                    // Handle NullptrT which is also TypeClass::Builtin but not in BuiltinType enum.
                    return match &self.types[ty.index()].kind {
                        TypeKind::NullptrT => true,
                        TypeKind::Builtin(BuiltinType::Void) => false,
                        _ => true,
                    };
                }
                TypeClass::Record | TypeClass::Enum => {
                    return match &self.types[ty.index()].kind {
                        TypeKind::Record { is_complete, .. } | TypeKind::Enum { is_complete, .. } => *is_complete,
                        _ => true,
                    };
                }
                TypeClass::Alias => {
                    if let TypeKind::Alias(inner) = &self.types[ty.index()].kind {
                        ty = *inner;
                    } else {
                        return true;
                    }
                }
                _ => return true,
            }
        }
    }

    pub(super) fn is_const_recursive(&self, mut qt: QualType) -> bool {
        loop {
            if qt.is_const() {
                return true;
            }

            let ty = qt.ty();
            // Pointers only have recursive constness if the pointer itself is const (handled above).
            if ty.is_pointer() {
                return false;
            }

            if ty.is_inline_array() {
                qt = QualType::unqualified(self.reconstruct_element(ty));
                continue;
            }

            // Builtins (that aren't aliases) don't have recursive constness.
            if ty.builtin().is_some() {
                return false;
            }

            // Bolt ⚡: Direct registry access avoids Cow<Type> allocations.
            match &self.types[ty.index()].kind {
                TypeKind::Alias(inner) => {
                    qt = QualType::new(*inner, qt.qualifiers());
                }
                TypeKind::Record { members, .. } => {
                    return members.iter().any(|m| self.is_const_recursive(m.member_type));
                }
                TypeKind::Array { element_type, .. } => {
                    qt = QualType::unqualified(*element_type);
                }
                _ => return false,
            }
        }
    }

    pub(crate) fn is_variably_modified(&self, mut ty: TypeRef) -> bool {
        loop {
            // Bolt ⚡: Use TypeClass for fast dispatch to avoid redundant bitfield decoding.
            // This optimization reduces analysis time by early-exiting for types that are never variably modified.
            match ty.class() {
                TypeClass::Builtin | TypeClass::Enum | TypeClass::Record => return false,
                TypeClass::Pointer => {
                    if ty.is_inline_pointer() {
                        ty = self.reconstruct_pointee(ty);
                    } else if let TypeKind::Pointer { pointee } = &self.types[ty.index()].kind {
                        ty = pointee.ty();
                    } else {
                        return false;
                    }
                }
                TypeClass::Array => {
                    if ty.is_inline_array() {
                        ty = self.reconstruct_element(ty);
                    } else if let TypeKind::Array { element_type, size } = &self.types[ty.index()].kind {
                        if matches!(size, ArraySizeType::Variable(_)) {
                            return true;
                        }
                        ty = *element_type;
                    } else {
                        return false;
                    }
                }
                TypeClass::Complex => {
                    if let TypeKind::Complex { base_type } = &self.types[ty.index()].kind {
                        ty = *base_type;
                    } else {
                        return false;
                    }
                }
                TypeClass::Function => {
                    if let TypeKind::Function {
                        return_type,
                        parameters,
                        ..
                    } = &self.types[ty.index()].kind
                    {
                        if self.is_variably_modified(*return_type) {
                            return true;
                        }
                        return parameters.iter().any(|p| self.is_variably_modified(p.param_type.ty()));
                    }
                    return false;
                }
                TypeClass::Alias => {
                    if let TypeKind::Alias(inner) = &self.types[ty.index()].kind {
                        ty = *inner;
                    } else {
                        return false;
                    }
                }
            }
        }
    }

    /// Returns true if the type is directly a variable length array type.
    /// Unlike `is_variably_modified`, this does NOT recurse through pointers —
    /// a pointer to a VLA is variably modified but is NOT itself a VLA type.
    /// This distinction matters for C11 6.5.2.5p1 (compound literals).
    pub(crate) fn is_vla_type(&self, mut ty: TypeRef) -> bool {
        loop {
            if ty.is_inline_pointer() || ty.builtin().is_some() {
                return false;
            }
            if ty.is_inline_array() {
                ty = self.reconstruct_element(ty);
                continue;
            }
            match &self.types[ty.index()].kind {
                TypeKind::Alias(inner) => ty = *inner,
                TypeKind::Array { element_type, size } => {
                    if matches!(size, ArraySizeType::Variable(_)) {
                        return true;
                    }
                    ty = *element_type;
                }
                _ => return false,
            }
        }
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
            _ => format!("{}", type_kind),
        }
    }
}

// ================================================================
// Helper types
// ================================================================

/// Internal task used to extract information from TypeKind without cloning it.
enum LayoutTask {
    Builtin(BuiltinType),
    Pointer,
    Array(TypeRef, usize),
    Complex(TypeRef),
    Function,
    Record(Arc<[RecordMember]>, bool, Option<u32>, Option<u16>),
    Enum(TypeRef),
    Alias(TypeRef),
    Incomplete,
    NullptrT,
    Unsupported(&'static str),
}

/// Key for canonicalizing function types.
/// Bolt ⚡: Uses SmallVec to avoid heap allocations during function type lookups.
/// Most C functions have <= 8 parameters, allowing the key to remain on the stack.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct FnSigKey {
    return_type: TypeRef,
    params: SmallVec<[QualType; 8]>,
    is_variadic: bool,
    is_noreturn: bool,
}
