use hashbrown::HashMap;
use serde::Serialize;
use smallvec::SmallVec;
use std::sync::{OnceLock, RwLock};

use crate::semantic::{TypeRef, TypeRegistry};

const TAG_SHIFT: u64 = 61;
const PAYLOAD_MASK: u64 = (1u64 << TAG_SHIFT) - 1;

const TAG_INT: u64 = 0;
const TAG_BOOL: u64 = 1;
const TAG_NULLPTR: u64 = 2;
const TAG_CHAR: u64 = 3;
const TAG_SMALL_STR: u64 = 4;
const TAG_FLOAT32: u64 = 5;
const TAG_INTERNED: u64 = 7;

const INT_VALUE_BITS: u64 = 48;
const INT_VALUE_MASK: u64 = (1u64 << INT_VALUE_BITS) - 1;
const INT_MIN_SMALL: i64 = -(1i64 << (INT_VALUE_BITS - 1));
const INT_MAX_SMALL: i64 = (1i64 << (INT_VALUE_BITS - 1)) - 1;
const INT_SUFFIX_SHIFT: u64 = 48;
const INT_RADIX_SHIFT: u64 = 52;
const INT_RADIX_MASK: u64 = 0x3F;

const CHAR_PREFIX_SHIFT: u64 = 32;
const CHAR_VAL_MASK: u64 = 0xFFFF_FFFF;

const STR_MAX_SMALL_LEN: usize = 6;
const STR_LEN_SHIFT: u64 = 58;
const STR_LEN_MASK: u64 = 0x7;
const STR_PREFIX_SHIFT: u64 = 55;
const STR_PREFIX_MASK: u64 = 0x7;

const FLOAT32_VAL_MASK: u64 = 0xFFFF_FFFF;
const FLOAT_SUFFIX_SHIFT: u64 = 32;

const INTERN_KIND_SHIFT: u64 = 58;
const INTERN_KIND_MASK: u64 = 0x7;
const INTERN_INDEX_MASK: u64 = (1u64 << 58) - 1;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
#[repr(u8)]
#[allow(clippy::upper_case_acronyms)]
pub enum IntSuffix {
    None = 0,
    L = 1,
    LL = 2,
    U = 3,
    UL = 4,
    ULL = 5,
}

impl IntSuffix {
    fn from_u8(v: u8) -> Self {
        match v {
            1 => Self::L,
            2 => Self::LL,
            3 => Self::U,
            4 => Self::UL,
            5 => Self::ULL,
            _ => Self::None,
        }
    }

    pub(crate) fn get_candidates(self, registry: &TypeRegistry, is_decimal: bool) -> SmallVec<[TypeRef; 6]> {
        match self {
            IntSuffix::None => {
                if is_decimal {
                    SmallVec::from_slice(&[registry.type_int, registry.type_long, registry.type_long_long])
                } else {
                    SmallVec::from_slice(&[
                        registry.type_int,
                        registry.type_int_unsigned,
                        registry.type_long,
                        registry.type_long_unsigned,
                        registry.type_long_long,
                        registry.type_long_long_unsigned,
                    ])
                }
            }
            IntSuffix::U => SmallVec::from_slice(&[
                registry.type_int_unsigned,
                registry.type_long_unsigned,
                registry.type_long_long_unsigned,
            ]),
            IntSuffix::L => {
                if is_decimal {
                    SmallVec::from_slice(&[registry.type_long, registry.type_long_long])
                } else {
                    SmallVec::from_slice(&[
                        registry.type_long,
                        registry.type_long_unsigned,
                        registry.type_long_long,
                        registry.type_long_long_unsigned,
                    ])
                }
            }
            IntSuffix::UL => SmallVec::from_slice(&[registry.type_long_unsigned, registry.type_long_long_unsigned]),
            IntSuffix::LL => {
                if is_decimal {
                    SmallVec::from_slice(&[registry.type_long_long])
                } else {
                    SmallVec::from_slice(&[registry.type_long_long, registry.type_long_long_unsigned])
                }
            }
            IntSuffix::ULL => SmallVec::from_slice(&[registry.type_long_long_unsigned]),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
#[repr(u8)]
#[allow(clippy::upper_case_acronyms)]
pub enum FloatSuffix {
    None = 0,
    F = 1,
    L = 2,
    I = 3,
    IF = 4,
    IL = 5,
}

impl FloatSuffix {
    fn from_u8(v: u8) -> Self {
        match v {
            1 => Self::F,
            2 => Self::L,
            3 => Self::I,
            4 => Self::IF,
            5 => Self::IL,
            _ => Self::None,
        }
    }

    pub(crate) fn get_type(self, registry: &TypeRegistry) -> TypeRef {
        match self {
            Self::F => registry.type_float,
            Self::IF => registry.type_complex_float,
            Self::L => registry.type_long_double,
            Self::IL => registry.type_complex_long_double,
            Self::I => registry.type_complex_double,
            _ => registry.type_double,
        }
    }

    pub(crate) fn is_imaginary(self) -> bool {
        matches!(self, Self::I | Self::IF | Self::IL)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
#[repr(u8)]
pub enum StrPrefix {
    None = 0,
    Wide = 1,
    Utf16 = 2,
    Utf32 = 3,
    Utf8 = 4,
}

impl StrPrefix {
    fn from_u8(v: u8) -> Self {
        match v {
            1 => Self::Wide,
            2 => Self::Utf16,
            3 => Self::Utf32,
            4 => Self::Utf8,
            _ => Self::None,
        }
    }

    pub(crate) fn from_str(s: &str) -> Self {
        match s {
            "u8" => Self::Utf8,
            "L" => Self::Wide,
            "u" => Self::Utf16,
            "U" => Self::Utf32,
            _ => Self::None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
#[repr(u8)]
pub enum CharPrefix {
    None = 0,
    Wide = 1,
    Char16 = 2,
    Char32 = 3,
    Utf8 = 4,
}

impl CharPrefix {
    fn from_u8(v: u8) -> Self {
        match v {
            1 => Self::Wide,
            2 => Self::Char16,
            3 => Self::Char32,
            4 => Self::Utf8,
            _ => Self::None,
        }
    }

    pub(crate) fn get_type(self, registry: &TypeRegistry) -> TypeRef {
        match self {
            CharPrefix::Utf8 => registry.type_char_unsigned,
            CharPrefix::Wide => registry.type_signed, // wchar_t is signed i32 usually
            CharPrefix::Char16 => registry.type_short_unsigned,
            CharPrefix::Char32 => registry.type_int_unsigned,
            CharPrefix::None => registry.type_int,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
#[repr(u8)]
pub enum LitKind {
    Int = 0,
    Float = 1,
    Char = 2,
    String = 3,
    Bool = 4,
    Nullptr = 5,
}

impl LitKind {
    fn from_u8(v: u8) -> Self {
        match v {
            1 => Self::Float,
            2 => Self::Char,
            3 => Self::String,
            4 => Self::Bool,
            5 => Self::Nullptr,
            _ => Self::Int,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
pub enum LitVal {
    Int { value: i64, suffix: IntSuffix, radix: u8 },
    Float { bits: u64, suffix: FloatSuffix },
    Char(u32, CharPrefix),
    String { value: Vec<u8>, prefix: StrPrefix },
    Nullptr,
    True,
    False,
}

impl LitVal {
    pub(crate) fn from_f64(val: f64, suffix: FloatSuffix) -> Self {
        Self::Float {
            bits: val.to_bits(),
            suffix,
        }
    }

    pub(crate) fn as_f64(&self) -> f64 {
        match self {
            Self::Float { bits, .. } => f64::from_bits(*bits),
            _ => panic!("Not a float literal"),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
#[repr(transparent)]
pub struct StringLitRef(LitRef);

impl StringLitRef {
    pub fn new(lit: LitRef) -> Self {
        assert_eq!(lit.kind(), LitKind::String);
        Self(lit)
    }

    pub fn get_val(self) -> (Vec<u8>, StrPrefix) {
        if let LitVal::String { value, prefix } = self.0.get_val() {
            (value, prefix)
        } else {
            unreachable!("StringLitRef must contain a string literal")
        }
    }

    pub(crate) fn from_bytes<'a>(s: std::borrow::Cow<'a, [u8]>, prefix: StrPrefix) -> Self {
        let bytes = s.as_ref();
        if bytes.len() <= STR_MAX_SMALL_LEN && bytes.is_ascii() {
            let mut packed = 0u64;
            for (i, b) in bytes.iter().enumerate() {
                packed |= (*b as u64) << (i * 8);
            }
            let payload = packed | ((prefix as u64) << STR_PREFIX_SHIFT) | ((bytes.len() as u64) << STR_LEN_SHIFT);
            Self(LitRef((TAG_SMALL_STR << TAG_SHIFT) | payload))
        } else {
            Self(LitRef::intern(LitVal::String {
                value: s.into_owned(),
                prefix,
            }))
        }
    }
}

impl From<StringLitRef> for LitRef {
    #[inline]
    fn from(val: StringLitRef) -> Self {
        val.0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
#[repr(transparent)]
pub struct LitRef(u64);

impl LitRef {
    pub const NULLPTR: Self = Self(TAG_NULLPTR << TAG_SHIFT);
    pub const TRUE: Self = Self((TAG_BOOL << TAG_SHIFT) | 1);
    pub const FALSE: Self = Self(TAG_BOOL << TAG_SHIFT);

    #[inline]
    fn tag(self) -> u64 {
        self.0 >> TAG_SHIFT
    }

    #[inline]
    fn payload(self) -> u64 {
        self.0 & PAYLOAD_MASK
    }

    pub(crate) fn from_int(value: i64, suffix: IntSuffix, radix: u8) -> Self {
        if (INT_MIN_SMALL..=INT_MAX_SMALL).contains(&value) {
            let payload = ((value as u64) & INT_VALUE_MASK)
                | ((suffix as u64) << INT_SUFFIX_SHIFT)
                | (((radix as u64) & INT_RADIX_MASK) << INT_RADIX_SHIFT);
            Self((TAG_INT << TAG_SHIFT) | payload)
        } else {
            Self::intern(LitVal::Int { value, suffix, radix })
        }
    }

    pub(crate) fn from_char(ch: u32, prefix: CharPrefix) -> Self {
        Self((TAG_CHAR << TAG_SHIFT) | ch as u64 | ((prefix as u64) << CHAR_PREFIX_SHIFT))
    }

    /// Returns true if the literal is an integer-compatible zero (0, nullptr, false, '\0').
    /// Bolt ⚡: Optimized zero-check that avoids intern table lookups and locks for most literals.
    /// Note: Does NOT return true for 0.0, as float literals are not null pointer constants.
    #[inline]
    pub(crate) fn is_integer_zero(self) -> bool {
        match self.tag() {
            TAG_INT => (self.payload() & INT_VALUE_MASK) == 0,
            TAG_BOOL => self.payload() == 0,
            TAG_NULLPTR => true,
            TAG_CHAR => (self.payload() & CHAR_VAL_MASK) == 0,
            TAG_FLOAT32 => false,
            TAG_SMALL_STR => false,
            TAG_INTERNED => false, // 0 and '\0' are always represented as small literals.
            _ => false,
        }
    }

    pub(crate) fn from_f64(value: f64, suffix: FloatSuffix) -> Self {
        match suffix {
            FloatSuffix::F => {
                let bits = (value as f32).to_bits() as u64;
                Self((TAG_FLOAT32 << TAG_SHIFT) | bits | ((suffix as u64) << FLOAT_SUFFIX_SHIFT))
            }
            _ => Self::intern(LitVal::from_f64(value, suffix)),
        }
    }

    pub(crate) fn get_val(self) -> LitVal {
        match self.tag() {
            TAG_INT => {
                let p = self.payload();
                let raw = p & INT_VALUE_MASK;
                // Sign-extend from 48 bits
                let value = ((raw << (64 - INT_VALUE_BITS)) as i64) >> (64 - INT_VALUE_BITS);
                let suffix = IntSuffix::from_u8(((p >> INT_SUFFIX_SHIFT) & 0xF) as u8);
                let radix = ((p >> INT_RADIX_SHIFT) & INT_RADIX_MASK) as u8;
                LitVal::Int { value, suffix, radix }
            }
            TAG_BOOL => {
                if self.payload() != 0 {
                    LitVal::True
                } else {
                    LitVal::False
                }
            }
            TAG_NULLPTR => LitVal::Nullptr,
            TAG_CHAR => {
                let p = self.payload();
                LitVal::Char(
                    (p & CHAR_VAL_MASK) as u32,
                    CharPrefix::from_u8(((p >> CHAR_PREFIX_SHIFT) & 0xFF) as u8),
                )
            }
            TAG_SMALL_STR => {
                let p = self.payload();
                let len = ((p >> STR_LEN_SHIFT) & STR_LEN_MASK) as usize;
                let prefix = StrPrefix::from_u8(((p >> STR_PREFIX_SHIFT) & STR_PREFIX_MASK) as u8);
                let mut bytes = Vec::with_capacity(len);
                for i in 0..len {
                    bytes.push(((p >> (i * 8)) & 0xFF) as u8);
                }
                LitVal::String { value: bytes, prefix }
            }
            TAG_FLOAT32 => {
                let p = self.payload();
                let bits = (p & FLOAT32_VAL_MASK) as u32;
                let suffix = FloatSuffix::from_u8(((p >> FLOAT_SUFFIX_SHIFT) & 0xF) as u8);
                LitVal::from_f64(f32::from_bits(bits) as f64, suffix)
            }
            TAG_INTERNED => self.with_val(|v| v.clone()),
            _ => unreachable!(),
        }
    }

    /// Access the literal value without always cloning (for interned values).
    /// Bolt ⚡: Optimization: providing direct access to the global literal table via a closure
    /// avoids expensive clones of large string literals in the hot path.
    pub(crate) fn with_val<R>(self, f: impl FnOnce(&LitVal) -> R) -> R {
        if self.tag() == TAG_INTERNED {
            let id = (self.payload() & INTERN_INDEX_MASK) as u32;
            let table = global_literal_table().read().unwrap();
            f(table.get(id))
        } else {
            f(&self.get_val())
        }
    }

    /// Retrieve metadata about a string literal without full value retrieval.
    /// Bolt ⚡: Optimization: metadata-only access avoids heap allocations and RwLock
    /// overhead for small literals, and avoids String clones for interned ones.
    pub(crate) fn get_string_metadata(self) -> Option<(usize, StrPrefix)> {
        match self.tag() {
            TAG_SMALL_STR => {
                let p = self.payload();
                let len = ((p >> STR_LEN_SHIFT) & STR_LEN_MASK) as usize;
                let prefix = StrPrefix::from_u8(((p >> STR_PREFIX_SHIFT) & STR_PREFIX_MASK) as u8);
                Some((len + 1, prefix))
            }
            TAG_INTERNED => self.with_val(|val| {
                if let LitVal::String { value, prefix } = val {
                    Some((get_string_literal_size(value.as_slice(), *prefix), *prefix))
                } else {
                    None
                }
            }),
            _ => None,
        }
    }

    /// intern LitVal into global literal table
    fn intern(val: LitVal) -> Self {
        let kind = match &val {
            LitVal::Int { .. } => LitKind::Int,
            LitVal::Float { .. } => LitKind::Float,
            LitVal::Char(..) => LitKind::Char,
            LitVal::String { .. } => LitKind::String,
            LitVal::True | LitVal::False => LitKind::Bool,
            LitVal::Nullptr => LitKind::Nullptr,
        };

        let id = global_literal_table().write().unwrap().insert(val);
        Self((TAG_INTERNED << TAG_SHIFT) | ((kind as u64) << INTERN_KIND_SHIFT) | (id as u64 & INTERN_INDEX_MASK))
    }

    #[inline]
    pub(crate) fn kind(self) -> LitKind {
        match self.tag() {
            TAG_INT => LitKind::Int,
            TAG_BOOL => LitKind::Bool,
            TAG_NULLPTR => LitKind::Nullptr,
            TAG_CHAR => LitKind::Char,
            TAG_SMALL_STR => LitKind::String,
            TAG_FLOAT32 => LitKind::Float,
            TAG_INTERNED => LitKind::from_u8(((self.payload() >> INTERN_KIND_SHIFT) & INTERN_KIND_MASK) as u8),
            _ => unreachable!(),
        }
    }
}

/// Calculate the number of elements in the string literal, including the null terminator.
/// Bolt ⚡: Optimized metadata-only calculation to avoid full literal lowering.
/// Standard string literals (None/Utf8) provide O(1) size via content.len().
pub fn get_string_literal_size(content: &[u8], prefix: StrPrefix) -> usize {
    match prefix {
        StrPrefix::None | StrPrefix::Utf8 => content.len() + 1,
        StrPrefix::Wide | StrPrefix::Utf32 => String::from_utf8_lossy(content).chars().count() + 1,
        StrPrefix::Utf16 => {
            let mut len = 0;
            let s = String::from_utf8_lossy(content);
            for c in s.chars() {
                len += c.len_utf16();
            }
            len + 1
        }
    }
}

#[derive(Default)]
pub struct LiteralTable {
    values: Vec<LitVal>,
    map: HashMap<LitVal, u32>,
}

impl LiteralTable {
    fn insert(&mut self, val: LitVal) -> u32 {
        if let Some(&id) = self.map.get(&val) {
            return id;
        }
        let id = self.values.len() as u32;
        self.values.push(val.clone());
        self.map.insert(val, id);
        id
    }

    pub(crate) fn get(&self, id: u32) -> &LitVal {
        &self.values[id as usize]
    }
}

static LITERAL_TABLE: OnceLock<RwLock<LiteralTable>> = OnceLock::new();

fn global_literal_table() -> &'static RwLock<LiteralTable> {
    LITERAL_TABLE.get_or_init(|| RwLock::new(LiteralTable::default()))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_intern_and_get_int() {
        // intern must have same value
        let lit1 = LitRef::from_int(1234567, IntSuffix::None, 10);
        let lit2 = LitRef::from_int(1234567, IntSuffix::None, 10);
        assert_eq!(lit1, lit2);
        assert_eq!(lit1.get_val(), lit2.get_val());
    }

    #[test]
    fn test_intern_and_get_float() {
        let lit1 = LitRef::from_f64(1234567.0, FloatSuffix::None);
        let lit2 = LitRef::from_f64(1234567.0, FloatSuffix::None);
        assert_eq!(lit1, lit2);
        assert_eq!(lit1.get_val(), lit2.get_val());
    }

    #[test]
    fn test_literal_coverage() {
        // Test FloatSuffix::from_u8 missing arms
        assert_eq!(FloatSuffix::from_u8(1), FloatSuffix::F);
        assert_eq!(FloatSuffix::from_u8(2), FloatSuffix::L);
        assert_eq!(FloatSuffix::from_u8(3), FloatSuffix::I);
        assert_eq!(FloatSuffix::from_u8(4), FloatSuffix::IF);
        assert_eq!(FloatSuffix::from_u8(5), FloatSuffix::IL);
        assert_eq!(FloatSuffix::from_u8(99), FloatSuffix::None);

        // Test CharPrefix::from_u8 missing arms
        assert_eq!(CharPrefix::from_u8(1), CharPrefix::Wide);
        assert_eq!(CharPrefix::from_u8(2), CharPrefix::Char16);
        assert_eq!(CharPrefix::from_u8(3), CharPrefix::Char32);
        assert_eq!(CharPrefix::from_u8(4), CharPrefix::Utf8);
        assert_eq!(CharPrefix::from_u8(99), CharPrefix::None);

        // Test is_imaginary
        assert!(FloatSuffix::I.is_imaginary());
        assert!(FloatSuffix::IF.is_imaginary());
        assert!(FloatSuffix::IL.is_imaginary());
        assert!(!FloatSuffix::F.is_imaginary());

        // Test LitRef::is_integer_zero for NULLPTR
        let null_lit = LitRef::NULLPTR;
        assert!(null_lit.is_integer_zero());
    }
}
