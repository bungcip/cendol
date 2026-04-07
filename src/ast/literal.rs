use crate::ast::NameId;
use crate::semantic::{TypeRef, TypeRegistry};
use serde::Serialize;
use smallvec::SmallVec;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
#[repr(u8)]
#[allow(clippy::upper_case_acronyms)]
pub enum IntegerSuffix {
    L,
    LL,
    U,
    UL,
    ULL,
}

impl IntegerSuffix {
    pub(crate) fn get_candidates(
        suffix: Option<Self>,
        registry: &TypeRegistry,
        is_decimal: bool,
    ) -> SmallVec<[TypeRef; 6]> {
        match suffix {
            None => {
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
            Some(IntegerSuffix::U) => SmallVec::from_slice(&[
                registry.type_int_unsigned,
                registry.type_long_unsigned,
                registry.type_long_long_unsigned,
            ]),
            Some(IntegerSuffix::L) => {
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
            Some(IntegerSuffix::UL) => {
                SmallVec::from_slice(&[registry.type_long_unsigned, registry.type_long_long_unsigned])
            }
            Some(IntegerSuffix::LL) => {
                if is_decimal {
                    SmallVec::from_slice(&[registry.type_long_long])
                } else {
                    SmallVec::from_slice(&[registry.type_long_long, registry.type_long_long_unsigned])
                }
            }
            Some(IntegerSuffix::ULL) => SmallVec::from_slice(&[registry.type_long_long_unsigned]),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
#[repr(u8)]
pub enum FloatSuffix {
    F,
    L,
    I,
    IF,
    IL,
}

impl FloatSuffix {
    pub(crate) fn get_type(suffix: Option<Self>, registry: &TypeRegistry) -> TypeRef {
        match suffix {
            Some(FloatSuffix::F) => registry.type_float,
            Some(FloatSuffix::L) => registry.type_long_double,
            Some(FloatSuffix::I) => registry.type_complex_double,
            Some(FloatSuffix::IF) => registry.type_complex_float,
            Some(FloatSuffix::IL) => registry.type_complex_long_double,
            None => registry.type_double,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
#[repr(u8)]
pub enum CharPrefix {
    None,
    Wide,
    Char16,
    Char32,
    Utf8,
}

impl CharPrefix {
    pub(crate) fn get_type(&self, registry: &TypeRegistry) -> TypeRef {
        match self {
            CharPrefix::Utf8 => registry.type_char_unsigned,
            CharPrefix::Wide => registry.type_int,
            CharPrefix::Char16 => registry.type_short_unsigned,
            CharPrefix::Char32 => registry.type_int_unsigned,
            CharPrefix::None => registry.type_int,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Serialize)]
pub enum Literal {
    Int {
        val: i64,
        suffix: Option<IntegerSuffix>,
        base: u32,
    },
    Float {
        val: f64,
        suffix: Option<FloatSuffix>,
    },
    Char(u64, CharPrefix),
    String(NameId),
    Nullptr,
    True,
    False,
}
