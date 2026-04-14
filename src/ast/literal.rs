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

use hashbrown::HashMap;
use std::num::NonZeroU32;

#[derive(Debug, Clone, Copy, PartialEq, Serialize, Hash, Eq)]
pub struct LitRef(NonZeroU32);

impl LitRef {
    pub(crate) fn new(id: u32) -> Self {
        Self(NonZeroU32::new(id).unwrap())
    }

    pub(crate) fn get(&self) -> u32 {
        self.0.get()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Serialize, Hash, Eq)]
pub enum LitVal {
    Int {
        val: i64,
        suffix: Option<IntegerSuffix>,
        radix: u8,
    },
    Float {
        val: u64, // Store f64 bits for Hash/Eq compatibility
        suffix: Option<FloatSuffix>,
    },
    Char(u64, CharPrefix),
    String(NameId),
    Nullptr,
    True,
    False,
}

impl LitVal {
    pub(crate) fn from_f64(val: f64, suffix: Option<FloatSuffix>) -> Self {
        Self::Float {
            val: val.to_bits(),
            suffix,
        }
    }

    pub(crate) fn as_f64(&self) -> f64 {
        match self {
            Self::Float { val, .. } => f64::from_bits(*val),
            _ => panic!("Not a float literal"),
        }
    }
}

#[derive(Debug, Clone, Serialize, Default)]
pub struct LiteralTable {
    pub values: Vec<LitVal>,
    #[serde(skip)]
    pub map: HashMap<LitVal, LitRef>,
}

impl LiteralTable {
    pub fn insert(&mut self, val: LitVal) -> LitRef {
        if let Some(&id) = self.map.get(&val) {
            return id;
        }

        let id = LitRef::new(self.values.len() as u32 + 1);
        self.values.push(val);
        self.map.insert(val, id);
        id
    }

    pub fn get(&self, lit: LitRef) -> &LitVal {
        &self.values[(lit.get() - 1) as usize]
    }
}
