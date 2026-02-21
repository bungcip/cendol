use crate::ast::NameId;
use serde::Serialize;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
#[repr(u8)]
pub enum IntegerSuffix {
    L,
    LL,
    U,
    UL,
    ULL,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
#[repr(u8)]
pub enum FloatSuffix {
    F,
    L,
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
    Char(u64),
    String(NameId),
}
