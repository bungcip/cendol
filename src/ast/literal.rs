use crate::ast::NameId;
use serde::Serialize;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
pub enum IntegerSuffix {
    L,
    LL,
    U,
    UL,
    ULL,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
pub enum FloatSuffix {
    F,
    L,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub enum Literal {
    Int {
        val: i64,
        suffix: Option<IntegerSuffix>,
    },
    Float {
        val: f64,
        suffix: Option<FloatSuffix>,
    },
    Char(u8),
    String(NameId),
}
