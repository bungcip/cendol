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

#[derive(Debug, Clone, PartialEq, Serialize)]
pub enum Literal {
    Int {
        val: i64,
        suffix: Option<IntegerSuffix>,
    },
    Float(f64),
    Char(u8),
    String(NameId),
}
