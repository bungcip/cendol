use std::cell::RefCell;
use thin_vec::ThinVec;
use std::num::NonZeroU32;

use crate::parser::ast::Expr;
use crate::types::ArrayExprListId;

thread_local! {
    static THREAD_ARRAY_TABLE: RefCell<ArrayExprTable> = RefCell::new(ArrayExprTable::new());
}

struct ArrayExprTable {
    table: Vec<ThinVec<Expr>>
}

impl ArrayExprTable {
    pub fn new() -> Self {
        ArrayExprTable {
            table: Vec::new(),
        }
    }
}

pub struct ArrayExprListInterner;

impl ArrayExprListInterner {
    pub fn intern(array_exprs: ThinVec<Expr>) -> ArrayExprListId {
        THREAD_ARRAY_TABLE.with(|tbl|{
            let mut t = tbl.borrow_mut();
            t.table.push(array_exprs);
            let index = t.table.len();
            let index = unsafe {
                // SAFETY: index is > 0 since we pushed an element
                NonZeroU32::new_unchecked(index as u32)
            };
            index
        })
    }

    pub fn get(id: ArrayExprListId) -> ThinVec<Expr> {
        THREAD_ARRAY_TABLE.with(|tbl| {
            let t = tbl.borrow();
            t.table[id.get() as usize - 1].clone()
        })
    }
}