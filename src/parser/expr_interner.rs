use std::num::NonZeroU32;
use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt;
use std::rc::Rc;
use std::sync::{OnceLock, RwLock};
use thin_vec::ThinVec;

use crate::parser::ast::Expr;

thread_local! {
    static THREAD_EXPR_TABLE: RefCell<ExprTable> = RefCell::new(ExprTable::new());
}
struct ExprTable {
    table: Vec<Expr>
}


impl ExprTable {
    pub fn new() -> Self {
        ExprTable {
            table: Vec::new(),
        }
    }
}


#[derive(PartialEq, Eq, Debug, Hash, Copy, Clone)]
#[repr(transparent)]
pub struct ExprId(NonZeroU32);

impl ExprId {
    /// get cloned expr from interned expr
    pub fn get(&self) -> Expr {
        THREAD_EXPR_TABLE.with_borrow(|tbl|{
            let index = self.0.get() - 1;
            tbl.table[index as usize].clone()
        })
    }
}


pub struct ExprInterner;

impl ExprInterner {
    pub fn intern(expr: Expr) -> ExprId {
        THREAD_EXPR_TABLE.with(|tbl|{
            let mut t = tbl.borrow_mut();
            t.table.push(expr);
            let index = t.table.len() + 1;
            let index = unsafe {
                // SAFETY: +1 on table length
                NonZeroU32::new_unchecked(index as u32)
            };
            ExprId(index)
        })
    }
}
