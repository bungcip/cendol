use symbol_table::GlobalSymbol;

pub type StringId = GlobalSymbol;

pub struct StringInterner;

impl StringInterner {
    /// Interns a string, returning a StringId.
    /// If the string is already interned, returns the existing StringId.
    /// Otherwise, inserts it and returns a new StringId.
    pub fn intern(s: &str) -> StringId {
        //self.table.intern(s)
        GlobalSymbol::new(s)
    }

    pub fn empty_id() -> StringId {
        Self::intern("")
    }
}
