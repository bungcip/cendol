use crate::ast::StringId;
use crate::lang_options::LangOptions;
use crate::pp::PPToken;
use crate::pp::pp_lexer::PPTokenKind;
use crate::source_manager::SourceManager;
use crate::source_manager::{SourceId, SourceLoc};
use chrono::{DateTime, Utc};
use rustc_hash::FxHashMap;
use smallvec::SmallVec;
use std::path::PathBuf;
use std::sync::Arc;
use target_lexicon::Triple;

// Packed boolean flags for macro properties
bitflags::bitflags! {
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Default)]
    pub struct MacroFlags: u8 {
        const FUNCTION_LIKE = 1 << 0;
        const C99_VARARGS = 1 << 1;
        const GNU_VARARGS = 1 << 2;
        const BUILTIN = 1 << 3;
        const DISABLED = 1 << 4;
        const USED = 1 << 5;
        const HAS_VA_OPT = 1 << 6;
    }
}

/// Interned table of hide sets for Dave Prosser's macro expansion algorithm
#[derive(Debug, Clone)]
pub(crate) struct HideSetTable {
    pub(crate) sets: Vec<Arc<[StringId]>>,
    pub(crate) map: FxHashMap<Arc<[StringId]>, u32>,
    pub(crate) intersection_cache: FxHashMap<(u32, u32), u32>,
    pub(crate) insert_cache: FxHashMap<(u32, StringId), u32>,
}

impl Default for HideSetTable {
    fn default() -> Self {
        Self::new()
    }
}

impl HideSetTable {
    pub(super) fn new() -> Self {
        // Index 0 is the empty hide set
        let empty: Arc<[StringId]> = Arc::from([]);
        let mut map = FxHashMap::default();
        map.insert(empty.clone(), 0);
        Self {
            sets: vec![empty],
            map,
            intersection_cache: FxHashMap::default(),
            insert_cache: FxHashMap::default(),
        }
    }
    pub(crate) fn intern(&mut self, set: SmallVec<[StringId; 4]>) -> u32 {
        if set.is_empty() {
            return 0;
        }

        // Bolt ⚡: Perform a zero-allocation lookup first to avoid creating an Arc on cache hits.
        if let Some(&id) = self.map.get(set.as_slice()) {
            return id;
        }

        // Bolt ⚡: Instantiate Arc directly from the slice to avoid a redundant Vec heap allocation.
        let arc_set: Arc<[StringId]> = Arc::from(set.as_slice());
        let id = self.sets.len() as u32;
        self.sets.push(arc_set.clone());
        self.map.insert(arc_set, id);
        id
    }

    pub(super) fn intersection(&mut self, id1: u32, id2: u32) -> u32 {
        if id1 == 0 || id2 == 0 {
            return 0;
        }
        if id1 == id2 {
            return id1;
        }

        // Bolt ⚡: Check cache first to avoid merge and interning overhead.
        let key = if id1 < id2 { (id1, id2) } else { (id2, id1) };
        if let Some(&res) = self.intersection_cache.get(&key) {
            return res;
        }

        let set1 = &self.sets[id1 as usize];
        let set2 = &self.sets[id2 as usize];

        // Optimized merge-based intersection for sorted sets: O(M+K)
        let mut result = SmallVec::<[StringId; 4]>::new();
        let (mut i, mut j) = (0, 0);
        while i < set1.len() && j < set2.len() {
            match set1[i].cmp(&set2[j]) {
                std::cmp::Ordering::Equal => {
                    result.push(set1[i]);
                    i += 1;
                    j += 1;
                }
                std::cmp::Ordering::Less => i += 1,
                std::cmp::Ordering::Greater => j += 1,
            }
        }

        let res = self.intern(result);
        self.intersection_cache.insert(key, res);
        res
    }

    pub(super) fn insert(&mut self, id: u32, symbol: StringId) -> u32 {
        // Bolt ⚡: Check cache first.
        if let Some(&res) = self.insert_cache.get(&(id, symbol)) {
            return res;
        }

        let existing = &self.sets[id as usize];
        let res = match existing.binary_search(&symbol) {
            Ok(_) => id,
            Err(pos) => {
                let mut new_set = SmallVec::<[StringId; 4]>::new();
                new_set.extend_from_slice(&existing[..pos]);
                new_set.push(symbol);
                new_set.extend_from_slice(&existing[pos..]);
                self.intern(new_set)
            }
        };

        self.insert_cache.insert((id, symbol), res);
        res
    }

    pub(super) fn contains(&self, id: u32, symbol: StringId) -> bool {
        if id == 0 {
            return false;
        }
        self.sets[id as usize].binary_search(&symbol).is_ok()
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) struct MacroParam {
    pub(crate) name: StringId,
    pub(crate) needs_expansion: bool,
}

impl MacroParam {
    pub(crate) fn new(name: StringId) -> Self {
        Self {
            name,
            needs_expansion: false,
        }
    }
}

/// Represents a macro definition
#[derive(Clone, Default)]
pub(crate) struct MacroInfo {
    pub(crate) location: SourceLoc,
    pub(crate) flags: MacroFlags, // Packed boolean flags
    pub(crate) tokens: Arc<[PPToken]>,
    parameters: Arc<[MacroParam]>,
    variadic_arg: Option<MacroParam>,
}

impl MacroInfo {
    pub(crate) fn is_identical_signature(&self, other: &MacroInfo) -> bool {
        self.parameters
            .iter()
            .map(|p| p.name)
            .eq(other.parameters.iter().map(|p| p.name))
            && self.variadic_arg.map(|p| p.name) == other.variadic_arg.map(|p| p.name)
    }

    pub(crate) fn is_identical_definition(&self, other: &MacroInfo, sm: &SourceManager) -> bool {
        let identity_flags_mask = MacroFlags::FUNCTION_LIKE | MacroFlags::C99_VARARGS | MacroFlags::GNU_VARARGS;
        if (self.flags & identity_flags_mask) != (other.flags & identity_flags_mask) {
            return false;
        }
        if !self.is_identical_signature(other) {
            return false;
        }
        if self.tokens.len() != other.tokens.len() {
            return false;
        }

        self.tokens.iter().zip(other.tokens.iter()).all(|(a, b)| {
            if a.kind != b.kind {
                return false;
            }
            match a.kind {
                PPTokenKind::Identifier(_) => true,
                PPTokenKind::Number | PPTokenKind::StringLiteral | PPTokenKind::CharLiteral(_) => {
                    a.get_text(sm) == b.get_text(sm)
                }
                _ => true,
            }
        })
    }

    pub(crate) fn with_parameters(mut self, parameters: Arc<[MacroParam]>, variadic_arg: Option<MacroParam>) -> Self {
        self.parameters = parameters;
        self.variadic_arg = variadic_arg;
        self
    }

    pub(crate) fn with_location(mut self, location: SourceLoc) -> Self {
        self.location = location;
        self
    }

    pub(crate) fn with_flags(mut self, flags: MacroFlags) -> Self {
        self.flags = flags;
        self
    }

    pub(crate) fn with_tokens(mut self, tokens: Arc<[PPToken]>) -> Self {
        self.tokens = tokens;
        self
    }

    pub(crate) fn param_len(&self) -> usize {
        self.parameters.len()
    }

    pub(crate) fn has_variadic(&self) -> bool {
        self.variadic_arg.is_some()
    }

    pub(crate) fn is_variadic_param(&self, symbol: StringId) -> bool {
        self.variadic_arg.is_some_and(|p| p.name == symbol)
    }

    /// Checks if a parameter token at index `i` is subject to stringification (#) or token pasting (##).
    /// If so, the C standard dictates it should NOT be macro-expanded prior to substitution.
    pub(crate) fn param_needs_expansion(tokens: &[PPToken], i: usize) -> bool {
        let preceded_by_hash = i > 0 && tokens[i - 1].kind == PPTokenKind::Hash;
        let preceded_by_hashhash = i > 0 && tokens[i - 1].kind == PPTokenKind::HashHash;
        let followed_by_hashhash = i + 1 < tokens.len() && tokens[i + 1].kind == PPTokenKind::HashHash;
        !preceded_by_hash && !preceded_by_hashhash && !followed_by_hashhash
    }

    /// Pre-calculates whether parameters need expansion based on # and ## operators.
    /// Also detects the presence of __VA_OPT__ and returns true if found.
    pub(crate) fn precalculate_expansion_needs(
        tokens: &[PPToken],
        parameters: &mut [MacroParam],
        variadic_arg: &mut Option<MacroParam>,
        va_opt_sym: StringId,
    ) -> bool {
        let mut has_va_opt = false;
        for i in 0..tokens.len() {
            let t = &tokens[i];
            if let PPTokenKind::Identifier(sym) = t.kind {
                // Check for __VA_OPT__
                if variadic_arg.is_some() && sym == va_opt_sym {
                    has_va_opt = true;
                }

                // Match parameter
                let mut matched_param = parameters.iter_mut().find(|p| p.name == sym);
                if matched_param.is_none() && variadic_arg.as_ref().is_some_and(|p| p.name == sym) {
                    matched_param = variadic_arg.as_mut();
                }

                if let Some(param) = matched_param
                    && Self::param_needs_expansion(tokens, i)
                {
                    param.needs_expansion = true;
                }
            }
        }
        has_va_opt
    }

    pub(crate) fn get_param_idx(&self, symbol: StringId) -> Option<usize> {
        if let Some(idx) = self.parameters.iter().position(|p| p.name == symbol) {
            Some(idx)
        } else if self.is_variadic_param(symbol) {
            Some(self.parameters.len())
        } else {
            None
        }
    }

    pub(crate) fn get_param(&self, idx: usize) -> Option<&MacroParam> {
        self.parameters.get(idx).or_else(|| {
            if idx >= self.parameters.len() && self.variadic_arg.is_some() {
                self.variadic_arg.as_ref()
            } else {
                None
            }
        })
    }

    pub(crate) fn is_valid_arg_count(&self, count: usize) -> bool {
        let expected = self.parameters.len();
        if self.variadic_arg.is_some() {
            count >= expected
        } else {
            count == expected
        }
    }
}

/// Represents conditional compilation state
#[derive(Debug, Clone)]
pub(crate) struct PPConditionalInfo {
    pub(crate) was_skipping: bool,
    pub(crate) found_else: bool,
    pub(crate) found_non_skipping: bool,
}

/// Include stack information
#[derive(Clone)]
pub(crate) struct IncludeStackInfo {
    pub(crate) file_id: SourceId,
}

/// Configuration for preprocessor
#[derive(Debug, Clone)]
pub struct PPConfig {
    pub(crate) max_include_depth: usize,
    pub(crate) system_include_paths: Vec<PathBuf>,
    pub(crate) quoted_include_paths: Vec<PathBuf>,
    pub(crate) angled_include_paths: Vec<PathBuf>,
    pub(crate) framework_paths: Vec<PathBuf>,
    pub(crate) target: Triple,
    pub(crate) current_time: Option<DateTime<Utc>>,
    pub(crate) lang_options: LangOptions,
}

impl Default for PPConfig {
    fn default() -> Self {
        Self {
            max_include_depth: 200,
            system_include_paths: Vec::new(),
            quoted_include_paths: Vec::new(),
            angled_include_paths: Vec::new(),
            framework_paths: Vec::new(),
            target: Triple::host(),
            current_time: None,
            lang_options: LangOptions::default(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::StringId;

    #[test]
    fn test_hidesettable_methods() {
        let mut table = HideSetTable::default();
        let id_a = StringId::new("a");
        let id_b = StringId::new("b");
        let id_c = StringId::new("c");

        let id1 = table.intern(smallvec::smallvec![id_a]);

        let inserted = table.insert(id1, id_b);
        let inserted_hit = table.insert(id1, id_b); // cache hit
        assert_eq!(inserted, inserted_hit);

        let intersected = table.intersection(inserted, id1);
        let intersected_hit = table.intersection(inserted, id1); // cache hit
        assert_eq!(intersected, intersected_hit);

        let intersect_zero1 = table.intersection(0, id1);
        let intersect_zero2 = table.intersection(id1, 0);
        let intersect_same = table.intersection(id1, id1);

        assert_eq!(intersect_zero1, 0);
        assert_eq!(intersect_zero2, 0);
        assert_eq!(intersect_same, id1);

        // Complex case
        let id12 = table.intern(smallvec::smallvec![id_a, id_b]);
        let id13 = table.intern(smallvec::smallvec![id_a, id_c]);
        assert_eq!(table.intersection(id13, id12), id1);
    }
}
