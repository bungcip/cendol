use crate::ast::StringId;
use crate::lang_options::CStandard;
use crate::pp::pp_lexer::{PPToken, PPTokenKind};
use crate::source_manager::{SourceId, SourceLoc};
use chrono::{DateTime, Utc};
use hashbrown::HashMap;
use smallvec::SmallVec;
use std::path::PathBuf;
use std::sync::Arc;
use target_lexicon::Triple;

// Packed boolean flags for macro properties
bitflags::bitflags! {
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
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
    pub(crate) map: HashMap<Arc<[StringId]>, u32>,
    pub(crate) intersection_cache: HashMap<(u32, u32), u32>,
    pub(crate) insert_cache: HashMap<(u32, StringId), u32>,
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
        let mut map = HashMap::new();
        map.insert(empty.clone(), 0);
        Self {
            sets: vec![empty],
            map,
            intersection_cache: HashMap::new(),
            insert_cache: HashMap::new(),
        }
    }

    #[cfg(test)]
    pub(crate) fn intern(&mut self, mut set: SmallVec<[StringId; 4]>) -> u32 {
        if set.is_empty() {
            return 0;
        }
        set.sort();
        set.dedup();
        self.intern_canonical(set)
    }

    fn intern_canonical(&mut self, set: SmallVec<[StringId; 4]>) -> u32 {
        if set.is_empty() {
            return 0;
        }

        // Bolt ⚡: Perform a zero-allocation lookup first to avoid creating an Arc on cache hits.
        if let Some(&id) = self.map.get(set.as_slice()) {
            return id;
        }

        let arc_set: Arc<[StringId]> = Arc::from(set.into_vec());
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

        let res = self.intern_canonical(result);
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
                self.intern_canonical(new_set)
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

/// Represents a macro definition
#[derive(Clone)]
pub(crate) struct MacroInfo {
    pub(crate) location: SourceLoc,
    pub(crate) flags: MacroFlags, // Packed boolean flags
    pub(crate) tokens: Arc<[PPToken]>,
    pub(crate) parameter_list: Arc<[StringId]>,
    pub(crate) variadic_arg: Option<StringId>,
    /// Bolt ⚡: Pre-calculated map indicating if a parameter needs expansion.
    /// This avoids O(N*M) body scans during every expansion.
    pub(crate) parameter_needs_expansion: Arc<[bool]>,
}

impl MacroInfo {
    /// Bolt ⚡: Pre-calculate which parameters need expansion (prescan).
    /// A parameter needs expansion if it's used in the body without being stringified (#) or pasted (##).
    pub(crate) fn calculate_expansion_needs(
        tokens: &[PPToken],
        params: &[StringId],
        variadic: Option<StringId>,
    ) -> Arc<[bool]> {
        let mut needs_expansion = Vec::with_capacity(params.len() + variadic.is_some() as usize);

        for &param_sym in params {
            needs_expansion.push(Self::check_param_needs_expansion(tokens, param_sym));
        }

        if let Some(v_sym) = variadic {
            needs_expansion.push(Self::check_param_needs_expansion(tokens, v_sym));
        }

        Arc::from(needs_expansion)
    }

    fn check_param_needs_expansion(tokens: &[PPToken], param_sym: StringId) -> bool {
        for i in 0..tokens.len() {
            if let PPTokenKind::Identifier(sym) = tokens[i].kind
                && sym == param_sym
            {
                let preceded_by_hash = i > 0 && tokens[i - 1].kind == PPTokenKind::Hash;
                let preceded_by_hashhash = i > 0 && tokens[i - 1].kind == PPTokenKind::HashHash;
                let followed_by_hashhash = i + 1 < tokens.len() && tokens[i + 1].kind == PPTokenKind::HashHash;

                if !preceded_by_hash && !preceded_by_hashhash && !followed_by_hashhash {
                    return true;
                }
            }
        }
        false
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
    pub(crate) c_standard: CStandard,
    pub(crate) target: Triple,
    pub(crate) current_time: Option<DateTime<Utc>>,
    pub(crate) pedantic: bool,
    pub(crate) pedantic_errors: bool,
}

impl Default for PPConfig {
    fn default() -> Self {
        Self {
            max_include_depth: 200,
            system_include_paths: Vec::new(),
            quoted_include_paths: Vec::new(),
            angled_include_paths: Vec::new(),
            framework_paths: Vec::new(),
            c_standard: CStandard::default(),
            target: Triple::host(),
            current_time: None,
            pedantic: false,
            pedantic_errors: false,
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
