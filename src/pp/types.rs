use crate::ast::StringId;
use crate::lang_options::CStandard;
use crate::pp::pp_lexer::PPToken;
use crate::source_manager::{SourceId, SourceLoc};
use chrono::{DateTime, Utc};
use hashbrown::HashMap;
use smallvec::SmallVec;
use std::path::PathBuf;
use std::sync::Arc;
use target_lexicon::Triple;

/// Preprocessor directive kinds
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DirectiveKind {
    Define,
    Undef,
    Include,
    IncludeNext,
    If,
    Ifdef,
    Ifndef,
    Elif,
    Else,
    Endif,
    Line,
    Pragma,
    Error,
    Warning,
}

/// Table of pre-interned preprocessor directive names for O(1) keyword recognition
#[derive(Clone)]
pub(crate) struct DirectiveKeywordTable {
    pub(crate) define: StringId,
    pub(crate) undef: StringId,
    pub(crate) include: StringId,
    pub(crate) include_next: StringId,
    pub(crate) if_: StringId,
    pub(crate) ifdef: StringId,
    pub(crate) ifndef: StringId,
    pub(crate) elif: StringId,
    pub(crate) else_: StringId,
    pub(crate) endif: StringId,
    pub(crate) line: StringId,
    pub(crate) pragma: StringId,
    pub(crate) error: StringId,
    pub(crate) warning: StringId,
    pub(crate) defined: StringId, // For the defined operator in expressions
    pub(crate) has_include: StringId,
    pub(crate) has_include_next: StringId,
    pub(crate) has_builtin: StringId,
    pub(crate) has_attribute: StringId,
    pub(crate) has_feature: StringId,
    pub(crate) has_extension: StringId,
    pub(crate) line_macro: StringId,
    pub(crate) file_macro: StringId,
    pub(crate) counter_macro: StringId,
    pub(crate) pragma_operator: StringId,
}

impl Default for DirectiveKeywordTable {
    fn default() -> Self {
        Self::new()
    }
}

impl DirectiveKeywordTable {
    pub(crate) fn new() -> Self {
        DirectiveKeywordTable {
            define: StringId::new("define"),
            undef: StringId::new("undef"),
            include: StringId::new("include"),
            include_next: StringId::new("include_next"),
            if_: StringId::new("if"),
            ifdef: StringId::new("ifdef"),
            ifndef: StringId::new("ifndef"),
            elif: StringId::new("elif"),
            else_: StringId::new("else"),
            endif: StringId::new("endif"),
            line: StringId::new("line"),
            pragma: StringId::new("pragma"),
            error: StringId::new("error"),
            warning: StringId::new("warning"),
            defined: StringId::new("defined"),
            has_include: StringId::new("__has_include"),
            has_include_next: StringId::new("__has_include_next"),
            has_builtin: StringId::new("__has_builtin"),
            has_attribute: StringId::new("__has_attribute"),
            has_feature: StringId::new("__has_feature"),
            has_extension: StringId::new("__has_extension"),
            line_macro: StringId::new("__LINE__"),
            file_macro: StringId::new("__FILE__"),
            counter_macro: StringId::new("__COUNTER__"),
            pragma_operator: StringId::new("_Pragma"),
        }
    }

    pub(crate) fn is_directive(&self, symbol: StringId) -> Option<DirectiveKind> {
        if symbol == self.define {
            Some(DirectiveKind::Define)
        } else if symbol == self.undef {
            Some(DirectiveKind::Undef)
        } else if symbol == self.include {
            Some(DirectiveKind::Include)
        } else if symbol == self.include_next {
            Some(DirectiveKind::IncludeNext)
        } else if symbol == self.if_ {
            Some(DirectiveKind::If)
        } else if symbol == self.ifdef {
            Some(DirectiveKind::Ifdef)
        } else if symbol == self.ifndef {
            Some(DirectiveKind::Ifndef)
        } else if symbol == self.elif {
            Some(DirectiveKind::Elif)
        } else if symbol == self.else_ {
            Some(DirectiveKind::Else)
        } else if symbol == self.endif {
            Some(DirectiveKind::Endif)
        } else if symbol == self.line {
            Some(DirectiveKind::Line)
        } else if symbol == self.pragma {
            Some(DirectiveKind::Pragma)
        } else if symbol == self.error {
            Some(DirectiveKind::Error)
        } else if symbol == self.warning {
            Some(DirectiveKind::Warning)
        } else {
            None
        }
    }

    /// Get the interned symbol for the "defined" operator
    pub(crate) fn defined_symbol(&self) -> StringId {
        self.defined
    }

    /// Get the interned symbol for the "__has_include" operator
    pub(crate) fn has_include_symbol(&self) -> StringId {
        self.has_include
    }

    /// Get the interned symbol for the "__has_include_next" operator
    pub(crate) fn has_include_next_symbol(&self) -> StringId {
        self.has_include_next
    }

    /// Get the interned symbol for the "__has_builtin" operator
    pub(crate) fn has_builtin_symbol(&self) -> StringId {
        self.has_builtin
    }

    /// Get the interned symbol for the "__has_attribute" operator
    pub(crate) fn has_attribute_symbol(&self) -> StringId {
        self.has_attribute
    }

    /// Get the interned symbol for the "__has_feature" operator
    pub(crate) fn has_feature_symbol(&self) -> StringId {
        self.has_feature
    }

    /// Get the interned symbol for the "__has_extension" operator
    pub(crate) fn has_extension_symbol(&self) -> StringId {
        self.has_extension
    }
}

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
    }
}

/// Interned table of hide sets for Dave Prosser's macro expansion algorithm
#[derive(Debug, Clone)]
pub(crate) struct HideSetTable {
    pub(crate) sets: Vec<Arc<[StringId]>>,
    pub(crate) map: HashMap<Arc<[StringId]>, u32>,
}

impl Default for HideSetTable {
    fn default() -> Self {
        Self::new()
    }
}

impl HideSetTable {
    pub(crate) fn new() -> Self {
        // Index 0 is the empty hide set
        let empty: Arc<[StringId]> = Arc::from([]);
        let mut map = HashMap::new();
        map.insert(empty.clone(), 0);
        Self { sets: vec![empty], map }
    }

    pub(crate) fn intern(&mut self, mut set: SmallVec<[StringId; 4]>) -> u32 {
        if set.is_empty() {
            return 0;
        }
        set.sort();
        set.dedup();

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

    pub(crate) fn intersection(&mut self, id1: u32, id2: u32) -> u32 {
        if id1 == 0 || id2 == 0 {
            return 0;
        }
        if id1 == id2 {
            return id1;
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

        self.intern(result)
    }

    pub(crate) fn union(&mut self, id1: u32, id2: u32) -> u32 {
        if id1 == 0 {
            return id2;
        }
        if id2 == 0 {
            return id1;
        }
        if id1 == id2 {
            return id1;
        }
        let set1 = &self.sets[id1 as usize];
        let set2 = &self.sets[id2 as usize];

        // Optimized merge-based union for sorted sets: O(M+K)
        let mut result = SmallVec::<[StringId; 4]>::new();
        let (mut i, mut j) = (0, 0);
        while i < set1.len() && j < set2.len() {
            match set1[i].cmp(&set2[j]) {
                std::cmp::Ordering::Equal => {
                    result.push(set1[i]);
                    i += 1;
                    j += 1;
                }
                std::cmp::Ordering::Less => {
                    result.push(set1[i]);
                    i += 1;
                }
                std::cmp::Ordering::Greater => {
                    result.push(set2[j]);
                    j += 1;
                }
            }
        }
        result.extend_from_slice(&set1[i..]);
        result.extend_from_slice(&set2[j..]);

        self.intern(result)
    }

    pub(crate) fn insert(&mut self, id: u32, symbol: StringId) -> u32 {
        let existing = &self.sets[id as usize];
        if existing.binary_search(&symbol).is_ok() {
            return id;
        }
        let mut new_set = SmallVec::<[StringId; 4]>::new();
        new_set.extend_from_slice(existing);
        new_set.push(symbol);
        // Note: intern will sort it
        self.intern(new_set)
    }

    pub(crate) fn contains(&self, id: u32, symbol: StringId) -> bool {
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
    pub max_include_depth: usize,
    pub system_include_paths: Vec<PathBuf>,
    pub quoted_include_paths: Vec<PathBuf>,
    pub angled_include_paths: Vec<PathBuf>,
    pub framework_paths: Vec<PathBuf>,
    pub c_standard: CStandard,
    pub target: Triple,
    pub current_time: Option<DateTime<Utc>>,
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
        }
    }
}
