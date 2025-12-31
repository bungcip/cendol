use super::{Declarator, NameId};

/// Extract identifier from a declarator (helper function)
pub fn extract_identifier(declarator: &Declarator) -> Option<NameId> {
    match declarator {
        Declarator::Identifier(name, _) => Some(*name),
        Declarator::Pointer(_, next) => next.as_ref().and_then(|d| extract_identifier(d)),
        Declarator::Array(base, _) => extract_identifier(base),
        Declarator::Function { inner, .. } => extract_identifier(inner),
        Declarator::BitField(base, _) => extract_identifier(base),
        _ => None,
    }
}
