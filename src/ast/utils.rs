use super::{Declarator, Symbol};

/// Extract identifier from a declarator (helper function)
pub fn extract_identifier(declarator: &Declarator) -> Option<Symbol> {
    match declarator {
        Declarator::Identifier(name, _, _) => Some(*name),
        Declarator::Pointer(_, next) => next.as_ref().and_then(|d| extract_identifier(d)),
        Declarator::Array(base, _) => extract_identifier(base),
        Declarator::Function(base, _) => extract_identifier(base),
        Declarator::BitField(base, _) => extract_identifier(base),
        _ => None,
    }
}
