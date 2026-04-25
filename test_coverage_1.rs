#[cfg(test)]
mod tests {
    use crate::semantic::type_registry::*;
    use crate::semantic::types::*;
    use std::borrow::Cow;
    use std::sync::Arc;

    #[test]
    fn test_to_semantic_kind() {
        use crate::semantic::errors::SemanticError;
        let err = TypeRegistryError::RecursiveType { ty: TypeRef::dummy() };
        assert!(matches!(err.to_semantic_kind(), SemanticError::RecursiveType { ty } if ty == TypeRef::dummy()));
        let err2 = TypeRegistryError::SizeOfIncompleteType { ty: TypeRef::dummy() };
        assert!(matches!(err2.to_semantic_kind(), SemanticError::SizeOfIncompleteType { ty } if ty == TypeRef::dummy()));
    }
}
