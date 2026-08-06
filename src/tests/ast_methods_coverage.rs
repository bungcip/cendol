#[cfg(test)]
mod tests {
    use crate::ast::literal::{LitRef, StrPrefix, StringLitRef};
    use crate::ast::{Ast, NodeKind, NodeRef, SemanticInfo, ValueCategory};
    use crate::semantic::types::{QualType, TypeClass, TypeRef};
    use crate::source_manager::SourceSpan;

    #[test]
    fn test_ast_setters_and_getters() {
        let mut ast = Ast::new();
        let node = ast.push_dummy(SourceSpan::empty());

        ast.set_kind(node, NodeKind::Break);
        assert!(matches!(ast.get_kind(node), NodeKind::Break));

        let span2 = SourceSpan::empty();
        ast.set_span(node, span2);

        let mut sem_info = SemanticInfo::default();
        let ty_ref = TypeRef::new(1, TypeClass::Builtin, 0, 0).unwrap();
        let ty = QualType::unqualified(ty_ref);

        // Ensure vector is large enough
        sem_info.types.resize(node.index() + 1, None);
        sem_info.types[node.index()] = Some(ty);

        sem_info
            .value_categories
            .resize(node.index() + 1, ValueCategory::RValue);
        sem_info.value_categories[node.index()] = ValueCategory::LValue;

        // Generic selection
        sem_info.generic_selections.insert(node.index(), node);
        // Choose expression
        sem_info.choose_expressions.insert(node.index(), node);

        ast.attach_semantic_info(sem_info);

        assert_eq!(ast.get_resolved_type(node), Some(ty));
        assert_eq!(ast.get_value_category(node), Some(ValueCategory::LValue));
        assert_eq!(ast.qual_type_of(node), ty);
        assert_eq!(ast.get_generic_selection(node), node);
        assert_eq!(ast.get_choose_expression(node), node);

        // Root node
        assert_eq!(ast.get_root(), NodeRef::ROOT);

        // Try string literal
        let break_node = ast.push_node(NodeKind::Break, SourceSpan::empty());
        assert_eq!(ast.try_string_literal(break_node), None);

        let lit_ref = LitRef::TRUE;
        let lit_node = ast.push_node(NodeKind::Literal(lit_ref), SourceSpan::empty());
        assert_eq!(ast.try_string_literal(lit_node), None);

        // This is a string literal, so it should return Some("hello")
        let str_ref = StringLitRef::from_bytes(std::borrow::Cow::Borrowed(b"hello"), StrPrefix::None);
        let str_node = ast.push_node(NodeKind::Literal(str_ref.into()), SourceSpan::empty());
        assert_eq!(ast.try_string_literal(str_node), Some("hello".to_string()));

        // NodeRef range
        let mut range = node.range(2_u32);
        assert_eq!(range.len(), 2);

        let n1 = range.next().unwrap();
        assert_eq!(n1.raw(), 1);

        let n2 = range.next().unwrap();
        assert_eq!(n2.raw(), 2);

        assert!(range.next().is_none());
        assert_eq!(range.size_hint(), (0, Some(0)));
    }
}
