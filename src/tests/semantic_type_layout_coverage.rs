#[cfg(test)]
mod tests {
    use crate::semantic::type_registry::*;
    use crate::semantic::types::*;
    use target_lexicon::Triple;

    #[test]
    fn test_try_get_layout_coverage() {
        let mut registry = TypeRegistry::new(Triple::host());

        // Test Short
        let short_ty = registry.get_builtin_type(BuiltinType::Short);
        let layout = registry.try_get_layout(short_ty).unwrap();
        assert_eq!(layout.size, 2);
        assert_eq!(layout.alignment, 2);

        // Test Float
        let float_ty = registry.get_builtin_type(BuiltinType::Float);
        let layout = registry.try_get_layout(float_ty).unwrap();
        assert_eq!(layout.size, 4);
        assert_eq!(layout.alignment, 4);

        // Test Double
        let double_ty = registry.get_builtin_type(BuiltinType::Double);
        let layout = registry.try_get_layout(double_ty).unwrap();
        assert_eq!(layout.size, 8);
        assert_eq!(layout.alignment, 8);

        // Test LongDouble
        let long_double_ty = registry.get_builtin_type(BuiltinType::LongDouble);
        let layout = registry.try_get_layout(long_double_ty).unwrap();
        assert_eq!(layout.size, 16);
        assert_eq!(layout.alignment, 16);

        // Test VaList
        let va_list_ty = registry.get_builtin_type(BuiltinType::VaList);
        let layout = registry.try_get_layout(va_list_ty).unwrap();
        assert_eq!(layout.size, 24);
        assert_eq!(layout.alignment, 8);

        // Test Complex
        let float_ty = registry.get_builtin_type(BuiltinType::Float);
        let complex_ty = registry.complex_type(float_ty);
        let layout = registry.try_get_layout(complex_ty).unwrap();
        assert_eq!(layout.size, 8);
        assert_eq!(layout.alignment, 4);
    }
}
