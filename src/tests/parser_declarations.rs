#[cfg(test)]
mod tests {
    use crate::tests::parser_utils::setup_declaration;

    #[test]
    fn test_parse_noreturn_function_declaration() {
        let resolved = setup_declaration("_Noreturn void foo();");
        insta::assert_yaml_snapshot!(&resolved, @"
        Declaration:
          specifiers:
            - Noreturn
            - void
          init_declarators:
            - name: foo
              kind: function(void) -> int
        ");
    }
}
