#[cfg(test)]
mod tests {
    use crate::tests::parser_utils::setup_declaration;

    #[test]
    fn test_cast_attribute_pointer() {
        // This reproduces the issue: int b = ( (int(ATTR *)(void)) function_pointer)();
        let resolved = setup_declaration("int x = (int (__attribute__((unused)) *) (void)) 0;");
        insta::assert_yaml_snapshot!(resolved, @r"
        Declaration:
          specifiers:
            - int
          init_declarators:
            - name: x
              initializer:
                Cast:
                  - parsed_type_1_3
                  - LiteralInt: 0
        ");
    }

    #[test]
    fn test_param_attribute_int() {
        // Verify that (ATTR int) is still parsed as a parameter list.
        let resolved = setup_declaration("void foo(int (__attribute__((unused)) int));");
        insta::assert_yaml_snapshot!(resolved, @r"
        Declaration:
          specifiers:
            - void
          init_declarators:
            - name: foo
              kind: function(function(int) -> int) -> int
        ");
    }
}
