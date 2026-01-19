#[cfg(test)]
mod tests {
    use crate::tests::semantic_common::setup_mir;

    #[test]
    fn test_vla_ice_fix() {
        let source = r#"
            void f1(int argc)
            {
              char test[argc];
              if(0)
              label:
                (void)0;
              if(argc-- == 0)
                return;
              goto label;
            }
        "#;
        // Verify MIR generation succeeds (no ICE)
        // If semantic analysis fails to visit the VLA size expression,
        // the compiler panics with "ICE: ident 'argc' still not have resolved type".
        setup_mir(source);
    }

    #[test]
    fn test_vla_in_block_scope() {
        let source = r#"
            void f() {
                int n = 10;
                {
                    int m = 5;
                    int arr[n + m];
                }
            }
        "#;
        setup_mir(source);
    }
}
