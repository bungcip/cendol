#[cfg(test)]
mod tests {
    use crate::driver::CompilerDriver;
    use crate::driver::cli::CompileConfig;
    use crate::driver::compiler::CompilePhase;

    #[test]
    fn test_array_init_bug() {
        let source = r#"
            int a[] = {5, [2] = 2, 3};

            int
            main()
            {
                if (sizeof(a) != 4*sizeof(int))
                    return 1;

                if (a[0] != 5)
                    return 2;
                if (a[1] != 0)
                    return 3;
                if (a[2] != 2)
                    return 4;
                if (a[3] != 3)
                    return 5;

                return 0;
            }
        "#;

        let config = CompileConfig::from_virtual_file(source.to_string(), CompilePhase::EmitObject);
        let mut driver = CompilerDriver::from_config(config);

        let result = driver.run();
        assert!(result.is_ok(), "Compilation failed: {:?}", result.err());
    }
}
