use crate::tests::test_utils::run_pipeline_to_mir;

#[test]
fn test_comma_operator_crash() {
    let src = r#"
        void test(char *p, char *q) {
            p++, q++;
        }

        int main() {
            return 0;
        }
    "#;
    run_pipeline_to_mir(src);
}

#[test]
fn test_comma_operator_types() {
    let src = r#"
        void test() {
            int x = 0;
            char *p = 0;
            // (void)x, p  -> type should be char*
            char *q = (x++, p);
        }
    "#;
    run_pipeline_to_mir(src);
}

#[test]
fn test_comma_operator_loop() {
    let src = r#"
        void loop(char *s, char *f) {
            for (; *f; f++, s++)
                ;
        }
    "#;
    run_pipeline_to_mir(src);
}
