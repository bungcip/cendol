use super::semantic_common::run_full_pass;

#[test]
fn test_string_literal_array_init() {
    run_full_pass(
        r#"
        char s1[] = "abc";
        char s2[4] = "def";
        const char s3[] = "ghi";
        signed char s4[] = "jkl";
        unsigned char s5[] = "mno";

        int main() {
            if (sizeof(s1) != 4) return 1;
            if (sizeof(s2) != 4) return 2;
            if (sizeof(s3) != 4) return 3;
            if (sizeof(s4) != 4) return 4;
            if (sizeof(s5) != 4) return 5;
            return 0;
        }
    "#,
    );
}

#[test]
fn test_string_literal_concatenated_init() {
    run_full_pass(
        r#"
        #define B "b"
        char s[] = "a" B "c";
        int main() {
            if (sizeof(s) != 4) return 1;
            if (s[0] != 'a' || s[1] != 'b' || s[2] != 'c' || s[3] != '\0') return 2;
            return 0;
        }
    "#,
    );
}
