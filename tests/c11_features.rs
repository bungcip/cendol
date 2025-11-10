use insta::assert_snapshot;
use std::fs;
use std::process::Command;

/// Helper function to run the compiler with --dump-parser on a test file
fn run_c11_test(test_content: &str) -> (String, String) {
    let test_file = "tests/fixtures/temp_test.c";
    fs::write(test_file, test_content).expect("Failed to write test file");
    
    let output = Command::new("cargo")
        .args(&["run", "--", "--dump-parser", test_file])
        .output()
        .expect("Failed to execute cargo run");
    
    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    
    // Clean up
    fs::remove_file(test_file).ok();
    
    (stdout, stderr)
}

#[test]
fn test_basic_enum() {
    let test_content = r#"
enum Color { RED, GREEN, BLUE };
int main() {
    enum Color c = RED;
    return 0;
}
"#;

    let (stdout, stderr) = run_c11_test(test_content);
    
    if !stderr.is_empty() {
        println!("Stderr: {}", stderr);
    }
    
    assert_snapshot!(stdout);
}

#[test]
fn test_c11_booleans() {
    let test_content = r#"
int main() {
    _Bool flag = 1;
    _Bool another_flag = 0;
    return 0;
}
"#;

    let (stdout, stderr) = run_c11_test(test_content);
    
    if !stderr.is_empty() {
        println!("Stderr: {}", stderr);
    }
    
    assert_snapshot!(stdout);
}

#[test]
fn test_c11_restrict() {
    let test_content = r#"
void copy_string(char* restrict dest, const char* restrict src) {
    int i;
    for (i = 0; src[i] != '\0'; i++) {
        dest[i] = src[i];
    }
    dest[i] = '\0';
}

int main() {
    char buffer[100];
    copy_string(buffer, "Hello");
    return 0;
}
"#;

    let (stdout, stderr) = run_c11_test(test_content);
    
    if !stderr.is_empty() {
        println!("Stderr: {}", stderr);
    }
    
    assert_snapshot!(stdout);
}

#[test]
fn test_c11_static_assert() {
    let test_content = r#"
int main() {
    _Static_assert(sizeof(int) >= 4, "int must be at least 4 bytes");
    return 0;
}
"#;

    let (stdout, stderr) = run_c11_test(test_content);
    
    if !stderr.is_empty() {
        println!("Stderr: {}", stderr);
    }
    
    assert_snapshot!(stdout);
}

#[test]
fn test_existing_enum_simple() {
    let test_content = r#"
int main() {
    enum { RED, GREEN, BLUE } x;
    return 0;
}
"#;

    let (stdout, stderr) = run_c11_test(test_content);
    
    if !stderr.is_empty() {
        println!("Stderr: {}", stderr);
    }
    
    assert_snapshot!(stdout);
}

#[test]
fn test_existing_enum_with_usage() {
    let test_content = r#"
int main() {
    enum { RED, GREEN, BLUE } x;
    x = GREEN;
    return 0;
}
"#;

    let (stdout, stderr) = run_c11_test(test_content);
    
    if !stderr.is_empty() {
        println!("Stderr: {}", stderr);
    }
    
    assert_snapshot!(stdout);
}

#[test]
fn test_c11_unicode_strings() {
    let test_content = r#"
int main() {
    char* s1 = u8"UTF-8 string";
    wchar_t* s2 = L"Wide string";
    return 0;
}
"#;

    let (stdout, stderr) = run_c11_test(test_content);
    
    if !stderr.is_empty() {
        println!("Stderr: {}", stderr);
    }
    
    assert_snapshot!(stdout);
}

#[test]
fn test_complex_numbers() {
    let test_content = r#"
int main() {
    float _Complex z1 = 1.0f + 2.0fi;
    double _Complex z2 = 3.0 + 4.0i;
    return 0;
}
"#;

    let (stdout, stderr) = run_c11_test(test_content);
    
    if !stderr.is_empty() {
        println!("Stderr: {}", stderr);
    }
    
    assert_snapshot!(stdout);
}

#[test]
fn test_aligned_types() {
    let test_content = r#"
int main() {
    _Alignas(16) int aligned_int;
    _Alignof(int) alignment;
    return 0;
}
"#;

    let (stdout, stderr) = run_c11_test(test_content);
    
    if !stderr.is_empty() {
        println!("Stderr: {}", stderr);
    }
    
    assert_snapshot!(stdout);
}

#[test]
fn test_thread_local() {
    let test_content = r#"
_Thread_local int global_counter = 0;

int main() {
    global_counter = 42;
    return 0;
}
"#;

    let (stdout, stderr) = run_c11_test(test_content);
    
    if !stderr.is_empty() {
        println!("Stderr: {}", stderr);
    }
    
    assert_snapshot!(stdout);
}

#[test]
fn test_generic_selection() {
    let test_content = r#"
#define max(x, y) _Generic((x), \
    int: ((x) > (y) ? (x) : (y)), \
    default: 0 \
)

int main() {
    int a = max(5, 3);
    return 0;
}
"#;

    let (stdout, stderr) = run_c11_test(test_content);
    
    if !stderr.is_empty() {
        println!("Stderr: {}", stderr);
    }
    
    assert_snapshot!(stdout);
}

#[test]
fn test_noreturn() {
    let test_content = r#"
_Noreturn void fatal_error() {
    while (1) {
        // Infinite loop to simulate fatal error
    }
}

int main() {
    fatal_error();
    return 0;
}
"#;

    let (stdout, stderr) = run_c11_test(test_content);
    
    if !stderr.is_empty() {
        println!("Stderr: {}", stderr);
    }
    
    assert_snapshot!(stdout);
}

#[test]
fn test_comprehensive_c11() {
    let test_content = r#"
// Test multiple C11 features in one file
_Thread_local int thread_var = 0;

int main() {
    // Boolean type
    _Bool flag = 1;
    
    // Static assertion
    _Static_assert(sizeof(int) >= 4, "int too small");
    
    // Aligned types
    _Alignas(8) int aligned_int;
    
    // Generic selection
    #define type_name(x) _Generic((x), \
        int: "int", \
        float: "float", \
        default: "unknown" \
    )
    
    const char* name = type_name(42);
    
    // Thread local
    thread_var = 123;
    
    // Restrict pointers
    void copy_int(int* restrict dest, const int* restrict src) {
        *dest = *src;
    }
    
    int source = 999;
    int dest;
    copy_int(&dest, &source);
    
    return 0;
}
"#;

    let (stdout, stderr) = run_c11_test(test_content);
    
    if !stderr.is_empty() {
        println!("Stderr: {}", stderr);
    }
    
    assert_snapshot!(stdout);
}