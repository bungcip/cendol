use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_pipeline;

#[test]
fn test_c23_bool_literals_basic() {
    let src = "
        int main() {
            bool a = true;
            bool b = false;
            return a == true ? 1 : 0;
        }
    ";
    let _ = run_pipeline(src, CompilePhase::Mir);
}

#[test]
fn test_c23_bool_literals_types() {
    let src = "
        int main() {
            // true and false have type bool (_Bool)
            _Static_assert(sizeof(true) == 1, \"sizeof true\");
            _Static_assert(sizeof(false) == 1, \"sizeof false\");

            // _Generic should match _Bool
            _Static_assert(_Generic(true, _Bool: 1, default: 0) == 1, \"true is _Bool\");
            _Static_assert(_Generic(false, _Bool: 1, default: 0) == 1, \"false is _Bool\");

            return 0;
        }
    ";
    let _ = run_pipeline(src, CompilePhase::SemanticLowering);
}

#[test]
fn test_c23_bool_literals_pp() {
    let src = "
        #if true
        int x = 1;
        #else
        #error \"true should be 1\"
        #endif

        #if false
        #error \"false should be 0\"
        #else
        int y = 0;
        #endif

        // true and false interact with constants correctly in pp
        #if true + 1 == 2
        int z = 1;
        #endif

        int main() { return 0; }
    ";
    let _ = run_pipeline(src, CompilePhase::SemanticLowering);
}

#[test]
fn test_c23_bool_literals_const_eval() {
    let src = "
        // These can be used in constant expressions
        int arr1[true ? 5 : 2];
        _Static_assert(sizeof(arr1) == 5 * sizeof(int), \"size check\");

        int arr2[false ? 2 : 5];
        _Static_assert(sizeof(arr2) == 5 * sizeof(int), \"size check\");

        // Float conversion
        float f1 = true;
        float f2 = false;

        int main() { return 0; }
    ";
    let _ = run_pipeline(src, CompilePhase::Mir);
}
