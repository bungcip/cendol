use crate::tests::test_utils::run_fail_with_message;

#[test]
fn rejects_thread_local_on_function() {
    let src = "
        _Thread_local void my_func(void);
    ";
    run_fail_with_message(src, "_Thread_local is not allowed here");
}
