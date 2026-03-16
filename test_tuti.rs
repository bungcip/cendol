use crate::tests::parser_utils::setup_expr;

#[test]
fn test_sizeof_postfix_tail_coverage() {
    let resolved_arrow = setup_expr("sizeof(a)->b");
    let resolved_call = setup_expr("sizeof(a)()");
    let resolved_inc = setup_expr("sizeof(a)++");
    let resolved_dec = setup_expr("sizeof(a)--");

    // We just want to check they parse without error. We can also snapshot them.
}
