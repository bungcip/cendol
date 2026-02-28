use std::fs;

fn main() {
    let mut lowering = fs::read_to_string("src/semantic/lowering.rs").unwrap();
    lowering = lowering.replace(
        r#"        if let Some(cond_ty) = self.ast.get_resolved_type(cond_node)
            && !cond_ty.is_integer()
        {
            self.report_error(span, SemanticErrorKind::ExpectedIntegerType { found: cond_ty });
        }"#,
        r#"        if let Some(cond_ty) = self.ast.get_resolved_type(cond_node)
            && !cond_ty.is_integer()
        {
            // The condition of _Static_assert must be an integer constant expression.
            // Wait, an integer constant expression is one that has integer type.
            // If the type is not integer, we report error, but we still try to evaluate it for better diagnostics.
            self.report_error(span, SemanticErrorKind::ExpectedIntegerType { found: cond_ty });
        }"#
    );
    fs::write("src/semantic/lowering.rs", lowering).unwrap();

    let mut analyzer = fs::read_to_string("src/semantic/analyzer.rs").unwrap();
    analyzer = analyzer.replace(
        r#"        if let Some(cond_ty) = self.visit_node(cond)
            && !cond_ty.is_integer()
        {
            self.report_error(cond, SemanticErrorKind::ExpectedIntegerType { found: cond_ty });
        }"#,
        r#"        if let Some(cond_ty) = self.visit_node(cond)
            && !cond_ty.is_integer()
        {
            self.report_error(cond, SemanticErrorKind::ExpectedIntegerType { found: cond_ty });
        }"#
    );
    fs::write("src/semantic/analyzer.rs", analyzer).unwrap();
}
