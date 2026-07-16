use crate::pp::error::PPError;

#[test]
fn test_pperror_display() {
    let cases = [
        (PPError::IncludeDepthExceeded, "Include depth exceeded"),
        (PPError::ExpectedIdentifier, "Expected identifier"),
        (PPError::InvalidDirective, "Invalid directive"),
        (PPError::UnexpectedEndOfFile, "Unexpected end of file"),
        (PPError::InvalidMacroParameter, "Invalid macro parameter"),
        (PPError::InvalidIncludePath, "Invalid include path"),
        (PPError::UnmatchedEndif, "Unmatched #endif"),
        (PPError::ErrorDirective("foo".to_string()), "#error directive: foo"),
        (PPError::InvalidConditionalExpression, "Invalid conditional expression"),
        (PPError::DivisionByZero, "division by zero in preprocessor expression"),
        (PPError::RemainderByZero, "remainder by zero in preprocessor expression"),
        (PPError::InvalidLineDirective, "Invalid #line directive"),
        (PPError::MultipleElse, "Multiple #else directives"),
        (PPError::ElifAfterElse, "#elif after #else"),
        (PPError::ElifWithoutIf, "#elif without #if"),
        (PPError::ElseWithoutIf, "#else without #if"),
        (PPError::ExpectedEod, "Expected end of directive"),
        (
            PPError::UnknownPragma(crate::ast::StringId::new("bar")),
            "Unknown pragma: bar",
        ),
        (
            PPError::InvalidPragmaPackValue(crate::ast::StringId::new("baz")),
            "Invalid Pragma Pack Value: baz",
        ),
        (PPError::PragmaError("qux".to_string()), "Pragma error: qux"),
        (
            PPError::UnclosedConditional,
            "Unclosed preprocessor conditional directive",
        ),
        (
            PPError::InvalidUniversalCharacterName,
            "Invalid universal character name",
        ),
        (PPError::DollarInIdentifier, "'$' in identifier or number"),
        (
            PPError::DirectiveInMacroArgs,
            "embedding a directive within macro arguments is not portable",
        ),
        (
            PPError::ExpectedCommaInMacroParameterList,
            "expected comma in macro parameter list",
        ),
        (PPError::ExpectedRightParenAfterEllipsis, "expected ')' after \"...\""),
    ];

    for (error, expected_msg) in cases {
        assert_eq!(error.to_string(), expected_msg);
    }

    assert_eq!(
        PPError::FileNotFound {
            path: "test.h".to_string()
        }
        .to_string(),
        "File not found: test.h"
    );
    assert_eq!(
        PPError::MacroRedefined(crate::ast::StringId::new("MY_MACRO")).to_string(),
        "Macro 'MY_MACRO' redefined with different value"
    );
    assert_eq!(
        PPError::PoisonedIdentifier(crate::ast::StringId::new("BAD_ID")).to_string(),
        "attempt to use poisoned identifier 'BAD_ID'"
    );
    assert_eq!(
        PPError::DuplicateMacroParameter(crate::ast::StringId::new("param")).to_string(),
        "duplicate macro parameter name 'param'"
    );
}
