struct Parser;

fn parse(p: &mut Parser) {}

fn main() {
    let mut p = Parser;
    let parser = &mut p;

    // Test 1: Implicit reborrow?
    parse(parser);
    parse(parser); // If this compiles, implicit reborrow works for functions.
}
