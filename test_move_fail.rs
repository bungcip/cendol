enum Op { Const(i32), Other(Box<i32>) } fn main() { let op = Op::Const(1); match op { Op::Const(x) => { let y = op; } _ => {} } }
