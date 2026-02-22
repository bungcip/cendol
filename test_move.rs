enum Op { Const(i32), Other(Box<i32>) } fn main() { let op = Op::Const(1); if let Op::Const(x) = op { let y = Box::new(op); } }
