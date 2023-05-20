use aiken/list.{all}
use aiken/transaction/value.{Value, flatten}

// a helper function to check that the value is nonnegative
fn isNonnegativeValueInner(a: (t1, t2, Int)) -> Bool {
  let (_, _, n) =
    a
  n >= 0
}

pub fn isNonnegativeValue(val: Value) {
  all(flatten(val), isNonnegativeValueInner)
}
