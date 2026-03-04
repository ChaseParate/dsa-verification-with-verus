use vstd::prelude::*;

verus! {

use super::is_sorted;

pub fn selection_sort(v: &Vec<i32>) -> (s: Vec<i32>)
    ensures
        is_sorted(v),
{
    let mut s = v.clone();

    assume(is_sorted(v));  // TODO

    s
}

fn main() {
    let v = vec![9, 10, 4, 5, 1, 3];
    let v_sorted = selection_sort(&v);
}

} // verus!
