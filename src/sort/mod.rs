use vstd::prelude::*;

mod selection;

verus! {

pub open spec fn is_sorted(v: &Vec<i32>) -> bool {
    forall |i: int, j: int| 0 <= i < j < v.len() ==> v[i] < v[j]
}

} // verus!
