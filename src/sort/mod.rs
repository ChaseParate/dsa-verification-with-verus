use vstd::prelude::*;

mod selection;

verus! {

pub open spec fn is_sorted(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

pub open spec fn is_permutation(input: Seq<i32>, output: Seq<i32>) -> bool {
    input.to_multiset() =~= output.to_multiset()
}

pub open spec fn is_valid_sorting_algorithm(input: Seq<i32>, output: Seq<i32>) -> bool {
    is_sorted(output) && is_permutation(input, output)
}

} // verus!
