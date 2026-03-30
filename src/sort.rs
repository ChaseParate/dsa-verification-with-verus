use vstd::prelude::*;

mod insertion;
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

pub exec fn swap(input: &mut Vec<i32>, i: usize, j: usize)
    requires
        i < old(input).len(),
        j < old(input).len(),
    ensures
        old(input).len() == input.len(),
        old(input)[i as int] == input[j as int],
        old(input)[j as int] == input[i as int],
        forall|k: int|
            0 <= k < input.len() && k != i as int && k != j as int ==> old(input)[k] == input[k],
        is_permutation(old(input)@, input@),
{
    broadcast use vstd::seq_lib::group_to_multiset_ensures;

    let temp = input[i];
    input[i] = input[j];
    input[j] = temp;
}

} // verus!
