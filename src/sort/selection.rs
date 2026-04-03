use vstd::prelude::*;

verus! {

use super::{is_permutation, is_valid_sorting_algorithm, swap};

pub exec fn selection_sort(input: &mut Vec<i32>)
    ensures
        is_valid_sorting_algorithm(old(input)@, input@),
{
    if input.is_empty() {
        return ;
    }
    for i in iter: 0..(input.len() - 1)
        invariant
            iter.end == input.len() - 1,
            input.len() == old(input).len(),
            is_permutation(old(input)@, input@),
            forall|k1: int, k2: int| 0 <= k1 < k2 < i ==> input[k1] <= input[k2],  // The sorted partition is indeed sorted
            forall|k1: int, k2: int|
                0 <= k1 < i && i <= k2 < input.len() ==> input[k1] <= input[k2],  // Everything in the sorted partition is less than everything in the unsorted partition
    {
        let mut min_index = i;

        for j in iter: (i + 1)..input.len()
            invariant
                iter.end == input.len(),
                i <= min_index < input.len(),  // Bounds check for `min_index`
                forall|k: int| i <= k < j ==> input[min_index as int] <= input[k],  // The item at `min_index` is the smallest out of all currently seen items in the unsorted partition
        {
            if input[j] < input[min_index] {
                min_index = j;
            }
        }

        if min_index != i {
            swap(input, i, min_index);
        }
    }
}

fn main() {
    let mut v = vec![2, 4, -5, 1, 3, 2];
    let ghost old_v = v@;

    selection_sort(&mut v);
    let ghost new_v = v@;

    assert(is_valid_sorting_algorithm(old_v, new_v));
}

} // verus!
