use vstd::prelude::*;

verus! {

use super::{is_permutation, is_valid_sorting_algorithm, swap};

pub exec fn insertion_sort(input: &mut Vec<i32>)
    ensures
        is_valid_sorting_algorithm(old(input)@, input@),
{
    if input.is_empty() {
        return ;
    }
    for i in iter: 1..input.len()
        invariant
            iter.end == old(input).len(),
            input.len() == old(input).len(),
            forall|k1: int, k2: int| 0 <= k1 < k2 < i ==> input[k1] <= input[k2],  // Everything in the sorted partition is indeed sorted.
            is_permutation(old(input)@, input@),
    {
        let mut d = i;

        while d >= 1 && input[d - 1] > input[d]
            invariant
                0 <= d <= i < input.len(),
                input.len() == old(input).len(),
                forall|k1: int, k2: int| 0 <= k1 < k2 < d ==> input[k1] <= input[k2],  // Everything in the sorted partition before the "swapping point" is sorted.
                forall|k1: int, k2: int| d <= k1 < k2 <= i ==> input[k1] <= input[k2],  // Everything in the sorted partition after the "swapping point" is sorted.
                forall|k1: int, k2: int| 0 <= k1 < d && d < k2 <= i ==> input[k1] <= input[k2],  // Everything before the "swapping point" in the sorted partition is less than everything after the "swapping point" in the sorted partition.
                is_permutation(old(input)@, input@),
            decreases d,
        {
            swap(input, d, d - 1);
            d -= 1;
        }
    }
}

fn main() {
    let mut v = vec![2, 4, -5, 1, 3, 2];
    let ghost old_v = v@;

    insertion_sort(&mut v);
    let ghost new_v = v@;

    assert(is_valid_sorting_algorithm(old_v, new_v));
}

} // verus!
