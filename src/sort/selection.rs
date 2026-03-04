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
    for i in 0..(input.len() - 1)
        invariant
            0 <= i < input.len(),
    {
        assert(0 <= i < input.len());

        let mut max_index = i;
        assert(0 <= max_index < input.len());

        for j in (i + 1)..input.len()
            invariant
                i <= max_index < input.len(),
        {
            assert(0 <= j < input.len());
            assert(0 <= max_index < input.len());

            if input[j] > input[max_index] {
                max_index = j;
            }
        }

        swap(input, i, max_index);
    }
}

fn main() {
    let mut v = vec![2, 4, -5, 1, 3, 2];
    let ghost old_v = v@;

    selection_sort(&mut v);
    let ghost new_v = v@;
}

} // verus!
