use vstd::prelude::*;

verus! {

use super::{is_permutation, is_valid_sorting_algorithm, swap};

pub exec fn bubble_sort(input: &mut Vec<i32>)
    ensures
        is_valid_sorting_algorithm(old(input)@, input@),
{
    if input.is_empty() {
        return ;
    }
    for i in iter: 0..(input.len() - 1)
        invariant
            input.len() == old(input).len(),
            iter.end == input.len() - 1,
            0 <= i <= input.len() - 1,
            is_permutation(old(input)@, input@),
            forall|u: int, v: int|
                (input.len() - i) <= u < v < input.len() ==> input[u] <= input[v],
            forall|k: int, m: int|
                0 <= k < (input.len() - i) && (input.len() - i) <= m < input.len() ==> input[k]
                    <= input[m],
    {
        for j in iter: 0..(input.len() - i - 1)
            invariant
                iter.end == input.len() - i - 1,
                input.len() == old(input).len(),
                is_permutation(old(input)@, input@),
                forall|u: int, v: int|
                    (input.len() - i) <= u < v < input.len() ==> input[u] <= input[v],
                forall|k: int, m: int|
                    0 <= k < (input.len() - i) && (input.len() - i) <= m < input.len() ==> input[k]
                        <= input[m],
                forall|k: int| 0 <= k <= j ==> input[k] <= input[j as int],
        {
            if input[j] > input[j + 1] {
                swap(input, j, j + 1);
            }
        }
    }
}

fn main() {
    let mut v = vec![2, 4, -5, 1, 3, 2];
    let ghost old_v = v@;

    bubble_sort(&mut v);
    let ghost new_v = v@;

    assert(is_valid_sorting_algorithm(old_v, new_v));
}

} // verus!
