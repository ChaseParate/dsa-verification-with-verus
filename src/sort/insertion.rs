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
    let mut x = 1;
    while x < input.len()
        invariant
            1 <= x <= input.len(),
            input.len() == old(input).len(),
            forall|i: int, j: int| 0 <= i < j < x ==> input[i] <= input[j],
            is_permutation(old(input)@, input@),
        decreases input.len() - x,
    {
        let mut d = x;

        while d >= 1 && input[d - 1] > input[d]
            invariant
                0 <= d <= x < input.len(),
                input.len() == old(input).len(),
                forall|i: int, j: int| 0 <= i < j < d ==> input[i] <= input[j],
                forall|i: int, j: int| d <= i < j <= x ==> input[i] <= input[j],
                forall|i: int, j: int| 0 <= i < d && d < j <= x ==> input[i] <= input[j],
                is_permutation(old(input)@, input@),
            decreases d,
        {
            swap(input, d, d - 1);
            d -= 1;
        }

        x += 1;
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
