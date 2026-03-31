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
    let mut any_swapped = true;

    while any_swapped {
        any_swapped = false;

        for i in iter: 1..input.len(){
            if input[i - 1] > input[i] {
                swap(input, i - 1, i);
                any_swapped = true;
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
