use vstd::prelude::*;

verus! {

use super::is_valid_sorting_algorithm;

pub fn selection_sort(input: Vec<i32>) -> (output: Vec<i32>)
    ensures
        is_valid_sorting_algorithm(input@, output@),
{
    // TODO
    let output = input;
    assume(is_valid_sorting_algorithm(input@, output@));

    output
}

fn main() {
    let v = vec![2, 4, -5, 1, 3, 2];
    let v_sorted = selection_sort(v);
}

} // verus!
