use vstd::prelude::*;

verus! {

use super::{is_permutation, is_valid_sorting_algorithm, swap};

pub exec fn bubble_sort(input: &mut Vec<i32>)
    ensures
        is_valid_sorting_algorithm(old(input)@, input@),
{
    let len = input.len();
    if len < 2 {
        return ;
    }
    let mut i: usize = 0;
    while i < len - 1
        invariant
            input.len() == old(input).len(),
            len == input.len(),
            0 <= i <= len - 1,
            is_permutation(old(input)@, input@),
            forall|u: int, v: int|
                (len as int - i as int) <= u < v < len as int ==> input[u] <= input[v],
            forall|k: int, m: int|
                0 <= k < (len as int - i as int) && (len as int - i as int) <= m < len as int
                    ==> input[k] <= input[m],
        decreases len - i,
    {
        let mut j: usize = 0;
        while j < len - i - 1
            invariant
                input.len() == old(input).len(),
                len == input.len(),
                0 <= i <= len - 1,
                0 <= j <= len - i - 1,
                is_permutation(old(input)@, input@),
                forall|u: int, v: int|
                    (len as int - i as int) <= u < v < len as int ==> input[u] <= input[v],
                forall|k: int, m: int|
                    0 <= k < (len as int - i as int) && (len as int - i as int) <= m < len as int
                        ==> input[k] <= input[m],
                forall|k: int| 0 <= k <= j as int ==> input[k] <= input[j as int],
            decreases (len as int - i as int - 1) - j as int,
        {
            if input[j] > input[j + 1] {
                swap(input, j, j + 1);
            }
            j += 1;
        }
        i += 1;
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
