use vstd::prelude::*;

verus! {

use super::{is_permutation, is_valid_sorting_algorithm, swap};

pub exec fn merge_sort(input: &mut Vec<i32>)
    ensures
        is_valid_sorting_algorithm(old(input)@, input@),
{
    if input.len() <= 1 {
        return ;
    }
    let mut temp_merge_space = Vec::with_capacity(input.len());
    merge_sort_recursive(input, &mut temp_merge_space, 0, input.len() - 1);
}

pub exec fn merge(
    input: &mut Vec<i32>,
    temp_merge_space: &mut Vec<i32>,
    start: usize,
    middle: usize,
    end: usize,
)
    requires
        0 <= start <= middle < end < old(input).len(),
        old(temp_merge_space).len() == 0,
    ensures
        temp_merge_space.len() == 0,
{
    let left_start = start;
    let left_end = middle;
    let ghost left_size = left_end - left_start + 1;

    let right_start = middle + 1;
    let right_end = end;
    let ghost right_size = right_end - right_start + 1;

    let mut left_pointer = left_start;
    let mut right_pointer = right_start;

    let ghost both_size = left_size + right_size;

    while left_pointer <= left_end && right_pointer <= right_end
        decreases both_size,
    {
        if input[left_pointer] <= input[right_pointer] {
            temp_merge_space.push(input[left_pointer]);
            left_pointer += 1;
        } else {
            temp_merge_space.push(input[right_pointer]);
            right_pointer += 1;
        }

        proof {
            both_size = both_size - 1;
        }
    }

    while left_pointer <= left_end
        decreases both_size,
    {
        temp_merge_space.push(input[left_pointer]);
        left_pointer += 1;

        proof {
            both_size = both_size - 1;
        }
    }

    while right_pointer <= right_end
        decreases both_size,
    {
        temp_merge_space.push(input[right_pointer]);
        right_pointer += 1;

        proof {
            both_size = both_size - 1;
        }
    }

    assert(both_size == 0);

    for i in 0..temp_merge_space.len() {
        let input_i = i + left_start;
        input[input_i] = temp_merge_space[i];
    }

    temp_merge_space.clear();
}

pub exec fn merge_sort_recursive(
    input: &mut Vec<i32>,
    temp_merge_space: &mut Vec<i32>,
    start: usize,
    end: usize,
)
    requires
        0 <= start <= end < old(input).len(),
    ensures
        is_valid_sorting_algorithm(old(input)@, input@),
    decreases end - start,
{
    let size = end - start + 1;
    if size <= 1 {
        return ;
    }
    let middle = start + ((end - start) / 2);
    merge_sort_recursive(input, temp_merge_space, start, middle);
    merge_sort_recursive(input, temp_merge_space, middle + 1, end);
    merge(input, temp_merge_space, start, middle, end);
}

fn main() {
    let mut v = vec![2, 4, -5, 1, 3, 2];
    let ghost old_v = v@;

    merge_sort(&mut v);
    let ghost new_v = v@;

    assert(is_valid_sorting_algorithm(old_v, new_v));
}

} // verus!
