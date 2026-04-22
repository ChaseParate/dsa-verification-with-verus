use vstd::prelude::*;

verus! {

use super::{is_sorted, is_valid_sorting_algorithm};

broadcast use vstd::seq_lib::group_to_multiset_ensures;

proof fn concat_multiset(a: Seq<i32>, b: Seq<i32>)
    ensures
        (a + b).to_multiset() =~= a.to_multiset().add(b.to_multiset()),
    decreases b.len(),
{
    if b.len() != 0 {
        assert(b =~= b.drop_last().push(b.last()) && a + b =~= (a + b.drop_last()).push(b.last()));
        concat_multiset(a, b.drop_last());
    }
}

proof fn subrange_multiset_split(s: Seq<i32>, lo: int, mid: int, hi: int)
    requires
        0 <= lo <= mid <= hi <= s.len(),
    ensures
        s.subrange(lo, hi).to_multiset() =~= s.subrange(lo, mid).to_multiset().add(
            s.subrange(mid, hi).to_multiset(),
        ),
{
    assert(s.subrange(lo, hi) =~= s.subrange(lo, mid) + s.subrange(mid, hi));
    concat_multiset(s.subrange(lo, mid), s.subrange(mid, hi));
}

pub exec fn merge_sort(input: &mut Vec<i32>)
    ensures
        is_valid_sorting_algorithm(old(input)@, input@),
{
    if input.len() <= 1 {
        return ;
    }
    let mut temp_merge_space = Vec::with_capacity(input.len());
    merge_sort_recursive(input, &mut temp_merge_space, 0, input.len() - 1);
    proof {
        assert(input@.subrange(0, input@.len() as int) =~= input@ && old(input)@.subrange(
            0,
            old(input)@.len() as int,
        ) =~= old(input)@);
    }
}

exec fn merge(
    input: &mut Vec<i32>,
    temp_merge_space: &mut Vec<i32>,
    start: usize,
    middle: usize,
    end: usize,
)
    requires
        start <= middle < end < old(input).len(),
        old(temp_merge_space).len() == 0,
        is_sorted(old(input)@.subrange(start as int, middle as int + 1)),
        is_sorted(old(input)@.subrange(middle as int + 1, end as int + 1)),
    ensures
        input.len() == old(input).len(),
        temp_merge_space.len() == 0,
        is_sorted(input@.subrange(start as int, end as int + 1)),
        input@.subrange(start as int, end as int + 1).to_multiset() =~= old(input)@.subrange(
            start as int,
            end as int + 1,
        ).to_multiset(),
        forall|k: int| 0 <= k < start ==> input[k] == old(input)[k],
        forall|k: int| end < k < input.len() ==> input[k] == old(input)[k],
{
    let mut left_pointer = start;
    let mut right_pointer = middle + 1;

    while left_pointer <= middle || right_pointer <= end
        invariant
            start <= left_pointer <= middle + 1,
            middle + 1 <= right_pointer <= end + 1,
            end < input.len(),
            temp_merge_space.len() == (left_pointer - start) + (right_pointer - middle - 1),
            is_sorted(temp_merge_space@),
            temp_merge_space.len() > 0 && left_pointer <= middle ==> temp_merge_space@.last()
                <= input[left_pointer as int],
            temp_merge_space.len() > 0 && right_pointer <= end ==> temp_merge_space@.last()
                <= input[right_pointer as int],
            temp_merge_space@.to_multiset() =~= input@.subrange(
                start as int,
                left_pointer as int,
            ).to_multiset().add(
                input@.subrange(middle as int + 1, right_pointer as int).to_multiset(),
            ),
            is_sorted(input@.subrange(start as int, middle as int + 1)),
            is_sorted(input@.subrange(middle as int + 1, end as int + 1)),
        decreases end - start + 1 - temp_merge_space@.len(),
    {
        if right_pointer > end || (left_pointer <= middle && input[left_pointer]
            <= input[right_pointer]) {
            proof {
                assert((left_pointer + 1 <= middle ==> input@.subrange(
                    start as int,
                    middle as int + 1,
                )[(left_pointer - start) as int] <= input@.subrange(
                    start as int,
                    middle as int + 1,
                )[(left_pointer - start) as int + 1]) && input@.subrange(
                    start as int,
                    left_pointer as int + 1,
                ) =~= input@.subrange(start as int, left_pointer as int).push(
                    input[left_pointer as int],
                ));
            }
            temp_merge_space.push(input[left_pointer]);
            left_pointer += 1;
        } else {
            proof {
                assert((right_pointer + 1 <= end ==> input@.subrange(
                    middle as int + 1,
                    end as int + 1,
                )[(right_pointer - middle - 1) as int] <= input@.subrange(
                    middle as int + 1,
                    end as int + 1,
                )[(right_pointer - middle - 1) as int + 1]) && input@.subrange(
                    middle as int + 1,
                    right_pointer as int + 1,
                ) =~= input@.subrange(middle as int + 1, right_pointer as int).push(
                    input[right_pointer as int],
                ));
            }
            temp_merge_space.push(input[right_pointer]);
            right_pointer += 1;
        }
    }

    for i in 0..temp_merge_space.len()
        invariant
            temp_merge_space.len() == end - start + 1,
            input.len() == old(input).len(),
            end < input.len(),
            forall|k: int| 0 <= k < start ==> input[k] == old(input)[k],
            forall|k: int| end < k < input.len() ==> input[k] == old(input)[k],
            forall|k: int| 0 <= k < i ==> input[start as int + k] == temp_merge_space[k],
    {
        input[i + start] = temp_merge_space[i];
    }

    proof {
        subrange_multiset_split(old(input)@, start as int, middle as int + 1, end as int + 1);
        assert(input@.subrange(start as int, end as int + 1) =~= temp_merge_space@);
    }

    temp_merge_space.clear();
}

exec fn merge_sort_recursive(
    input: &mut Vec<i32>,
    temp_merge_space: &mut Vec<i32>,
    start: usize,
    end: usize,
)
    requires
        start <= end < old(input).len(),
        old(temp_merge_space).len() == 0,
    ensures
        input.len() == old(input).len(),
        temp_merge_space.len() == 0,
        is_sorted(input@.subrange(start as int, end as int + 1)),
        input@.subrange(start as int, end as int + 1).to_multiset() =~= old(input)@.subrange(
            start as int,
            end as int + 1,
        ).to_multiset(),
        forall|k: int| 0 <= k < start ==> input[k] == old(input)[k],
        forall|k: int| end < k < input.len() ==> input[k] == old(input)[k],
    decreases end - start,
{
    if start == end {
        return ;
    }
    let middle = start + ((end - start) / 2);

    merge_sort_recursive(input, temp_merge_space, start, middle);

    let ghost input_after_left = input@;

    merge_sort_recursive(input, temp_merge_space, middle + 1, end);

    proof {
        assert(input_after_left.subrange(middle as int + 1, end as int + 1) =~= old(
            input,
        )@.subrange(middle as int + 1, end as int + 1) && input@.subrange(
            start as int,
            middle as int + 1,
        ) =~= input_after_left.subrange(start as int, middle as int + 1));
        subrange_multiset_split(old(input)@, start as int, middle as int + 1, end as int + 1);
        subrange_multiset_split(input@, start as int, middle as int + 1, end as int + 1);
    }

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
