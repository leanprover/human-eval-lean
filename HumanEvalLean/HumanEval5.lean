example : [].intersperse 7 = []                              := rfl
example : [5, 6, 3, 2].intersperse 8 = [5, 8, 6, 8, 3, 8, 2] := rfl
example : [2, 2, 2].intersperse 2 = [2, 2, 2, 2, 2]          := rfl

namespace List

theorem intersperse_length_le (l : List α) : (l.intersperse delim).length ≤ 2 * l.length - 1 := by
  fun_induction intersperse <;> simp only [intersperse, length_cons] at * <;> try omega
  next h _ =>
    have := length_pos_iff.mpr h
    omega

-- Every element of index `2 * i` is the `i`th element of the input list.
theorem intersperse_getElem?_even {l : List α} (h : 1 < l.length) :
    (l.intersperse delim)[2 * i]? = l[i]? := by
  fun_induction intersperse generalizing i <;> try contradiction
  next hn ih =>
    have ⟨_, tl, hn⟩ := ne_nil_iff_exists_cons.mp hn
    cases tl <;> cases i
    case nil.succ j =>
      cases j <;> simp +arith [hn, intersperse]
    case cons.succ j =>
      have hj : 2 * (j + 1) = 2 * j + 2 := rfl
      rw [intersperse, hj] <;> simp_all
    all_goals simp [intersperse]

/-!
## Prompt

```python3
from typing import List


def intersperse(numbers: List[int], delimeter: int) -> List[int]:
    """ Insert a number 'delimeter' between every two consecutive elements of input list `numbers'
    >>> intersperse([], 4)
    []
    >>> intersperse([1, 2, 3], 4)
    [1, 4, 2, 4, 3]
    """
```

## Canonical solution

```python3
    if not numbers:
        return []

    result = []

    for n in numbers[:-1]:
        result.append(n)
        result.append(delimeter)

    result.append(numbers[-1])

    return result
```

## Tests

```python3


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    assert candidate([], 7) == []
    assert candidate([5, 6, 3, 2], 8) == [5, 8, 6, 8, 3, 8, 2]
    assert candidate([2, 2, 2], 2) == [2, 2, 2, 2, 2]
```
-/
