def intersperse : List Int → Int → List Int
  | [],             _     => []
  | [i],            _     => [i]
  | i₁ :: i₂ :: tl, delim => i₁ :: delim :: intersperse (i₂ :: tl) delim

example : intersperse [] 7 = []                              := rfl
example : intersperse [5, 6, 3, 2] 8 = [5, 8, 6, 8, 3, 8, 2] := rfl
example : intersperse [2, 2, 2] 2 = [2, 2, 2, 2, 2]          := rfl

theorem intersperse_length_le : (intersperse nums delim).length ≤ 2 * nums.length - 1 := by
  fun_induction intersperse <;> simp only [intersperse, List.length_cons] at * <;> omega

-- Every element of index `2 * i` is the `i`th element of the input list.
theorem intersperse_get?_num (h : 1 < nums.length) :
    (intersperse nums delim)[2 * i]? = nums[i]? := by
  fun_induction intersperse generalizing i <;> try contradiction
  next tl _ ih =>
    cases tl <;> cases i
    case nil.succ j =>
      cases j <;> simp +arith [intersperse]
    case cons.succ j =>
      have hj : 2 * (j + 1) = 2 * j + 2 := rfl
      rw [intersperse, hj]
      simp [ih]
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
