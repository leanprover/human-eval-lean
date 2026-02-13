module

public import Std
open Std

public section

/-! ## Implementation -/

@[grind =]
def getPositive (xs : Array Int): Array Int :=
  xs.filter (0 < ·)

/-! ## Tests -/

example : getPositive #[-1, -2, 4, 5, 6] = #[4, 5, 6] := by native_decide
example : getPositive #[5, 3, -5, 2, 3, 3, 9, 0, 123, 1, -10] = #[5, 3, 2, 3, 3, 9, 123, 1] := by native_decide
example : getPositive #[-1, -2] = #[] := by native_decide
example : getPositive #[] = #[] := by native_decide

/-! ## Verification -/

section Verification

variable {xs ys : Array Int}

theorem getPositive_empty : getPositive #[] = #[] := by grind
theorem getPositive_singleton_of_pos (h : 0 < x) : getPositive #[x] = #[x] := by grind
theorem getPositive_singleton_of_nonpos (h : x ≤ 0) : getPositive #[x] = #[] := by grind
theorem getPositive_push_of_pos (h : 0 < x) : getPositive (xs.push x) = (getPositive xs).push x := by grind
theorem getPositive_push_of_nonpos (h : x ≤ 0) : getPositive (xs.push x) = getPositive xs := by grind
theorem getPositive_append : getPositive (x ++ y) = getPositive x ++ getPositive y := by grind

end Verification

/-!
## Prompt

```python3


def get_positive(l: list):
    """Return only positive numbers in the list.
    >>> get_positive([-1, 2, -4, 5, 6])
    [2, 5, 6]
    >>> get_positive([5, 3, -5, 2, -3, 3, 9, 0, 123, 1, -10])
    [5, 3, 2, 3, 9, 123, 1]
    """
```

## Canonical solution

```python3
    return [e for e in l if e > 0]
```

## Tests

```python3


METADATA = {}


def check(candidate):
    assert candidate([-1, -2, 4, 5, 6]) == [4, 5, 6]
    assert candidate([5, 3, -5, 2, 3, 3, 9, 0, 123, 1, -10]) == [5, 3, 2, 3, 3, 9, 123, 1]
    assert candidate([-1, -2]) == []
    assert candidate([]) == []

```
-/
