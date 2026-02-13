module

/-! ## Implementation -/

def maxElement (xs : Array Int) : Int :=
  xs.max?.getD 0

/-! ## Tests -/

example : maxElement #[1, 2, 3] = 3 := by native_decide
example : maxElement #[5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10] = 124 := by native_decide

/-! ## Verification -/

theorem maxElement_le_iff {xs : Array Int} {y : Int} (h : xs ≠ #[]) :
    maxElement xs ≤ y ↔ ∀ x ∈ xs, x ≤ y := by
  simp [maxElement, Array.max?_eq_some_max h, Array.max_le_iff]

theorem maxElement_mem {xs : Array Int} (h : xs ≠ #[]) :
    maxElement xs ∈ xs := by
  simpa [maxElement, Array.max?_eq_some_max h] using Array.max_mem h

/-!
## Prompt

```python3


def max_element(l: list):
    """Return maximum element in the list.
    >>> max_element([1, 2, 3])
    3
    >>> max_element([5, 3, -5, 2, -3, 3, 9, 0, 123, 1, -10])
    123
    """
```

## Canonical solution

```python3
    m = l[0]
    for e in l:
        if e > m:
            m = e
    return m
```

## Tests

```python3


METADATA = {}


def check(candidate):
    assert candidate([1, 2, 3]) == 3
    assert candidate([5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10]) == 124
```
-/
