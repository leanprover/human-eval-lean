module

/-! ## Implementation -/

def monotonic (xs : List Int) : Bool :=
  xs.Pairwise (· ≤ ·) || xs.Pairwise (· ≥ ·)

/-! ## Tests -/

set_option cbv.warning false

example : monotonic [1, 2, 4, 10] = true := by cbv
example : monotonic [1, 2, 4, 20] = true := by cbv
example : monotonic [1, 20, 4, 10] = false := by cbv
example : monotonic [4, 1, 0, -10] = true := by cbv
example : monotonic [4, 1, 1, 0] = true := by cbv
example : monotonic [1, 2, 3, 2, 5, 60] = false := by cbv
example : monotonic [1, 2, 3, 4, 5, 60] = true := by cbv
example : monotonic [9, 9, 9, 9] = true := by cbv

/-! ## Verification -/

theorem monotonic_iff :
    monotonic xs ↔
      (∀ (i j : Nat) (hi : i < j) (hj : j < xs.length), xs[i] ≤ xs[j]) ∨
      (∀ (i j : Nat) (hi : i < j) (hj : j < xs.length), xs[i] ≥ xs[j]) := by
  grind [monotonic, List.pairwise_iff_getElem]

/-!
## Prompt

```python3


def monotonic(l: list):
    """Return True is list elements are monotonically increasing or decreasing.
    >>> monotonic([1, 2, 4, 20])
    True
    >>> monotonic([1, 20, 4, 10])
    False
    >>> monotonic([4, 1, 0, -10])
    True
    """
```

## Canonical solution

```python3
    if l == sorted(l) or l == sorted(l, reverse=True):
        return True
    return False
```

## Tests

```python3


METADATA = {}


def check(candidate):
    assert candidate([1, 2, 4, 10]) == True
    assert candidate([1, 2, 4, 20]) == True
    assert candidate([1, 20, 4, 10]) == False
    assert candidate([4, 1, 0, -10]) == True
    assert candidate([4, 1, 1, 0]) == True
    assert candidate([1, 2, 3, 2, 5, 60]) == False
    assert candidate([1, 2, 3, 4, 5, 60]) == True
    assert candidate([9, 9, 9, 9]) == True

```
-/
