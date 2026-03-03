module

set_option cbv.warning false

public section

/-! ## Implementation -/

def belowThreshold (xs : List Nat) (t : Nat) : Bool :=
  xs.all (· < t)

/-! ## Tests -/

example : belowThreshold [1, 2, 4, 10] 100 = true := by cbv
example : belowThreshold [1, 20, 4, 10] 5 = false := by cbv
example : belowThreshold [1, 20, 4, 10] 21 = true := by cbv
example : belowThreshold [1, 20, 4, 10] 22 = true := by cbv
example : belowThreshold [1, 8, 4, 10] 11 = true := by cbv
example : belowThreshold [1, 8, 4, 10] 10 = false := by cbv

/-! ## Verification -/

theorem belowThreshold_iff :
    belowThreshold xs t ↔ ∀ x ∈ xs, x < t := by
  grind [belowThreshold]

/-!
## Prompt

```python3


def below_threshold(l: list, t: int):
    """Return True if all numbers in the list l are below threshold t.
    >>> below_threshold([1, 2, 4, 10], 100)
    True
    >>> below_threshold([1, 20, 4, 10], 5)
    False
    """
```

## Canonical solution

```python3
    for e in l:
        if e >= t:
            return False
    return True
```

## Tests

```python3


METADATA = {}


def check(candidate):
    assert candidate([1, 2, 4, 10], 100)
    assert not candidate([1, 20, 4, 10], 5)
    assert candidate([1, 20, 4, 10], 21)
    assert candidate([1, 20, 4, 10], 22)
    assert candidate([1, 8, 4, 10], 11)
    assert not candidate([1, 8, 4, 10], 10)

```
-/
