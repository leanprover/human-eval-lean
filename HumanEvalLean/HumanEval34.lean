module

public import Std
open Std

public section

/-! ## Implementation -/

def unique (xs : Array Nat) : Array Nat :=
  (TreeSet.ofList xs.toList).toArray -- TODO: use `ofArray` as soon as there are lemmas for it

/-! ## Tests -/

example : unique #[5, 3, 5, 2, 3, 3, 9, 0, 123] = #[0, 2, 3, 5, 9, 123] := by native_decide

/-! ## Verification -/

theorem pairwise_lt_unique {xs : Array Nat} :
    (unique xs).toList.Pairwise (· < ·) := by
  -- ideally, we'd have `ordered_toArray`
  simpa [unique, ← TreeSet.toArray_toList, compare_eq_lt] using TreeSet.ordered_toList (α := Nat) (cmp := compare)

theorem pairwise_ne_unique {xs : Array Nat} :
    (unique xs).toList.Pairwise ( · ≠ ·) := by
  simpa [unique, ← TreeSet.toArray_toList, compare_ne_eq] using TreeSet.distinct_toList (α := Nat) (cmp := compare)

theorem mem_unique_iff {xs : Array Nat} {x : Nat} :
    x ∈ unique xs ↔ x ∈ xs := by
  grind [unique]

/-!
## Prompt

```python3


def unique(l: list):
    """Return sorted unique elements in a list
    >>> unique([5, 3, 5, 2, 3, 3, 9, 0, 123])
    [0, 2, 3, 5, 9, 123]
    """
```

## Canonical solution

```python3
    return sorted(list(set(l)))
```

## Tests

```python3


METADATA = {}


def check(candidate):
    assert candidate([5, 3, 5, 2, 3, 3, 9, 0, 123]) == [0, 2, 3, 5, 9, 123]

```
-/
