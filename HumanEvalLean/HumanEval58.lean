module

public import Std
open Std

public section

/-! ## Implementation -/

def common (xs ys : List Nat) : List Nat :=
  let xsSet : TreeSet Nat := .ofList xs
  let ysSet : TreeSet Nat := .ofList ys
  ysSet.filter (· ∈ xsSet) |>.toList

/-! ## Tests -/

set_option cbv.warning false

example : common [1, 4, 3, 34, 653, 2, 5] [5, 7, 1, 5, 9, 653, 121] = [1, 5, 653] := by cbv
example : common [5, 3, 2, 8] [3, 2] = [2, 3] := by cbv
example : common [4, 3, 2, 8] [3, 2, 4] = [2, 3, 4] := by cbv
example : common [4, 3, 2, 8] [] = [] := by cbv

/-! ## Verification -/

theorem pairwise_lt_common :
    (common xs ys).Pairwise (· < ·) := by
  grind [common, TreeSet.ordered_toList, compare_eq_lt]

theorem distinct_common :
    (common xs ys).Pairwise (· ≠ ·) := by
  grind [common, TreeSet.distinct_toList]

theorem mem_common_iff :
    x ∈ common xs ys ↔ x ∈ xs ∧ x ∈ ys := by
  grind [common]

/-!
## Prompt

```python3


def common(l1: list, l2: list):
    """Return sorted unique common elements for two lists.
    >>> common([1, 4, 3, 34, 653, 2, 5], [5, 7, 1, 5, 9, 653, 121])
    [1, 5, 653]
    >>> common([5, 3, 2, 8], [3, 2])
    [2, 3]

    """
```

## Canonical solution

```python3
    ret = set()
    for e1 in l1:
        for e2 in l2:
            if e1 == e2:
                ret.add(e1)
    return sorted(list(ret))
```

## Tests

```python3


METADATA = {}


def check(candidate):
    assert candidate([1, 4, 3, 34, 653, 2, 5], [5, 7, 1, 5, 9, 653, 121]) == [1, 5, 653]
    assert candidate([5, 3, 2, 8], [3, 2]) == [2, 3]
    assert candidate([4, 3, 2, 8], [3, 2, 4]) == [2, 3, 4]
    assert candidate([4, 3, 2, 8], []) == []

```
-/
