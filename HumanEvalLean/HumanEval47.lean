module

/-! ## Implementation -/

public section

@[grind =]
def Array.mergeSort (xs : Array Int) : Array Int :=
  xs.toList.mergeSort.toArray

def median (xs : Array Int) (h : xs ≠ #[]) : Rat :=
  let sorted := xs.mergeSort
  have : 0 < sorted.size := by grind [List.length_mergeSort]
  if xs.size % 2 = 1 then
    sorted[sorted.size / 2]
  else
    (sorted[sorted.size / 2 - 1] + sorted[sorted.size / 2] : Rat) / 2

/-! ## Tests -/

example : median #[3, 1, 2, 4, 5] (by decide) = 3 := by native_decide
example : median #[-10, 4, 6, 1000, 10, 20] (by decide) = 8 := by native_decide
example : median #[5] (by decide) = 5 := by native_decide
example : median #[6, 5] (by decide) = 11/2 := by native_decide
example : median #[8, 1, 3, 9, 9, 2, 7] (by decide) = 7 := by native_decide

/-! ## Verification -/

theorem median_eq_getElem_of_odd {xs : Array Int} {h} (h' : xs.size % 2 = 1) :
    median xs h = xs.mergeSort[xs.size / 2]'(by grind [List.length_mergeSort]) := by
  grind [median, List.length_mergeSort]

theorem two_mul_median_of_even {xs : Array Int} {h} (h' : xs.size % 2 = 0) :
    2 * median xs h =
      xs.mergeSort[xs.size / 2 - 1]'(by grind [List.length_mergeSort]) +
      xs.mergeSort[xs.size / 2]'(by grind [List.length_mergeSort]) := by
  grind [median, List.length_mergeSort]

/-!
### MergeSort properties

The following two library lemmas show that `Array.mergeSort` correctly sorts an array.
-/

example {xs : Array Int} : xs.mergeSort.toList.Pairwise (· ≤ ·) := by
  grind [List.pairwise_mergeSort]

example {xs : Array Int} : xs.mergeSort.Perm xs := by
  grind [List.mergeSort_perm, Array.Perm]

/-!
## Prompt

```python3


def median(l: list):
    """Return median of elements in the list l.
    >>> median([3, 1, 2, 4, 5])
    3
    >>> median([-10, 4, 6, 1000, 10, 20])
    15.0
    """
```

## Canonical solution

```python3
    l = sorted(l)
    if len(l) % 2 == 1:
        return l[len(l) // 2]
    else:
        return (l[len(l) // 2 - 1] + l[len(l) // 2]) / 2.0
```

## Tests

```python3


METADATA = {}


def check(candidate):
    assert candidate([3, 1, 2, 4, 5]) == 3
    assert candidate([-10, 4, 6, 1000, 10, 20]) == 8.0
    assert candidate([5]) == 5
    assert candidate([6, 5]) == 5.5
    assert candidate([8, 1, 3, 9, 9, 2, 7]) == 7

```
-/
