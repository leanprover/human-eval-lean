module

import Std

open Std

/-!
## Implementation
-/

def addElements (xs : Array Int) (k : Nat) : Int :=
  xs.iter.take k
    |>.filter (fun x => (toString x).length ≤ 2)
    |>.fold (init := 0) (· + ·)

/-!
## Tests
-/

example : addElements #[1,-2,-3,41,57,76,87,88,99] 3 = -4 := by native_decide
example : addElements #[111,121,3,4000,5,6] 2 = 0 := by native_decide
example : addElements #[11,21,3,90,5,6,7,8,9] 4 = 125 := by native_decide
example : addElements #[111,21,3,4000,5,6,7,8,9] 4 = 24 := by native_decide
example : addElements #[1] 1 = 1 := by native_decide

/-!
## Verification
-/

theorem Array.sum_eq_foldl_int {xs : Array Int} :
    xs.sum = xs.foldl (init := 0) (· + ·) := by
  sorry

theorem Array.sum_append_int {xs ys : Array Int} :
    (xs ++ ys).sum = xs.sum + ys.sum := by
  sorry

attribute [simp] Iter.toArray_filter

/-- arithmetic characterization of an integer's length as a string -/
theorem length_toString_le_two_iff {x : Int} :
    (toString x).length ≤ 2 ↔ x ∈ (-9)...=99 := by
  sorry

/-- characterization of `addElements` in terms of `Array` operations -/
theorem addElements_spec {xs : Array Int} {k : Nat} :
    addElements xs k = ((xs.extract 0 k).filter (fun x => (toString x).length ≤ 2)).sum := by
  simp [addElements, ← Iter.foldl_toArray, Array.sum_eq_foldl_int]

-- next, we state and verify the behavior from different angles

theorem addElements_append {xs ys : Array Int} {k : Nat} :
    addElements (xs ++ ys) k = addElements xs k + addElements ys (k - xs.size) := by
  simp [addElements_spec, Array.sum_append_int]

theorem addElements_zero {xs : Array Int} :
    addElements xs 0 = 0 := by
  simp [addElements_spec]


/-!
## Prompt

```python3

def add_elements(arr, k):
    """
    Given a non-empty array of integers arr and an integer k, return
    the sum of the elements with at most two digits from the first k elements of arr.

    Example:

        Input: arr = [111,21,3,4000,5,6,7,8,9], k = 4
        Output: 24 # sum of 21 + 3

    Constraints:
        1. 1 <= len(arr) <= 100
        2. 1 <= k <= len(arr)
    """
```

## Canonical solution

```python3
    return sum(elem for elem in arr[:k] if len(str(elem)) <= 2)
```

## Tests

```python3
def check(candidate):

    # Check some simple cases
    assert candidate([1,-2,-3,41,57,76,87,88,99], 3) == -4
    assert candidate([111,121,3,4000,5,6], 2) == 0
    assert candidate([11,21,3,90,5,6,7,8,9], 4) == 125
    assert candidate([111,21,3,4000,5,6,7,8,9], 4) == 24, "This prints if this assert fails 1 (good for debugging!)"

    # Check some edge cases that are easy to work out by hand.
    assert candidate([1], 1) == 1, "This prints if this assert fails 2 (also good for debugging!)"

```
-/
