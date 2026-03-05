module

/-! ## Missing API -/

-- The following two instances should not be upstreamed verbatim. Instead, `Bool` should be
-- a genuine linear order.
instance : Std.LawfulOrderOrd Bool where
  isLE_compare a b := by cases a <;> cases b <;> simp [compare, LE.le]
  isGE_compare a b := by cases a <;> cases b <;> simp [compare, LE.le]
instance : Std.LawfulOrderLT Bool where
  lt_iff a b := by cases a <;> cases b <;> simp [LT.lt, LE.le]

-- The lexicographic order on pairs is intentionally not a global instance.
-- However, there should be a `IsLinearOrder` instance for it (etc.)
local instance : Ord (Bool × Nat) := lexOrd
local instance : LE (Bool × Nat) := leOfOrd
local instance : LT (Bool × Nat) := ltOfOrd
local instance : Std.IsLinearOrder (Bool × Nat) := .of_ord

@[simp, grind .]
theorem Bool.not_lt_false {x : Bool} :
    ¬ x < false := by
  simp [LT.lt]

theorem Bool.compare_eq_lt {x y : Bool} :
    compare x y = .lt ↔ x = false ∧ y = true := by
  simp only [compare]
  split <;> grind

theorem compare_lexOrd_eq [Ord α] [Ord β] {x y : α × β} :
    haveI : Ord (α × β) := lexOrd
    compare x y = (compare x.1 y.1).then (compare x.2 y.2) := by
  simp [compare, compareLex, compareOn]

/-! ## Implementation -/

-- (Returning an `Option (Nat × Nat))` would be better, but we will stick to the problem description.)
def pluck (xs : Array Nat) : List Nat :=
  let i? := xs.toList.minIdxOn? (fun x => (x % 2 == 1, x))
  match h : i? with
  | some i =>
    have h : i < xs.size := by
      simp only [i?, Option.eq_some_iff_get_eq, List.get_minIdxOn?_eq_minIdxOn] at h
      simp only [← h.choose_spec]
      apply List.minIdxOn_lt_length
    let x := xs[i]'h
    if x % 2 = 0 then
      [x, i]
    else
      []
  | none => []

/-! ## Tests -/

example : pluck #[4, 2, 3] = [2, 1] := by native_decide
example : pluck #[1, 2, 3] = [2, 1] := by native_decide
example : pluck #[] = [] := by native_decide
example : pluck #[5, 0, 3, 0, 4, 2] = [0, 1] := by native_decide
example : pluck #[1, 2, 3, 0, 5, 3] = [0, 3] := by native_decide
example : pluck #[5, 4, 8, 4, 8] = [4, 1] := by native_decide
example : pluck #[7, 6, 7, 1] = [6, 1] := by native_decide
example : pluck #[7, 9, 7, 1] = [] := by native_decide

/-! ## Verification -/

theorem pluck_empty :
    pluck #[] = [] := by
  grind [pluck, List.minIdxOn?_nil]

theorem pluck_eq_empty (h : ∀ (i : Nat) (hi : i < xs.size), xs[i] % 2 = 1) :
    pluck xs = [] := by
  grind [pluck]

theorem pluck_eq_pair {i : Nat} (hi : i < xs.size) (h_even : xs[i] % 2 = 0)
    (h : ∀ (j : Nat) (hj : j < xs.size), xs[j] % 2 = 1 ∨ xs[i] ≤ xs[j])
    (h' : ∀ (j : Nat) (hj : j < i), xs[j] % 2 = 1 ∨ xs[i] < xs[j]) :
    pluck xs = [xs[i], i] := by
  rw [pluck]
  split
  · rename_i j heq
    simp only [Option.eq_some_iff_get_eq, List.get_minIdxOn?_eq_minIdxOn] at heq
    conv at heq => congr; ext; rw [List.minIdxOn_eq_iff (by grind)]
    simp only [LE.le, compare_lexOrd_eq, Ordering.isLE_then_iff_and,
      Std.isLE_compare (α := Bool)] at heq
    suffices i = j by grind
    apply Nat.le_antisymm <;> grind [Std.compare_eq_lt, Std.isLE_compare]
  · grind [List.minIdxOn?_eq_if, Array.toList_eq_nil_iff]

/-!
## Prompt

```python3

def pluck(arr):
    """
    "Given an array representing a branch of a tree that has non-negative integer nodes
    your task is to pluck one of the nodes and return it.
    The plucked node should be the node with the smallest even value.
    If multiple nodes with the same smallest even value are found return the node that has smallest index.

    The plucked node should be returned in a list, [ smalest_value, its index ],
    If there are no even values or the given array is empty, return [].

    Example 1:
        Input: [4,2,3]
        Output: [2, 1]
        Explanation: 2 has the smallest even value, and 2 has the smallest index.

    Example 2:
        Input: [1,2,3]
        Output: [2, 1]
        Explanation: 2 has the smallest even value, and 2 has the smallest index.

    Example 3:
        Input: []
        Output: []

    Example 4:
        Input: [5, 0, 3, 0, 4, 2]
        Output: [0, 1]
        Explanation: 0 is the smallest value, but  there are two zeros,
                     so we will choose the first zero, which has the smallest index.

    Constraints:
        * 1 <= nodes.length <= 10000
        * 0 <= node.value
    """
```

## Canonical solution

```python3
    if(len(arr) == 0): return []
    evens = list(filter(lambda x: x%2 == 0, arr))
    if(evens == []): return []
    return [min(evens), arr.index(min(evens))]
```

## Tests

```python3
def check(candidate):

    # Check some simple cases
    assert True, "This prints if this assert fails 1 (good for debugging!)"
    assert candidate([4,2,3]) == [2, 1], "Error"
    assert candidate([1,2,3]) == [2, 1], "Error"
    assert candidate([]) == [], "Error"
    assert candidate([5, 0, 3, 0, 4, 2]) == [0, 1], "Error"

    # Check some edge cases that are easy to work out by hand.
    assert True, "This prints if this assert fails 2 (also good for debugging!)"
    assert candidate([1, 2, 3, 0, 5, 3]) == [0, 3], "Error"
    assert candidate([5, 4, 8, 4 ,8]) == [4, 1], "Error"
    assert candidate([7, 6, 7, 1]) == [6, 1], "Error"
    assert candidate([7, 9, 7, 1]) == [], "Error"

```
-/
