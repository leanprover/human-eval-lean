import Std.Tactic.Do
open Std.Do

#check List.min

def Array.minD [Min α] (xs : Array α) (fallback : α) : α :=
    xs.toList.min?.getD fallback

attribute [grind =] Array.toList_mkSlice_rco Array.toList_mkSlice_rci

@[simp, grind =]
theorem Array.minD_empty [Min α] {fallback : α} :
    (#[] : Array α).minD fallback = fallback := by
  simp [Array.minD]

def minSubarraySum (xs : Array Int) : Int := Id.run do
    let mut minSum := 0
    let mut s := 0
    for num in xs do
        s := min 0 (s + num)
        minSum := min s minSum
    if minSum < 0 then
        return minSum
    else
        return xs.minD 0

@[simp, grind =]
theorem minSubarraySum_empty : minSubarraySum #[] = 0 := by simp [minSubarraySum]

def IsMinSubarraySum₀ (xs : Array Int) (s : Int) : Prop :=
  (∃ (i j : Nat), i ≤ j ∧ j ≤ xs.size ∧ s = xs[i...j].toList.sum) ∧
    (∀ (i j : Nat), i ≤ j → j ≤ xs.size → s ≤ xs[i...j].toList.sum)

def IsMinSuffixSum₀ (xs : Array Int) (s : Int) : Prop :=
  (∃ (i : Nat), i ≤ xs.size ∧ s = xs[i...*].toList.sum) ∧
    (∀ (i : Nat), i ≤ xs.size → s ≤ xs[i...*].toList.sum)

def IsMinSubarraySum (xs : Array Int) (s : Int) : Prop :=
  if xs = #[] then s = 0 else
    (∃ (i j : Nat), i < j ∧ j ≤ xs.size ∧ s = xs[i...j].toList.sum) ∧
      (∀ (i j : Nat), i < j → j ≤ xs.size → s ≤ xs[i...j].toList.sum)

@[simp, grind .]
theorem isMinSubarraySum₀_empty :
    IsMinSubarraySum₀ #[] 0 :=
  ⟨⟨0, 0, by grind, by grind, by grind⟩, fun i j hi hj => by grind⟩

@[simp, grind .]
theorem isMinSuffixSum₀_empty :
    IsMinSuffixSum₀ #[] 0 :=
  ⟨⟨0, by grind, by grind⟩, fun i hi => by grind⟩

@[simp, grind .]
theorem isMinSubarraySum_empty :
    IsMinSubarraySum #[] 0 := by
  grind [IsMinSubarraySum]

@[grind ←, grind →]
theorem isMinSubarraySum_of_isMinSubarraySum₀_of_neg {xs : Array Int} {s : Int} (hs : s < 0) :
    IsMinSubarraySum₀ xs s → IsMinSubarraySum xs s := by
  grind [IsMinSubarraySum, IsMinSubarraySum₀, List.drop_take_self]

theorem isMinSubarraySum_minSubarraySum {xs : Array Int} :
    IsMinSubarraySum xs (minSubarraySum xs) := by
  generalize hwp : minSubarraySum xs = w
  apply Std.Do.Id.of_wp_run_eq hwp
  mvcgen
  case inv1 => exact .noThrow fun ⟨cursor, minSum, minSuff⟩ =>
      ⌜IsMinSubarraySum₀ cursor.prefix.toArray minSum ∧
        IsMinSuffixSum₀ cursor.prefix.toArray minSuff⌝
  · mleave
    simp +zetaDelta
    sorry -- heavy lifting here
  · grind
  · simp only [Array.toArray_toList] at * -- Why? `Array.toArray_toList` is `grind =`-annotated.
    grind
  · mleave
    simp_all
    sorry


/-!
## Prompt

```python3

def minSubArraySum(nums):
    """
    Given an array of integers nums, find the minimum sum of any non-empty sub-array
    of nums.
    Example
    minSubArraySum([2, 3, 4, 1, 2, 4]) == 1
    minSubArraySum([-1, -2, -3]) == -6
    """
```

## Canonical solution

```python3
    max_sum = 0
    s = 0
    for num in nums:
        s += -num
        if (s < 0):
            s = 0
        max_sum = max(s, max_sum)
    if max_sum == 0:
        max_sum = max(-i for i in nums)
    min_sum = -max_sum
    return min_sum
```

## Tests

```python3
def check(candidate):

    # Check some simple cases
    assert candidate([2, 3, 4, 1, 2, 4]) == 1, "This prints if this assert fails 1 (good for debugging!)"
    assert candidate([-1, -2, -3]) == -6
    assert candidate([-1, -2, -3, 2, -10]) == -14
    assert candidate([-9999999999999999]) == -9999999999999999
    assert candidate([0, 10, 20, 1000000]) == 0
    assert candidate([-1, -2, -3, 10, -5]) == -6
    assert candidate([100, -1, -2, -3, 10, -5]) == -6
    assert candidate([10, 11, 13, 8, 3, 4]) == 3
    assert candidate([100, -33, 32, -1, 0, -2]) == -33

    # Check some edge cases that are easy to work out by hand.
    assert candidate([-10]) == -10, "This prints if this assert fails 2 (also good for debugging!)"
    assert candidate([7]) == 7
    assert candidate([1, -1]) == -1
```
-/
