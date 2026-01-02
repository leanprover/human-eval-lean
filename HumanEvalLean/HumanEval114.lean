import Std.Tactic.Do
open Std.Do
set_option mvcgen.warning false

/-!
## Implementation
-/

@[grind]
def Array.minD [Min α] (xs : Array α) (fallback : α) : α :=
  xs.toList.min?.getD fallback

@[grind]
def List.minD [Min α] (xs : List α) (fallback : α) : α :=
  xs.min?.getD fallback

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

/-!
## Tests
-/

example : minSubarraySum #[2, 3, 4, 1, 2, 4] = 1 := by decide
example : minSubarraySum #[-1, -2, -3] = -6 := by decide
example : minSubarraySum #[-1, -2, -3, 2, -10] = -14 := by decide
example : minSubarraySum #[-9999999999999999] = -9999999999999999 := by decide
example : minSubarraySum #[0, 10, 20, 1000000] = 0 := by decide
example : minSubarraySum #[-1, -2, -3, 10, -5] = -6 := by decide
example : minSubarraySum #[100, -1, -2, -3, 10, -5] = -6 := by decide
example : minSubarraySum #[10, 11, 13, 8, 3, 4] = 3 := by decide
example : minSubarraySum #[100, -33, 32, -1, 0, -2] = -33 := by decide
example : minSubarraySum #[-10] = -10 := by decide
example : minSubarraySum #[7] = 7 := by decide
example : minSubarraySum #[1, -1] = -1 := by decide

-- This edge case is unspecified in the task description.
example : minSubarraySum #[] = 0 := by decide

/-!
## Verification
-/

/-!
### Missing API
-/

attribute [grind =] List.toList_mkSlice_rco List.toList_mkSlice_rci List.le_min_iff
attribute [grind →] List.mem_of_mem_take List.mem_of_mem_drop

@[simp, grind =]
theorem Array.minD_empty [Min α] {fallback : α} :
    (#[] : Array α).minD fallback = fallback := by
  simp [Array.minD]

@[simp, grind =]
theorem List.minD_nil [Min α] {fallback : α} :
    ([] : List α).minD fallback = fallback := by
  simp [List.minD]

@[simp, grind =]
theorem List.sum_append_int {l₁ l₂ : List Int} : (l₁ ++ l₂).sum = l₁.sum + l₂.sum := by
  induction l₁ generalizing l₂ <;> simp_all [Int.add_assoc]

/-!
### Helper lemmas
-/

@[simp, grind =]
theorem minSubarraySum_empty : minSubarraySum #[] = 0 := by simp [minSubarraySum]

/--
`s` is the minimum sum of every possibly empty subarray of `xs`.
-/
def IsMinSubarraySum₀ (xs : List Int) (s : Int) : Prop :=
  (∃ (i j : Nat), i ≤ j ∧ j ≤ xs.length ∧ s = xs[i...j].toList.sum) ∧
    (∀ (i j : Nat), i ≤ j → j ≤ xs.length → s ≤ xs[i...j].toList.sum)

/--
`s` is the minimum sum of every possibly empty suffix of `xs`.
-/
def IsMinSuffixSum₀ (xs : List Int) (s : Int) : Prop :=
  (∃ (i : Nat), i ≤ xs.length ∧ s = xs[i...*].toList.sum) ∧
    (∀ (i : Nat), i ≤ xs.length → s ≤ xs[i...*].toList.sum)

/--
`s` is the minimum sum of every nonempty subarray of `xs`.
-/
def IsMinSubarraySum (xs : List Int) (s : Int) : Prop :=
  if xs = [] then s = 0 else
    (∃ (i j : Nat), i < j ∧ j ≤ xs.length ∧ s = xs[i...j].toList.sum) ∧
      (∀ (i j : Nat), i < j → j ≤ xs.length → s ≤ xs[i...j].toList.sum)

@[simp, grind .]
theorem isMinSubarraySum₀_nil :
    IsMinSubarraySum₀ [] 0 :=
  ⟨⟨0, 0, by grind, by grind, by grind⟩, fun i j hi hj => by grind⟩

@[simp, grind .]
theorem isMinSuffixSum₀_nil :
    IsMinSuffixSum₀ [] 0 :=
  ⟨⟨0, by grind, by grind⟩, fun i hi => by grind⟩

@[grind →]
theorem isMinSubarraySum₀_le_zero {xs : List Int} {s : Int} :
    IsMinSubarraySum₀ xs s → s ≤ 0 := by
  intro h
  have := h.2 0 0
  grind [IsMinSubarraySum₀]

theorem isMinSuffixSum₀_le_zero {xs : List Int} {s : Int} :
    IsMinSuffixSum₀ xs s → s ≤ 0 := by
  intro h
  have := h.2 xs.length
  grind [IsMinSuffixSum₀]

@[grind ←, grind →]
theorem isMinSubarraySum_of_isMinSubarraySum₀_of_neg {xs : List Int} {s : Int} (hs : s < 0) :
    IsMinSubarraySum₀ xs s → IsMinSubarraySum xs s := by
  grind [IsMinSubarraySum, IsMinSubarraySum₀, List.drop_take_self]

@[grind =>]
theorem isMinSubarraySum₀_append_singleton_eq {xs : List Int} {x minSum minSuff : Int}
    (h₁ : IsMinSubarraySum₀ xs minSum) (h₂ : IsMinSuffixSum₀ xs minSuff) :
    IsMinSubarraySum₀ (xs ++ [x]) (min (min 0 (minSuff + x)) minSum) := by
  have : min (min 0 (minSuff + x)) minSum = min (minSuff + x) minSum := by grind
  rw [this]
  by_cases h : minSum ≤ minSuff + x
  · rw [show min (minSuff + x) minSum = minSum by grind]
    apply And.intro
    · grind [IsMinSubarraySum₀, List.take_append_of_le_length]
    · intro i j hi hj
      simp only [List.toList_mkSlice_rco]
      by_cases heq : j = (xs ++ [x]).length
      · by_cases hieq : i = (xs ++ [x]).length
        · grind
        · simp only [heq, List.take_length]
          rw [List.drop_append_of_le_length (by grind), List.sum_append_int]
          have := h₂.2 i
          grind
      · rw [List.take_append_of_le_length (by grind)]
        have := h₁.2 i j hi
        grind
  · rw [show min (minSuff + x) minSum = minSuff + x by grind]
    apply And.intro
    · obtain ⟨i, hi, h₂₁⟩ := h₂.1
      exact ⟨i, xs.length + 1, by grind, by grind, by grind⟩
    · intro i j hi hj
      by_cases heq : j = (xs ++ [x]).length
      · by_cases hieq : i = (xs ++ [x]).length
        · grind
        · simp only [heq, List.toList_mkSlice_rco, List.take_length]
          have := h₂.2 i (by grind)
          grind [List.drop_append_of_le_length]
      · have := h₁.2 i j (by grind) (by grind)
        grind [List.take_append_of_le_length]

@[grind =>]
theorem isMinSuffixSum₀_append_singleton_eq {xs : List Int} {x minSuff : Int}
    (h : IsMinSuffixSum₀ xs minSuff) :
    IsMinSuffixSum₀ (xs ++ [x]) (min 0 (minSuff + x)) := by
  by_cases hle : 0 ≤ minSuff + x
  · rw [show min 0 (minSuff + x) = 0 by grind]
    apply And.intro
    · refine ⟨xs.length + 1, by grind, ?_⟩
      simp only [List.toList_mkSlice_rci, List.drop_length_add_append]
      grind
    · intro i hi
      by_cases hieq : i = (xs ++ [x]).length
      · grind
      · simp only [IsMinSuffixSum₀] at h
        grind [List.drop_append_of_le_length]
  · rw [show min 0 (minSuff + x) = minSuff + x by grind]
    apply And.intro
    · simp only [IsMinSuffixSum₀] at h
      grind [List.drop_append_of_le_length]
    · intro i hi
      by_cases hieq : i = (xs ++ [x]).length
      · grind
      · simp only [IsMinSuffixSum₀] at h
        grind [List.drop_append_of_le_length]

theorem List.zero_le_min_of_zero_le_sum {xs : List Int} (hne : xs ≠ []) (h : xs.sum ≤ 0) :
    xs.min hne ≤ 0 := by
  induction xs
  · grind
  · rename_i x xs ih
    cases xs
    · simp_all [List.min_eq_get_min?]
    · grind [min?_cons, min_eq_get_min?]

theorem List.length_mul_le_sum {xs : List Int} {m : Int} (h : ∀ x, x ∈ xs → m ≤ x) :
    xs.length * m ≤ xs.sum := by
  induction xs
  · grind
  · rename_i x xs ih
    simp only [mem_cons, forall_eq_or_imp, length_cons] at *
    grind

theorem this_should_not_be_so_hard (a : Int) (b : Nat) (h : 0 ≤ a) (h' : 0 < b) :
    a ≤ b * a := by
  match b with
  | 0 => grind
  | b + 1 =>
    induction b <;> grind

@[grind →, grind <=]
theorem isMinSubarraySum_of_nonneg {xs : List Int} {minSum : Int}
    (h : IsMinSubarraySum₀ xs minSum)  (hs : minSum ≥ 0) :
    IsMinSubarraySum xs (xs.minD 0) := by
  rw [IsMinSubarraySum]
  split
  · simp [*]
  · have : minSum = 0 := by grind
    have := this
    rw [List.minD, List.min?_eq_some_min (by grind), Option.getD_some]
    have hmin : xs.min (by grind) = xs.min (by grind) := rfl
    rw [List.min_eq_iff, List.mem_iff_getElem] at hmin
    have : 0 ≤ xs.min (by grind) := by
      false_or_by_contra
      obtain ⟨i, _, hi⟩ := hmin.1
      have := h.2 i (i + 1) (by grind) (by grind)
      simp only [List.toList_mkSlice_rco, List.take_add_one] at this
      grind
    apply And.intro
    · obtain ⟨i, _, hi⟩ := hmin.1
      exact ⟨i, i + 1, by grind, by grind, by grind [List.take_add_one]⟩
    · intro i j hi hj
      have : ∀ a, a ∈ (xs.take j).drop i → xs.min (by grind) ≤ a := by grind
      have := List.length_mul_le_sum this
      simp only [List.toList_mkSlice_rco, *]
      refine Int.le_trans ?_ this
      simp only [List.length_drop, List.length_take]
      apply this_should_not_be_so_hard <;> grind

/-!
### Final theorems
-/

theorem isMinSubarraySum_minSubarraySum {xs : Array Int} :
    IsMinSubarraySum xs.toList (minSubarraySum xs) := by
  generalize hwp : minSubarraySum xs = w
  apply Std.Do.Id.of_wp_run_eq hwp
  mvcgen
  case inv1 => exact .noThrow fun ⟨cursor, minSum, minSuff⟩ =>
      ⌜IsMinSubarraySum₀ cursor.prefix minSum ∧
        IsMinSuffixSum₀ cursor.prefix minSuff⌝
  all_goals grind

theorem isMinSubarraySum_nil :
    IsMinSubarraySum [] 0 := by
  grind [IsMinSubarraySum]

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
