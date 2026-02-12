module

public section
open Std

/-! ## Implementation -/

def rescaleToUnit (xs : Array Rat) (h : xs ≠ #[] := by grind) : Array Rat :=
  let minNumber := xs.min h
  let maxNumber := xs.max h
  xs.map (fun x => (x - minNumber) / (maxNumber - minNumber))

/-! ## Tests -/

example : rescaleToUnit #[2.0, 49.9] = #[0.0, 1.0] := by native_decide
example : rescaleToUnit #[100.0, 49.9] = #[1.0, 0.0] := by native_decide
example : rescaleToUnit #[1.0, 2.0, 3.0, 4.0, 5.0] = #[0.0, 0.25, 0.5, 0.75, 1.0] := by native_decide
example : rescaleToUnit #[2.0, 1.0, 5.0, 3.0, 4.0] = #[0.25, 0.0, 1.0, 0.5, 0.75] := by native_decide
example : rescaleToUnit #[12.0, 11.0, 15.0, 13.0, 14.0] = #[0.25, 0.0, 1.0, 0.5, 0.75] := by native_decide

/-! ## Missing API -/

namespace Rat

instance : LawfulOrderInf Rat where le_min_iff := by grind
instance : LawfulOrderSup Rat where max_le_iff := by grind

@[simp]
theorem div_zero {x : Rat} : x / 0 = 0 := by grind

theorem div_le_iff_le_mul {x y z : Rat} (h' : 0 < y) : x / y ≤ z ↔ x ≤ z * y := by
  rw [← Rat.not_lt, Rat.lt_div_iff (by grind)]
  grind

theorem div_nonneg_of_nonneg_of_nonneg (x y : Rat) (h : 0 ≤ x) (h' : 0 ≤ y) : 0 ≤ x / y := by
  by_cases y = 0
  · simp_all [Rat.div_zero]
  · rw [← Rat.not_lt, Rat.div_lt_iff (by grind)]
    grind

end Rat

/-! ## Verification -/

def IsAdmissible (xs : Array Rat) : Prop :=
  ∃ (i j : Nat) (hi : i < xs.size) (hj : j < xs.size), xs[i] < xs[j]

@[grind →]
theorem two_le_size_of_isAdmissible {xs : Array Rat} (h : IsAdmissible xs) :
    2 ≤ xs.size := by
  grind [IsAdmissible]

@[grind →]
theorem min_lt_max_of_isAdmissible {xs : Array Rat} (h : IsAdmissible xs) :
    xs.min (by grind) < xs.max (by grind) := by
  have (i : Nat) (hi : i < xs.size) : xs.min (by grind) ≤ xs[i] := by grind
  have (i : Nat) (hi : i < xs.size) : xs[i] ≤ xs.max (by grind)  := by grind
  grind [IsAdmissible]

@[simp, grind =]
theorem size_rescaleToUnit {xs : Array Rat} {h} :
    (rescaleToUnit xs h).size = xs.size := by
  grind [rescaleToUnit]

theorem getElem_rescaleToUnit {xs : Array Rat} {i : Nat} {h} {h' : i < (rescaleToUnit xs h).size} :
    (rescaleToUnit xs h)[i] =
      (xs[i]'(by simpa using h') - xs.min (by grind)) / (xs.max (by grind) - xs.min (by grind)) := by
  grind [rescaleToUnit]

theorem rescaleToUnit_affine {xs : Array Rat} {i j k : Nat} {h}
    (hi : i < (rescaleToUnit xs h).size) (hj : j < (rescaleToUnit xs h).size)
    (hk : k < (rescaleToUnit xs h).size) (h' : IsAdmissible xs) :
    ((rescaleToUnit xs h)[i] - (rescaleToUnit xs h)[k]) / ((rescaleToUnit xs h)[j] - (rescaleToUnit xs h)[k]) =
      (xs[i]'(by grind) - xs[k]'(by grind)) / (xs[j]'(by grind) - xs[k]'(by grind)) := by
  grind [getElem_rescaleToUnit]

theorem zero_mem_rescaleToUnit {xs : Array Rat} {h : 2 ≤ xs.size} :
    0 ∈ rescaleToUnit xs := by
  simp only [rescaleToUnit, Array.mem_map]
  exact ⟨xs.min (by grind), by grind [Array.min_mem]⟩

theorem one_mem_rescaleToUnit {xs : Array Rat} (h : IsAdmissible xs) :
    1 ∈ rescaleToUnit xs := by
  simp only [rescaleToUnit, Array.mem_map]
  exact ⟨xs.max (by grind), by grind [Array.max_mem]⟩

theorem zero_le_of_mem {xs : Array Rat} {x : Rat} (h : IsAdmissible xs) (h : x ∈ rescaleToUnit xs) :
    0 ≤ x := by
  simp only [rescaleToUnit, Array.mem_map] at h
  obtain ⟨a, ha, rfl⟩ := h
  have : xs.min (by grind) ≤ a := by grind
  apply Rat.div_nonneg_of_nonneg_of_nonneg <;> grind

theorem le_one_of_mem {xs : Array Rat} {x : Rat} (h : IsAdmissible xs) (h : x ∈ rescaleToUnit xs) :
    x ≤ 1 := by
  simp only [rescaleToUnit, Array.mem_map] at h
  obtain ⟨a, ha, rfl⟩ := h
  have : a ≤ xs.max (by grind) := by grind
  rw [Rat.div_le_iff_le_mul (by grind)]
  grind

theorem min_rescaleToUnit {xs : Array Rat} (h : IsAdmissible xs) :
    (rescaleToUnit xs).min (by grind) = 0 := by
  grind [Array.min_eq_iff, zero_mem_rescaleToUnit, zero_le_of_mem]

theorem max_rescaleToUnit {xs : Array Rat} (h : IsAdmissible xs) :
    (rescaleToUnit xs).max (by grind) = 1 := by
  grind [Array.max_eq_iff, one_mem_rescaleToUnit, le_one_of_mem]

/-!
## Prompt

```python3
from typing import List


def rescale_to_unit(numbers: List[float]) -> List[float]:
    """ Given list of numbers (of at least two elements), apply a linear transform to that list,
    such that the smallest number will become 0 and the largest will become 1
    >>> rescale_to_unit([1.0, 2.0, 3.0, 4.0, 5.0])
    [0.0, 0.25, 0.5, 0.75, 1.0]
    """
```

## Canonical solution

```python3
    min_number = min(numbers)
    max_number = max(numbers)
    return [(x - min_number) / (max_number - min_number) for x in numbers]
```

## Tests

```python3


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    assert candidate([2.0, 49.9]) == [0.0, 1.0]
    assert candidate([100.0, 49.9]) == [1.0, 0.0]
    assert candidate([1.0, 2.0, 3.0, 4.0, 5.0]) == [0.0, 0.25, 0.5, 0.75, 1.0]
    assert candidate([2.0, 1.0, 5.0, 3.0, 4.0]) == [0.25, 0.0, 1.0, 0.5, 0.75]
    assert candidate([12.0, 11.0, 15.0, 13.0, 14.0]) == [0.25, 0.0, 1.0, 0.5, 0.75]
```
-/
