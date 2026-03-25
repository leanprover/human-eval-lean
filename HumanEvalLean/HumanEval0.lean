module

import Std
import all Init.Data.List.Sort.Basic
import all Init.Data.Slice.Array.Lemmas
import all Init.Data.Range.Polymorphic.UpwardEnumerable -- UpwardEnumerable.least not exposed
open Std Std.Do

set_option mvcgen.warning false

/-!
## Missing API
-/

theorem Nat.eq_add_of_toList_rio_eq_append_cons {a : Nat} {pref cur suff}
    (h : (*...a).toList = pref ++ cur :: suff) :
    cur = pref.length := by
  have := Rio.eq_succMany?_of_toList_eq_append_cons h
  simpa [PRange.UpwardEnumerable.least, PRange.least?] using this

/-!
## Implementation
-/

def hasCloseElements (xs : Array Rat) (threshold : Rat) : Bool := Id.run do
  let sorted := xs.mergeSort
  for h : i in *...(sorted.size - 1) do
    if (sorted[i + 1] - sorted[i]).abs < threshold then
      return true
  return false

/-!
## Tests
-/

example : hasCloseElements #[1.0, 2.0, 3.9, 4.0, 5.0, 2.2] 0.3 = true := by cbv
example : hasCloseElements #[1.0, 2.0, 3.9, 4.0, 5.0, 2.2] 0.05 = false := by cbv
example : hasCloseElements #[1.0, 2.0, 5.9, 4.0, 5.0] 0.95 = true := by cbv
example : hasCloseElements #[1.0, 2.0, 5.9, 4.0, 5.0] 0.8 = false := by cbv
example : hasCloseElements #[1.0, 2.0, 3.0, 4.0, 5.0, 2.0] 0.1 = true := by cbv
example : hasCloseElements #[1.1, 2.2, 3.1, 4.1, 5.1] 1.0 = true := by cbv
example : hasCloseElements #[1.1, 2.2, 3.1, 4.1, 5.1] 0.5 = false := by cbv

/-!
## Verification
-/

theorem hasCloseElements_iff_mergeSort {xs threshold} :
    hasCloseElements xs threshold ↔ ∃ (i : Nat) (_ : i < xs.mergeSort.size - 1), (xs.mergeSort[i + 1] - xs.mergeSort[i]).abs < threshold := by
  generalize hwp : hasCloseElements xs threshold = wp
  apply Id.of_wp_run_eq hwp
  mvcgen
  invariants
  · .withEarlyReturn
      (fun cur _ => ⌜∀ i < cur.prefix.length, threshold ≤ (xs.mergeSort[i + 1]! - xs.mergeSort[i]!).abs⌝)
      (fun r _ => ⌜r = true ∧ ∃ (i : Nat) (_ : i < xs.mergeSort.size - 1), (xs.mergeSort[i + 1] - xs.mergeSort[i]).abs < threshold⌝)
  with grind [Nat.eq_add_of_toList_rio_eq_append_cons, Rio.length_toList, Nat.size_rio]

theorem hasCloseElements_iff {xs threshold} :
    hasCloseElements xs threshold ↔ ¬ xs.toList.Pairwise (fun a b => threshold ≤ (b - a).abs) := by
  simp only [hasCloseElements_iff_mergeSort]
  have := xs.mergeSort_perm (le := (· ≤ ·))
  rw [← this.pairwise_iff]
  · apply Iff.intro
    · simp only [List.pairwise_iff_getElem, Classical.not_forall]
      grind
    · simp only [List.pairwise_iff_getElem, Classical.not_forall]
      rintro ⟨i, j, hi, hj, hij, h⟩
      refine ⟨i, by grind, ?_⟩
      have h_sorted := xs.pairwise_mergeSort (le := (· ≤ ·)) (by grind) (by grind)
      rw [List.pairwise_iff_getElem] at h_sorted
      rw [Rat.abs_of_nonneg (by grind)] at ⊢ h
      have : xs.mergeSort[i + 1]'(by grind) ≤ xs.mergeSort[j] := by by_cases i + 1 = j <;> grind
      grind
  · simp [Rat.abs_sub_comm]

/-!
## Prompt

```python3
from typing import List


def has_close_elements(numbers: List[float], threshold: float) -> bool:
    """ Check if in given list of numbers, are any two numbers closer to each other than
    given threshold.
    >>> has_close_elements([1.0, 2.0, 3.0], 0.5)
    False
    >>> has_close_elements([1.0, 2.8, 3.0, 4.0, 5.0, 2.0], 0.3)
    True
    """
```

## Canonical solution

```python3
    for idx, elem in enumerate(numbers):
        for idx2, elem2 in enumerate(numbers):
            if idx != idx2:
                distance = abs(elem - elem2)
                if distance < threshold:
                    return True

    return False
```

## Tests

```python3


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    assert candidate([1.0, 2.0, 3.9, 4.0, 5.0, 2.2], 0.3) == True
    assert candidate([1.0, 2.0, 3.9, 4.0, 5.0, 2.2], 0.05) == False
    assert candidate([1.0, 2.0, 5.9, 4.0, 5.0], 0.95) == True
    assert candidate([1.0, 2.0, 5.9, 4.0, 5.0], 0.8) == False
    assert candidate([1.0, 2.0, 3.0, 4.0, 5.0, 2.0], 0.1) == True
    assert candidate([1.1, 2.2, 3.1, 4.1, 5.1], 1.0) == True
    assert candidate([1.1, 2.2, 3.1, 4.1, 5.1], 0.5) == False

```
-/
