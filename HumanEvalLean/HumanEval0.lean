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

namespace Array

def MergeSort.merge (xs ys : Array α) (le : α → α → Bool := by exact (· ≤ ·)) : Array α :=
  if hxs : 0 < xs.size then
    if hys : 0 < ys.size then
      go xs[*...*] ys[*...*] (by simp only [Array.size_mkSlice_rii]; omega) (by simp only [Array.size_mkSlice_rii]; omega) (Array.emptyWithCapacity (xs.size + ys.size))
    else
      xs
  else
    ys
where
  go (xs ys : Subarray α) (hxs : 0 < xs.size) (hys : 0 < ys.size) (acc : Array α) : Array α :=
    let x := xs[0]
    let y := ys[0]
    if le x y then
      if hi : 1 < xs.size then
        go (xs.drop 1) ys (by simp only [Subarray.size_drop]; omega) hys (acc.push x)
      else
        ys.foldl (init := acc.push x) (fun acc y => acc.push y)
    else
      if hj : 1 < ys.size then
        go xs (ys.drop 1) hxs (by simp only [Subarray.size_drop]; omega) (acc.push y)
      else
        xs.foldl (init := acc.push y) (fun acc x => acc.push x)
  termination_by xs.size + ys.size

def _root_.Subarray.mergeSort (xs : Subarray α) (le : α → α → Bool := by exact (· ≤ ·)) : Array α :=
    if h : 1 < xs.size then
      let splitIdx := (xs.size + 1) / 2 -- We follow the same splitting convention as `List.mergeSort`
      let left := xs[*...splitIdx]
      let right := xs[splitIdx...*]
      MergeSort.merge (mergeSort left le) (mergeSort right le) le
    else
      xs
termination_by xs.size
decreasing_by
  · simp only [Subarray.size_mkSlice_rio]; omega
  · simp only [Subarray.size_mkSlice_rci]; omega

def mergeSort (xs : Array α) (le : α → α → Bool := by exact (· ≤ ·)) : Array α :=
    xs[*...*].mergeSort le

end Array

theorem Array.MergeSort.merge.go_eq_listMerge {xs ys : Subarray α} {hxs hys le acc} :
    (Array.MergeSort.merge.go le xs ys hxs hys acc).toList = acc.toList ++ List.merge xs.toList ys.toList le := by
  fun_induction Array.MergeSort.merge.go le xs ys hxs hys acc
  · rename_i xs ys _ _ _ _ _ _ _ _
    rw [List.merge.eq_def]
    split
    · have : xs.size = 0 := by simp [← Subarray.length_toList, *]
      omega
    · have : ys.size = 0 := by simp [← Subarray.length_toList, *]
      omega
    · rename_i x' xs' y' ys' _ _
      simp +zetaDelta only at *
      have h₁ : x' = xs[0] := by simp [Subarray.getElem_eq_getElem_toList, *]
      have h₂ : y' = ys[0] := by simp [Subarray.getElem_eq_getElem_toList, *]
      cases h₁
      cases h₂
      simp [Subarray.toList_drop, *]
  · rename_i xs ys _ _ _ _ _ _ _
    rw [List.merge.eq_def]
    split
    · have : xs.size = 0 := by simp [← Subarray.length_toList, *]
      omega
    · have : ys.size = 0 := by simp [← Subarray.length_toList, *]
      omega
    · rename_i x' xs' y' ys' _ _
      simp +zetaDelta only at *
      have h₁ : x' = xs[0] := by simp [Subarray.getElem_eq_getElem_toList, *]
      have h₂ : y' = ys[0] := by simp [Subarray.getElem_eq_getElem_toList, *]
      cases h₁
      cases h₂
      simp [*]
      have : xs.size = xs'.length + 1 := by simp [← Subarray.length_toList, *]
      have : xs' = [] := List.eq_nil_of_length_eq_zero (by omega)
      simp [this]
      rw [← Subarray.foldl_toList]
      simp [*]
  · rename_i xs ys _ _ _ _ _ _ _ _
    rw [List.merge.eq_def]
    split
    · have : xs.size = 0 := by simp [← Subarray.length_toList, *]
      omega
    · have : ys.size = 0 := by simp [← Subarray.length_toList, *]
      omega
    · rename_i x' xs' y' ys' _ _
      simp +zetaDelta only at *
      have h₁ : x' = xs[0] := by simp [Subarray.getElem_eq_getElem_toList, *]
      have h₂ : y' = ys[0] := by simp [Subarray.getElem_eq_getElem_toList, *]
      cases h₁
      cases h₂
      simp [Subarray.toList_drop, *]
  · rename_i xs ys _ _ _ _ _ _ _
    rw [List.merge.eq_def]
    split
    · have : xs.size = 0 := by simp [← Subarray.length_toList, *]
      omega
    · have : ys.size = 0 := by simp [← Subarray.length_toList, *]
      omega
    · rename_i x' xs' y' ys' _ _
      simp +zetaDelta only at *
      have h₁ : x' = xs[0] := by simp [Subarray.getElem_eq_getElem_toList, *]
      have h₂ : y' = ys[0] := by simp [Subarray.getElem_eq_getElem_toList, *]
      cases h₁
      cases h₂
      simp [*]
      have : ys.size = ys'.length + 1 := by simp [← Subarray.length_toList, *]
      have : ys' = [] := List.eq_nil_of_length_eq_zero (by omega)
      simp [this]
      rw [← Subarray.foldl_toList]
      simp [*]

theorem Array.MergeSort.merge_eq_listMerge {xs ys : Array α} {le} :
    (Array.MergeSort.merge xs ys le).toList = List.merge xs.toList ys.toList le := by
  rw [Array.MergeSort.merge]
  split <;> rename_i heq₁
  · split <;> rename_i heq₂
    · simp [Array.MergeSort.merge.go_eq_listMerge]
    · have : ys.toList = [] := by simp_all
      simp [this]
  · have : xs.toList = [] := by simp_all
    simp [this]

theorem List.mergeSort_eq_merge_mkSlice {xs : List α} :
    xs.mergeSort le =
      if 1 < xs.length then
        merge (xs[*...((xs.length + 1) / 2)].toList.mergeSort le) (xs[((xs.length + 1) / 2)...*].toList.mergeSort le) le
      else
        xs := by
  fun_cases xs.mergeSort le
  · simp
  · simp
  · rename_i x y ys lr hl hr
    simp [lr]

theorem Subarray.toList_mergeSort {xs : Subarray α} {le : α → α → Bool} :
    (xs.mergeSort le).toList = xs.toList.mergeSort le := by
  fun_induction xs.mergeSort le
  · rw [List.mergeSort_eq_merge_mkSlice]
    simp +zetaDelta [Array.MergeSort.merge_eq_listMerge, *]
  · simp [List.mergeSort_eq_merge_mkSlice, *]

theorem Array.toList_mergeSort {xs : Array α} {le : α → α → Bool} :
    (xs.mergeSort le).toList = xs.toList.mergeSort le := by
  rw [Array.mergeSort, Subarray.toList_mergeSort, Array.toList_mkSlice_rii]

theorem Nat.eq_add_of_toList_rio_eq_append_cons {a : Nat} {pref cur suff}
    (h : (*...a).toList = pref ++ cur :: suff) :
    cur = pref.length := by
  have := Rio.eq_succMany?_of_toList_eq_append_cons h
  simpa [PRange.UpwardEnumerable.least, PRange.least?] using this

@[simp, grind =]
theorem Array.size_mergeSort {xs : Array α} :
    (xs.mergeSort le).size = xs.size := by
  rw [← length_toList, Array.toList_mergeSort, List.length_mergeSort, length_toList]

theorem Array.mergeSort_perm {xs : Array α} :
    (xs.mergeSort le).Perm xs := by
  simpa only [perm_iff_toList_perm, Array.toList_mergeSort] using List.mergeSort_perm _ _

theorem Array.pairwise_mergeSort
    (trans : ∀ (a b c : α), le a b → le b c → le a c)
    (total : ∀ (a b : α), le a b || le b a) :
    (l : Array α) → (mergeSort l le).toList.Pairwise (le · ·) := by
  intro xs
  simpa [toList_mergeSort] using List.pairwise_mergeSort trans total _

attribute [simp, grind =] Rio.mem_iff

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

example : hasCloseElements #[1.0, 2.0, 3.9, 4.0, 5.0, 2.2] 0.3 = true := by native_decide
example : hasCloseElements #[1.0, 2.0, 3.9, 4.0, 5.0, 2.2] 0.05 = false := by native_decide
example : hasCloseElements #[1.0, 2.0, 5.9, 4.0, 5.0] 0.95 = true := by native_decide
example : hasCloseElements #[1.0, 2.0, 5.9, 4.0, 5.0] 0.8 = false := by native_decide
example : hasCloseElements #[1.0, 2.0, 3.0, 4.0, 5.0, 2.0] 0.1 = true := by native_decide
example : hasCloseElements #[1.1, 2.2, 3.1, 4.1, 5.1] 1.0 = true := by native_decide
example : hasCloseElements #[1.1, 2.2, 3.1, 4.1, 5.1] 0.5 = false := by native_decide

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
