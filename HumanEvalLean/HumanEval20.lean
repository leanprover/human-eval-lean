module

public import Std
import all Init.Data.Range.Polymorphic.UpwardEnumerable

open Std Std.Do
set_option mvcgen.warning false

public section

/-! ## Implementation -/

/--
`O(n log n)`. Returns a pair of elements in `xs` with the least possible distance, sorted in
increasing order.
-/
def findClosestElements (xs : Array Rat) (h : 2 ≤ xs.size := by grind) : Rat × Rat := Id.run do
  let sorted := xs.toList.mergeSort.toArray
  have : 2 ≤ sorted.size := by grind [List.length_mergeSort]
  let mut closest := (sorted[0], sorted[1])
  for hi : i in 1...(sorted.size - 1) do
    if (sorted[i + 1] - sorted[i]).abs < (closest.2 - closest.1).abs then
      closest := (sorted[i], sorted[i + 1])
  return closest

/-! ## Tests -/

example : findClosestElements #[(1.0 : Rat), 2.0, 3.9, 4.0, 5.0, 2.2] = (3.9, 4.0) := by native_decide
example : findClosestElements #[(1.0 : Rat), 2.0, 5.9, 4.0, 5.0] = (5.0, 5.9) := by native_decide
example : findClosestElements #[(1.0 : Rat), 2.0, 3.0, 4.0, 5.0, 2.2] = (2.0, 2.2) := by native_decide
example : findClosestElements #[(1.0 : Rat), 2.0, 3.0, 4.0, 5.0, 2.0] = (2.0, 2.0) := by native_decide
example : findClosestElements #[(1.1 : Rat), 2.2, 3.1, 4.1, 5.1] = (2.2, 3.1) := by native_decide

/-! ## Missing API -/

-- TODO: As soon as `Array.mergeSort` is merged, use that one.

theorem Nat.eq_add_of_toList_rco_eq_append_cons {a b : Nat} {pref cur suff}
    (h : (a...b).toList = pref ++ cur :: suff) :
    cur = a + pref.length := by
  have := Rco.eq_succMany?_of_toList_eq_append_cons h
  simpa [PRange.UpwardEnumerable.least, PRange.least?] using this

/-! ## Verification -/

/--
The elements of the pair `findClosestElements xs` are in increasing order.
-/
theorem sorted_findClosestElements {xs : Array Rat} {h : 2 ≤ xs.size} :
    (findClosestElements xs).1 ≤ (findClosestElements xs).2 := by
  generalize hwp : findClosestElements xs = wp
  apply Id.of_wp_run_eq hwp
  mvcgen
  invariants
  · ⇓⟨cur, closest⟩ => ⌜closest.1 ≤ closest.2⌝
  case vc1 sorted _ _ _ _ _ _ _ _ _ =>
    have : sorted.toList.Pairwise (· ≤ ·) := by grind [List.pairwise_mergeSort]
    simp only [List.pairwise_iff_getElem] at this
    grind
  case vc3 sorted _ _ =>
    have : sorted.toList.Pairwise (· ≤ ·) := by grind [List.pairwise_mergeSort]
    simp only [List.pairwise_iff_getElem] at this
    grind

/--
The elements of the pair `findClosestElements xs` are located in two distinct positions inside of
`xs`.
-/
theorem exists_mem_findClosestElements {xs : Array Rat} {h : 2 ≤ xs.size} :
    ∃ (i j : Nat) (hi : i < xs.size) (hj : j < xs.size) (_hij : i ≠ j),
      findClosestElements xs = (xs[i], xs[j]) := by
  suffices h' : ¬ xs.toList.mergeSort.Pairwise (fun x y => ¬ (findClosestElements xs = (x, y) ∨  findClosestElements xs = (y, x))) by
    have := xs.toList.mergeSort_perm (· ≤ ·)
    rw [this.pairwise_iff (by grind)] at h'
    grind [List.pairwise_iff_getElem]
  generalize hwp : findClosestElements xs = wp
  apply Id.of_wp_run_eq hwp
  mvcgen
  invariants
  | inv1 sorted _ _ => ⇓⟨cur, closest⟩ => ⌜∃ (i j : Nat) (hi : i < sorted.size) (hj : j < sorted.size) (hij : i ≠ j),
        closest = (sorted[i], sorted[j])⌝
  case vc1 => grind [List.length_mergeSort, List.pairwise_iff_getElem]
  case vc3 => exact ⟨0, 1, by grind⟩
  case vc4 => grind [List.length_mergeSort, List.pairwise_iff_getElem]

/--
This lemma is an intermediate step towards `pairwise_abs_findClosestElements_le`.
It proves a fact that is obvious from the implementation:
The distance of the components of `findClosestElements xs` is less than or equal to the
distance of any two consecutive elements in the *sorted* array.
-/
private theorem abs_findClosestElements_le_mergeSort {xs : Array Rat} {h : 2 ≤ xs.size} :
    letI closest := findClosestElements xs
    letI sorted := xs.toList.mergeSort.toArray
    ∀ (i : Nat) (hi : i + 1 < sorted.size),
      (closest.2 - closest.1).abs ≤ (sorted[i + 1] - sorted[i]).abs := by
  generalize hwp : findClosestElements xs = wp
  apply Id.of_wp_run_eq hwp
  mvcgen
  invariants
  | inv1 sorted _ _ => ⇓⟨cur, closest⟩ => ⌜∀ (i : Nat) (hi : i < cur.pos + 1), (closest.2 - closest.1).abs ≤ (sorted[i + 1]! - sorted[i]!).abs⌝
  case vc1 pref cur suff _ _ _ _ =>
    have := Nat.eq_add_of_toList_rco_eq_append_cons ‹_›
    intro i hi
    by_cases i < cur <;> grind
  case vc2 pref cur suff _ _ _ _ =>
    have := Nat.eq_add_of_toList_rco_eq_append_cons ‹_›
    intro i hi
    by_cases i < cur <;> grind
  case vc3 => grind
  case vc4 h =>
    simp +zetaDelta only [List.getElem!_toArray, List.getElem!_eq_getElem?_getD] at h
    grind [Nat.length_toList_rco]

/--
Optimality lemma:

The distance of elements `x` and `y` of `xs`, where `x` comes strictly before `y` in `xs`,
is at least as large as the distance between the components of `findClosestElements xs`.
-/
theorem pairwise_abs_findClosestElements_le {xs : Array Rat} {h : 2 ≤ xs.size} :
    letI closest := findClosestElements xs
    xs.toList.Pairwise (fun x y => (closest.2 - closest.1).abs ≤ (y - x).abs) := by
  have := xs.toList.mergeSort_perm (· ≤ ·)
  rw [← this.pairwise_iff (by grind [Rat.abs_sub_comm]), List.pairwise_iff_getElem]
  intro i j hi hj hij
  have := abs_findClosestElements_le_mergeSort (xs := xs) (h := h) i (by grind)
  have h_sorted := xs.toList.pairwise_mergeSort (le := (· ≤ ·)) (by grind) (by grind)
  grind [List.pairwise_iff_getElem, Rat.abs_of_nonneg]

/-!
## Prompt

```python3
from typing import List, Tuple


def find_closest_elements(numbers: List[float]) -> Tuple[float, float]:
    """ From a supplied list of numbers (of length at least two) select and return two that are the closest to each
    other and return them in order (smaller number, larger number).
    >>> find_closest_elements([1.0, 2.0, 3.0, 4.0, 5.0, 2.2])
    (2.0, 2.2)
    >>> find_closest_elements([1.0, 2.0, 3.0, 4.0, 5.0, 2.0])
    (2.0, 2.0)
    """
```

## Canonical solution

```python3
    closest_pair = None
    distance = None

    for idx, elem in enumerate(numbers):
        for idx2, elem2 in enumerate(numbers):
            if idx != idx2:
                if distance is None:
                    distance = abs(elem - elem2)
                    closest_pair = tuple(sorted([elem, elem2]))
                else:
                    new_distance = abs(elem - elem2)
                    if new_distance < distance:
                        distance = new_distance
                        closest_pair = tuple(sorted([elem, elem2]))

    return closest_pair
```

## Tests

```python3


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    assert candidate([1.0, 2.0, 3.9, 4.0, 5.0, 2.2]) == (3.9, 4.0)
    assert candidate([1.0, 2.0, 5.9, 4.0, 5.0]) == (5.0, 5.9)
    assert candidate([1.0, 2.0, 3.0, 4.0, 5.0, 2.2]) == (2.0, 2.2)
    assert candidate([1.0, 2.0, 3.0, 4.0, 5.0, 2.0]) == (2.0, 2.0)
    assert candidate([1.1, 2.2, 3.1, 4.1, 5.1]) == (2.2, 3.1)

```
-/
