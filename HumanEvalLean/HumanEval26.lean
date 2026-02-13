module

public import Std
open Std
open scoped List

public section

/-! ## Implementation -/

def counter (xs : Array Int) : TreeMap Int Nat :=
    xs.foldl (init := ∅) (fun m x => m.alter x (some <| ·.getD 0 + 1))

def removeDuplicates (xs : Array Int) : Array Int :=
  let counter := counter xs
  xs.filter (counter.getD · 0 ≤ 1)

/-! ## Tests -/

example : removeDuplicates #[] = #[] := by native_decide
example : removeDuplicates #[1, 2, 3, 4] = #[1, 2, 3, 4] := by native_decide
example : removeDuplicates #[1, 2, 3, 2, 4, 3, 5] = #[1, 4, 5] := by native_decide

/-! ## Missing API -/

theorem List.sublist_filter_iff' {l₁ : List α} {p : α → Bool} :
    l₁ <+ l₂.filter p ↔ l₁ <+ l₂ ∧ (∀ a ∈ l₁, p a) := by
  rw [List.sublist_filter_iff]
  apply Iff.intro
  · rintro ⟨l', hl', rfl⟩
    apply And.intro
    · exact List.Sublist.trans filter_sublist hl'
    · grind
  · rintro ⟨h, h'⟩
    refine ⟨l₁, h, ?_⟩
    apply Eq.symm
    simpa

theorem List.count_eq_foldl {xs : List α} {x : α} [BEq α] :
    xs.count x = xs.foldl (init := 0) (fun acc y => if y == x then acc + 1 else acc) := by
  simp [← foldl_filter, foldl_add_const, count_eq_length_filter]

theorem Array.count_eq_foldl {xs : Array α} {x : α} [BEq α] :
    xs.count x = xs.foldl (init := 0) (fun acc y => if y == x then acc + 1 else acc) := by
  simp [← count_toList, List.count_eq_foldl]

theorem List.count_filter_of_false {xs : List α} {x : α} [BEq α] [LawfulBEq α] (h : ¬ P x) :
    (xs.filter P).count x = 0 := by
  induction xs <;> grind

theorem Array.count_filter_of_false {xs : Array α} {x : α} [BEq α] [LawfulBEq α] (h : ¬ P x) :
    (xs.filter P).count x = 0 := by
  simp [← count_toList, List.count_filter_of_false h]

/-! ## Verification -/

theorem getD_counter {xs : Array Int} :
    (counter xs).getD x 0 = xs.count x := by
  rw [counter, Array.count_eq_foldl]
  conv => rhs; rw (occs := [1]) [show 0 = (∅ : TreeMap Int Nat compare).getD x 0 by simp]
  rw (occs := [1]) [Array.foldl_hom (xs := xs) (α₁ := TreeMap Int Nat compare) (α₂ := Nat)
    (f := fun m => m.getD x 0)
    (g₁ := fun m x => m.alter x fun x => some (x.getD 0 + 1))
    (init := ∅)]
  grind [TreeMap.getD_eq_getD_getElem?]

/--
This lemma proves that `removeDuplicates` is equivalent to a less efficient but more declarative
implementation, filtering based on `List.count`.
-/
theorem removeDuplicates_eq_filter_count :
    removeDuplicates xs = xs.filter (xs.count · ≤ 1) := by
  grind [removeDuplicates, getD_counter]

/--
This lemma characterizes `removeDuplicates` in terms of the kinds of sublists it has.
-/
theorem sublist_removeDuplicates_iff :
    ys <+ (removeDuplicates xs).toList ↔ ys <+ xs.toList ∧ ∀ y ∈ ys, xs.count y ≤ 1 := by
  grind [removeDuplicates_eq_filter_count, List.sublist_filter_iff']

/--
This lemma proves that `removeDuplicates xs` is contained in `xs` in the correct order.
-/
theorem removeDuplicates_sublist :
    (removeDuplicates xs).toList <+ xs.toList := by
  grind [removeDuplicates_eq_filter_count, List.filter_sublist]

/--
This lemma proves that `removeDuplicates xs` contains each element at most once,
depending on whether it is contained exactly once in `xs`.
-/
theorem count_removeDuplicates :
    (removeDuplicates xs).count x = if xs.count x = 1 then 1 else 0 := by
  grind [removeDuplicates_eq_filter_count, Array.count_filter, Array.count_filter_of_false]

/--
This lemma proves that an element is contained in `removeDuplicates xs` if and only if it is
contained exactly once in `xs`.
-/
theorem mem_removeDuplicates_iff :
    x ∈ removeDuplicates xs ↔ xs.count x = 1 := by
  have : x ∈ xs ↔ 1 ≤ xs.count x := by grind [Array.count_eq_zero]
  rw [← Array.mem_toList_iff, ← List.singleton_sublist, sublist_removeDuplicates_iff,
    List.singleton_sublist, Array.mem_toList_iff, this]
  grind

/-!
## Prompt

```python3
from typing import List


def remove_duplicates(numbers: List[int]) -> List[int]:
    """ From a list of integers, remove all elements that occur more than once.
    Keep order of elements left the same as in the input.
    >>> remove_duplicates([1, 2, 3, 2, 4])
    [1, 3, 4]
    """
```

## Canonical solution

```python3
    import collections
    c = collections.Counter(numbers)
    return [n for n in numbers if c[n] <= 1]
```

## Tests

```python3


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    assert candidate([]) == []
    assert candidate([1, 2, 3, 4]) == [1, 2, 3, 4]
    assert candidate([1, 2, 3, 2, 4, 3, 5]) == [1, 4, 5]
```
-/
