module

public import Std
import all Init.Data.Range.Polymorphic.UpwardEnumerable
public meta import Lean -- TODO
open Std

/-! ## Implementation -/

public section

instance : PRange.Least? (Fin n) where
  least? := if h : 0 < n then some ⟨0, by grind⟩ else none

instance : PRange.LawfulUpwardEnumerableLeast? (Fin n) where
  least?_le x := ⟨⟨0, by grind [x.isLt]⟩, by
    simp [PRange.least?, PRange.UpwardEnumerable.LE]
    constructor
    · grind [x.isLt]
    · refine ⟨x.val, by grind⟩⟩

def smallestChange (xs : Array Nat) : Nat :=
  (*...* : Rii (Fin (xs.size / 2))).iter.filter (fun i => xs[i.val] ≠ xs[xs.size - 1 - i.val]) |>.length

/-! ## Tests -/

example : smallestChange #[1,2,3,5,4,7,9,6] = 4 := by native_decide
example : smallestChange #[1, 2, 3, 4, 3, 2, 2] = 1 := by native_decide
example : smallestChange #[1, 4, 2] = 1 := by native_decide
example : smallestChange #[1, 4, 4, 2] = 1 := by native_decide
example : smallestChange #[1, 2, 3, 2, 1] = 0 := by native_decide
example : smallestChange #[3, 1, 1, 3] = 0 := by native_decide
example : smallestChange #[1] = 0 := by native_decide
example : smallestChange #[0, 1] = 1 := by native_decide

/-! ## Missing API -/

theorem Vector.ext_getElem_iff {l₁ l₂ : Vector α n} :
    l₁ = l₂ ↔ ∀ (i : Nat) (h₁ : i < n) (h₂ : i < n), l₁[i]'h₁ = l₂[i]'h₂ := by
  simp [← Vector.toList_inj, List.ext_getElem_iff]

@[simp, grind =]
theorem Fin.size_rii :
    (*...* : Rii (Fin n)).size = n := by
  simp only [Rii.size, PRange.least?, Rxi.HasSize.size]
  grind

attribute [grind =] Rii.length_toList

@[simp, grind =]
theorem Fin.length_toList_rii :
    (*...* : Rii (Fin n)).size = n := by
  grind

attribute [grind .] Rii.mem Rii.mem_toList Rii.nodup_toList

theorem List.filter_false {xs : List α} :
    xs.filter (fun _ => false) = [] := by
  simp

theorem List.Nodup.countP_le_countP_add_one {xs : List α} (h : xs.Nodup)
    (h' : ∀ b ∈ xs, b = a ∨ p b = q b) :
    xs.countP p ≤ xs.countP q + 1 := by
  open Classical in
  have : xs.countP p ≤ (xs.erase a).countP p + 1 := by
    have := (xs.filter p).le_length_erase (a := a)
    grind
  have : (xs.erase a).countP p = (xs.erase a).countP q := by
    apply List.countP_congr
    grind
  have : (xs.erase a).countP q ≤ xs.countP q := by
    apply List.Sublist.countP_le
    apply List.erase_sublist
  grind

@[grind .]
theorem List.Nodup.map (f : α → β) (h : ∀ a b : α, ¬ a = b → ¬ (f a) = (f b))
    (p : Nodup l) : Nodup (map f l) := by
  simp only [nodup_iff_pairwise_ne, ne_eq] at p ⊢
  exact Pairwise.map f h p

@[grind ←] theorem List.Nodup.filter (p : α → Bool) : Nodup l → Nodup (filter p l) :=
  Pairwise.sublist filter_sublist

theorem Array.getElem!_set {xs : Array Nat} {h} :
    (xs.set i v h)[j]! = if j = i then v else xs[j]! := by
  grind

theorem Fin.map_val_toList_roi {n : Nat} (m : Fin n) :
    (m<...* : Roi (Fin n)).toList.map (·.val) = (m.val<...n).toList := by
  induction h : n - m.val generalizing m
  · grind
  · rename_i ih
    have : m.val < n := by grind
    rw [Roi.toList_eq_match]
    split
    · simp only [List.map_nil, List.nil_eq, Nat.toList_roo_eq_nil_iff] at *
      grind
    · specialize ih ⟨m + 1, by grind⟩
      rw [Nat.toList_roo_eq_cons, ← ih] <;> grind

theorem Fin.map_val_toList_rci {n : Nat} (m : Fin n) :
    (m...* : Rci (Fin n)).toList.map (·.val) = (m.val...n).toList := by
  induction h : n - m.val generalizing m
  · grind
  · rename_i ih
    have : m.val < n := by grind
    rw [Rci.toList_eq_toList_roi, List.map_cons, Fin.map_val_toList_roi, Nat.toList_rco_eq_cons (by grind)]
    simp [Nat.toList_roo_eq_toList_rco]

theorem Fin.map_val_toList_rii {n : Nat} :
    (*...* : Rii (Fin n)).toList.map (·.val) = (*...n).toList := by
  simp only [Rii.toList_eq_match_rci, PRange.least?, Rio.toList_eq_match_rco]
  split
  · grind [Nat.toList_rco_eq_nil_iff]
  · grind [map_val_toList_rci]

/-! ## Verification -/

def IsPalindrome (xs : Vector Nat n) := xs.reverse = xs

theorem getElem_foldl_set {changes : List (Fin n × α)} {v : Vector α n}
    (h_nodup : (changes.map Prod.fst).Nodup) {j : Nat} (hj : j < n) :
    (changes.foldl (fun v' (i, x) => v'.set i x) v)[j] =
       match changes.find? (·.1.val == j) with
       | some (_, x) => x
       | none => v[j] := by
  rw [← List.reverse_reverse (as := changes)] at h_nodup ⊢
  generalize changes.reverse = revChanges at ⊢ h_nodup
  induction revChanges
  · simp
  · rename_i c cs ih
    simp only [List.foldl_reverse] at ih
    simp only [List.reverse_cons, List.foldl_append, List.foldl_reverse, List.foldl_cons,
      List.foldl_nil]
    rw [Vector.getElem_set, ih]
    split
    · split
      · simp only [List.reverse_cons, List.map_append] at h_nodup
        rw [List.nodup_append] at h_nodup
        replace h_nodup := h_nodup.2.2 c.fst
        grind
      · grind
    · grind
    · grind

/--
First direction of the characterization:

There is a finite sequence of modifications that transforms `xs` into a palindrome, and the sequence
consists of exactly `smallestChange xs` modifications..
-/
theorem exists_isPalindrome {xs : Array Nat} :
    ∃ changes : List (Fin xs.size × Nat), changes.length = smallestChange xs ∧
      IsPalindrome (changes.foldl (fun xs' (i, v) => xs'.set i.val v) xs.toVector) := by
  refine ⟨(*...* : Rii (Fin (xs.size / 2))).iter.filter (fun i => xs[i.val] ≠ xs[xs.size - 1 - i.val]) |>.map (fun i => (⟨i.val, by grind⟩, xs[xs.size - 1 - i.val])) |>.toList, ?_⟩
  constructor
  · simp [smallestChange, ← Iter.length_toList_eq_length]
  · rw [IsPalindrome, Vector.ext_getElem_iff]
    intro i h₁ h₂
    simp only [Iter.toList_map, Iter.toList_filter, Rii.toList_iter, Vector.getElem_reverse]
    rw [getElem_foldl_set (by grind), getElem_foldl_set (by grind)]
    simp only [List.find?_map, Vector.getElem_mk]
    split <;> split
    · grind
    · grind [Option.map_eq_some_iff]
    · grind [Option.map_eq_some_iff]
    · simp only [Option.map_eq_none_iff, List.find?_eq_none] at *
      rename_i heq heq'
      match hcmp : compare i (xs.size - 1 - i) with
      | .lt =>
        specialize heq ⟨i, by grind⟩
        grind
      | .eq => grind
      | .gt =>
        specialize heq' ⟨xs.size - 1 - i, by grind⟩
        grind

/--
An alternative, less efficient implementation of `smallestChange` that does not use `Fin`.
It is less dependently typed and therefore lends itself better to verification.
-/
private def smallestChangeAux (xs : Array Nat) : Nat :=
  (*...(xs.size / 2)).iter.filter (fun i => xs[i]! ≠ xs[xs.size - 1 - i]!) |>.length

private theorem smallChange_eq_smallChangeAux {xs : Array Nat} :
    smallestChange xs = smallestChangeAux xs := by
    simp only [smallestChange, ← Iter.length_toList_eq_length, smallestChangeAux,
      Iter.toList_filter, Rii.toList_iter, Rio.toList_iter, ← Fin.map_val_toList_rii,
      List.filter_map, Function.comp_def]
    grind

/--
Second part of the verification:

In order to transform `xs` into a palindrome, one needs at least `smallestChange xs` modifications.
-/
theorem smallestChange_le {xs : Array Nat} {changes : List (Fin xs.size × Nat)}
    (h : IsPalindrome (changes.foldl (fun xs' (i, v) => xs'.set i.val v) xs.toVector)) :
    smallestChange xs ≤ changes.length := by
  suffices ∀ ys : Vector Nat xs.size,
      IsPalindrome (changes.foldl (fun xs' (i, v) => xs'.set i.val v) ys) →
      (List.filter (fun i => !decide (ys.toArray[i]! = ys.toArray[ys.toArray.size - 1 - i]!))
        (*...ys.toArray.size / 2).iter.toList).length ≤ changes.length by
    rw [smallChange_eq_smallChangeAux, smallestChangeAux]
    simp only [ne_eq, decide_not, ← Iter.length_toList_eq_length, Iter.toList_filter]
    grind
  clear h
  intro ys h
  induction changes generalizing ys
  · simp only [Rio.toList_iter, List.length_nil, Nat.le_zero_eq, List.length_eq_zero_iff,
      List.filter_eq_nil_iff]
    intro a ha
    simp only [Rio.mem_toList_iff_mem, Rio.mem_iff] at ha
    grind [Vector.cast_mk, IsPalindrome, List.reverse_nil, Vector.reverse_mk, List.filter_false]
  · rename_i c cs ih
    specialize ih _  h
    simp only [List.foldl_cons] at h
    replace ih := Nat.add_le_add_right ih 1
    refine le_trans ?_ ih
    simp only [← List.countP_eq_length_filter, Vector.size_toArray]
    apply List.Nodup.countP_le_countP_add_one (a := min c.fst.val (xs.size - 1 - c.fst.val))
    · apply Rio.nodup_toList
    · intro b hb
      simp only [Vector.toArray_set, Array.getElem!_set]
      simp only [Rio.toList_iter, Rio.mem_toList_iff_mem, Rio.mem_iff] at hb
      split
      · grind
      · grind

/-!
## Prompt

```python3

def smallest_change(arr):
    """
    Given an array arr of integers, find the minimum number of elements that
    need to be changed to make the array palindromic. A palindromic array is an array that
    is read the same backwards and forwards. In one change, you can change one element to any other element.

    For example:
    smallest_change([1,2,3,5,4,7,9,6]) == 4
    smallest_change([1, 2, 3, 4, 3, 2, 2]) == 1
    smallest_change([1, 2, 3, 2, 1]) == 0
    """
```

## Canonical solution

```python3
    ans = 0
    for i in range(len(arr) // 2):
        if arr[i] != arr[len(arr) - i - 1]:
            ans += 1
    return ans
```

## Tests

```python3
def check(candidate):

    # Check some simple cases
    assert candidate([1,2,3,5,4,7,9,6]) == 4
    assert candidate([1, 2, 3, 4, 3, 2, 2]) == 1
    assert candidate([1, 4, 2]) == 1
    assert candidate([1, 4, 4, 2]) == 1

    # Check some edge cases that are easy to work out by hand.
    assert candidate([1, 2, 3, 2, 1]) == 0
    assert candidate([3, 1, 1, 3]) == 0
    assert candidate([1]) == 0
    assert candidate([0, 1]) == 1

```
-/
