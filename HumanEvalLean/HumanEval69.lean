module

public import Std
public import Init.Data.Iterators.Lemmas.Basic
open Std

public section

def frequencies (xs : List Nat) : TreeMap Nat Nat (fun a b => compare b a) :=
  xs.foldl (init := ∅) (fun freq (x : Nat) => freq.alter x (fun v? => some (v?.getD 0 + 1)))

def search (xs : List Nat) : Int :=
  let frequencies := frequencies xs
  let kv := frequencies.iter
    |>.filter (fun (k, v) => 0 < k ∧ k ≤ v)
    |>.map (fun (k, _) => k)
    |>.first?
  kv.getD (-1)

@[simp, grind =]
theorem Std.Iter.first?_toList {α β : Type w} [Iterator α Id β] [IteratorLoop α Id Id]
    [Iterators.Finite α Id] [LawfulIteratorLoop α Id Id] {it : Iter (α := α) β} :
    it.toList.head? = it.first? := by
  induction it using Iter.inductSteps with | step it ihy ihs
  rw [first?_eq_match_step, toList_eq_match_step]
  cases it.step using PlausibleIterStep.casesOn <;> simp [*]

theorem getElem?_frequencies {k : Nat} :
    (frequencies xs)[k]? = (some (xs.count k)).filter (0 < ·) := by
  -- We express the statement in terms of `List.foldr`, which makes the induction over `xs`
  -- easier because the initial tree map of the fold never changes. If the statement is expressed in
  -- terms of `List.foldl`, we would need to generalize the statement for general initial tree maps.
  rw [← List.reverse_reverse (as := xs), frequencies, List.foldl_reverse]
  generalize xs.reverse = xs
  induction xs <;> grind

theorem getElem_frequencies {k : Nat} {h} :
    (frequencies xs)[k]'h = xs.count k := by
  grind [getElem?_frequencies]

theorem mem_frequencies :
    x ∈ frequencies xs ↔ x ∈ xs := by
  rw [← TreeMap.isSome_getElem?_iff_mem, getElem?_frequencies]
  simp

theorem search_eq_neg_one (h : ∀ x, x = 0 ∨ xs.count x < x) :
    search xs = -1 := by
  simp only [search, ← Iter.first?_toList, Option.getD_eq_iff, Iter.toList_map, Iter.toList_filter,
    TreeMap.toList_iter]
  grind [List.length_filter_pos_iff, getElem?_frequencies]

theorem search_eq_neg_one_iff :
    search xs = -1 ↔ ∀ x, x = 0 ∨ xs.count x < x := by
  simp [search, ← Iter.first?_toList, Option.getD_eq_iff, Iter.toList_map, Iter.toList_filter,
    TreeMap.toList_iter, getElem?_frequencies]
  grind [List.length_filter_pos_iff]

def IsCandidate (xs : List Nat) (x : Nat) : Prop := 0 < x ∧ x ≤ xs.count x

theorem List.find?_eq_some_iff_of_pairwise_eq_lt {xs : List α} {cmp : α → α → Ordering}
    [OrientedCmp cmp] (h : xs.Pairwise (cmp · · = .lt)) :
    xs.find? P = some x ↔ x ∈ xs ∧ P x ∧ ∀ y ∈ xs, P y → (cmp x y).isLE := by
  rw [List.find?_eq_some_iff_append]
  constructor
  · intro h'
    refine ⟨by grind, by grind, ?_⟩
    intro y hm hy
    obtain ⟨as, bs, rfl, h''⟩ := h'.2
    have : y ∈ x :: bs := by grind
    simp only [pairwise_append, pairwise_cons] at h
    grind [Ordering.isLE_of_eq_eq, Ordering.isLE_of_eq_lt]
  · intro h'
    refine ⟨by grind, ?_⟩
    obtain ⟨as, bs, rfl⟩ := List.mem_iff_append.mp h'.1
    refine ⟨as, bs, rfl, ?_⟩
    intro a ha
    simp only [pairwise_append, pairwise_cons] at h
    replace h' := h'.2.2
    specialize h' a (by grind)
    have : cmp x a = .gt := by
      rw [OrientedCmp.eq_swap (cmp := cmp), Ordering.swap_eq_gt]
      grind
    grind [Ordering.ne_gt_iff_isLE]

theorem search_eq (h : IsCandidate xs x ∧ ∀ y, IsCandidate xs y → y ≤ x) :
    search xs = x := by
  have : OrientedCmp (fun x y : Nat × Nat => compare y.1 x.1) := by
    constructor
    grind [Nat.compare_swap]
  simp [search, ← Iter.first?_toList, Option.getD_eq_iff, List.find?_eq_some_iff_of_pairwise_eq_lt (frequencies xs).ordered_keys_toList, Int.natCast_inj]
  have : x ∈ xs := by grind [IsCandidate, List.count_pos_iff]
  refine ⟨(frequencies xs)[x]'(by simpa [mem_frequencies]), ?_⟩
  grind [getElem?_frequencies, IsCandidate, Nat.isLE_compare]

/-
Memo:

* grind runs into deep recursion
* hard to debug and minimize

[grind] Diagnostics ▼
  [thm] E-Matching instances ▼
    [] getElem?_neg ↦ 1
    [] getElem?_pos ↦ 1
    [] List.getElem?_map ↦ 1
    [] List.getElem_of_getElem? ↦ 1
    [] List.length_filter_pos_iff ↦ 1


    [thm] getElem?_neg: [@getElem? #8 #7 #6 #5 #4 #2 #1]
    [thm] getElem?_pos: [@getElem? #8 #7 #6 #5 #4 #2 #1]
    [thm] List.getElem?_map: [@getElem? (List #3) `[Nat] _ _ _ (@List.map #4 _ #2 #1) #0]
    [thm] List.map_map: [@List.map #5 #4 #2 (@List.map #3 _ #1 #0)]
    [thm] List.filter_map: [@List.filter #3 #1 (@List.map #4 _ #2 #0)]
    [thm] List.getElem?_filter: [@getElem? (List #6) `[Nat] _ _ _ (@List.filter _ #3 #4) #2, @some _ #5]
    [thm] List.getElem_of_getElem?: [@getElem? (List #4) `[Nat] _ _ _ #1 #3, @some _ #2]
    [thm] TreeMap.length_toList: [@List.length (Prod #3 #2) (@TreeMap.toList _ _ #1 #0)]
    [thm] List.length_filter_le: [@List.length #2 (@List.filter _ #1 #0)]
    [thm] List.length_map: [@List.length #2 (@List.map #3 _ #0 #1)]
    [thm] List.eq_nil_of_length_eq_zero: [@List.length #2 #1]
    [thm] List.getElem?_eq_none: [@List.length #3 #2, @getElem? (List _) `[Nat] _ _ _ #2 #1]
    [thm] Option.some_le_some: [@LE.le (Option #3) _ (@some _ #1) (@some _ #0)]
    [thm] Option.not_some_le_none: [@LE.le (Option #2) _ (@some _ #0) (@none _)]
    [thm] Option.none_le: [@LE.le (Option #2) _ (@none _) #0]
    [thm] Option.map_some: [@Option.map #3 #2 #0 (@some _ #1)]
    [thm] Option.map_none: [@Option.map #2 #1 #0 (@none _)]
-/

/-!
## Prompt

```python3

def search(lst):
    '''
    You are given a non-empty list of positive integers. Return the greatest integer that is greater than
    zero, and has a frequency greater than or equal to the value of the integer itself.
    The frequency of an integer is the number of times it appears in the list.
    If no such a value exist, return -1.
    Examples:
        search([4, 1, 2, 2, 3, 1]) == 2
        search([1, 2, 2, 3, 3, 3, 4, 4, 4]) == 3
        search([5, 5, 4, 4, 4]) == -1
    '''
```

## Canonical solution

```python3
    frq = [0] * (max(lst) + 1)
    for i in lst:
        frq[i] += 1;

    ans = -1
    for i in range(1, len(frq)):
        if frq[i] >= i:
            ans = i

    return ans
```

## Tests

```python3
def check(candidate):

    # manually generated tests
    assert candidate([5, 5, 5, 5, 1]) == 1
    assert candidate([4, 1, 4, 1, 4, 4]) == 4
    assert candidate([3, 3]) == -1
    assert candidate([8, 8, 8, 8, 8, 8, 8, 8]) == 8
    assert candidate([2, 3, 3, 2, 2]) == 2

    # automatically generated tests
    assert candidate([2, 7, 8, 8, 4, 8, 7, 3, 9, 6, 5, 10, 4, 3, 6, 7, 1, 7, 4, 10, 8, 1]) == 1
    assert candidate([3, 2, 8, 2]) == 2
    assert candidate([6, 7, 1, 8, 8, 10, 5, 8, 5, 3, 10]) == 1
    assert candidate([8, 8, 3, 6, 5, 6, 4]) == -1
    assert candidate([6, 9, 6, 7, 1, 4, 7, 1, 8, 8, 9, 8, 10, 10, 8, 4, 10, 4, 10, 1, 2, 9, 5, 7, 9]) == 1
    assert candidate([1, 9, 10, 1, 3]) == 1
    assert candidate([6, 9, 7, 5, 8, 7, 5, 3, 7, 5, 10, 10, 3, 6, 10, 2, 8, 6, 5, 4, 9, 5, 3, 10]) == 5
    assert candidate([1]) == 1
    assert candidate([8, 8, 10, 6, 4, 3, 5, 8, 2, 4, 2, 8, 4, 6, 10, 4, 2, 1, 10, 2, 1, 1, 5]) == 4
    assert candidate([2, 10, 4, 8, 2, 10, 5, 1, 2, 9, 5, 5, 6, 3, 8, 6, 4, 10]) == 2
    assert candidate([1, 6, 10, 1, 6, 9, 10, 8, 6, 8, 7, 3]) == 1
    assert candidate([9, 2, 4, 1, 5, 1, 5, 2, 5, 7, 7, 7, 3, 10, 1, 5, 4, 2, 8, 4, 1, 9, 10, 7, 10, 2, 8, 10, 9, 4]) == 4
    assert candidate([2, 6, 4, 2, 8, 7, 5, 6, 4, 10, 4, 6, 3, 7, 8, 8, 3, 1, 4, 2, 2, 10, 7]) == 4
    assert candidate([9, 8, 6, 10, 2, 6, 10, 2, 7, 8, 10, 3, 8, 2, 6, 2, 3, 1]) == 2
    assert candidate([5, 5, 3, 9, 5, 6, 3, 2, 8, 5, 6, 10, 10, 6, 8, 4, 10, 7, 7, 10, 8]) == -1
    assert candidate([10]) == -1
    assert candidate([9, 7, 7, 2, 4, 7, 2, 10, 9, 7, 5, 7, 2]) == 2
    assert candidate([5, 4, 10, 2, 1, 1, 10, 3, 6, 1, 8]) == 1
    assert candidate([7, 9, 9, 9, 3, 4, 1, 5, 9, 1, 2, 1, 1, 10, 7, 5, 6, 7, 6, 7, 7, 6]) == 1
    assert candidate([3, 10, 10, 9, 2]) == -1

```
-/
