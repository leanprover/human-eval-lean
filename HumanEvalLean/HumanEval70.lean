module

def strangeSortArray (xs : Array Int) : Array Int :=
  let sorted := xs.toList.mergeSort.toArray
  Array.ofFn (n := sorted.size)
    (fun i => if i.val % 2 = 0 then sorted[i.val / 2] else sorted[sorted.size - 1 - i.val / 2])

theorem t {xs : List Int} :
    xs.min?.all (· ∈ xs) := by
  simp only [Option.all_eq_true_iff_get]
  grind

grind_pattern t => xs.min?

def strangeSortListSlow (xs : List Int) : List Int :=
    match _ : xs.min? with
    | some minimum =>
      let xs' := xs.erase minimum
      minimum :: (strangeSortListSlow xs'.reverse).reverse
    | none => []
termination_by xs.length
decreasing_by grind

-- missing api

theorem List.Perm.min_eq [LE α] [Min α] [Std.LawfulOrderMin α] [Std.IsLinearOrder α]
    {xs ys : List α} (h_perm : xs.Perm ys) (h : xs ≠ []) :
    xs.min h = ys.min (by grind [Perm.eq_nil]) := by
  simp only [List.min_eq_iff]
  grind

theorem List.Perm.min?_eq [LE α] [Min α] [Std.LawfulOrderMin α] [Std.IsLinearOrder α]
    {xs ys : List α} (h_perm : xs.Perm ys) :
    xs.min? = ys.min? := by
  match xs, ys with
  | [], [] => rfl
  | x :: xs, y :: ys =>
    rw [min?_eq_some_min, min?_eq_some_min, h_perm.min_eq]
    simp
  | x :: xs, [] | [], y :: ys => grind [Perm.nil_eq, Perm.eq_nil]

theorem List.Perm.max_eq [LE α] [Max α] [Std.LawfulOrderMax α] [Std.IsLinearOrder α]
    {xs ys : List α} (h_perm : xs.Perm ys) (h : xs ≠ []) :
    xs.max h = ys.max (by grind [Perm.eq_nil]) := by
  simp only [List.max_eq_iff]
  grind

theorem List.Perm.max?_eq [LE α] [Max α] [Std.LawfulOrderMax α] [Std.IsLinearOrder α]
    {xs ys : List α} (h_perm : xs.Perm ys) :
    xs.max? = ys.max? := by
  match xs, ys with
  | [], [] => rfl
  | x :: xs, y :: ys =>
    rw [max?_eq_some_max, max?_eq_some_max, h_perm.max_eq]
    simp
  | x :: xs, [] | [], y :: ys => grind [Perm.nil_eq, Perm.eq_nil]

theorem List.foldl_concat [Max α] {xs : List α} :
    (xs.concat x).foldl f init = f (xs.foldl f init) x := by
  simp

-- theorem List.max?_concat [Max α] {xs : List α} :
--     (xs.concat x).max? = xs.max?.elim x (fun maximum => max maximum x) := by
--   induction xs
--   sorry

-- theorem List.max?_eq_getLast? [Max α] {xs : List α} (hp : xs.Pairwise (fun a b => max a b = b)) :
--     xs.max? = xs.getLast? := by
--   rw [← List.reverse_reverse (as := xs)]
--   generalize xs.reverse = xs
--   induction xs
--   · simp
--   · rename_i x xs ih
--     simp [List.max?_push, List.getLast?_cons]

theorem List.max_eq_getLast [Max α] {xs : List α} (h) (hp : xs.Pairwise (fun a b => max a b = b)) :
    xs.max h = xs.getLast h := by
  rw [List.max.eq_def]
  split
  rename_i x xs _
  suffices ∀ xs : List α, (x :: xs.reverse).Pairwise (fun a b => max a b = b) → foldl max x xs.reverse = (x :: xs.reverse).getLast (by grind) by
    simp +singlePass only [← List.reverse_reverse (as := xs)]
    grind
  simp [- pairwise_cons]
  intro xs hp
  induction xs
  · simp
  · simp
    rename_i ih
    rw [ih]
    rw [List.reverse_cons, ← List.cons_append, pairwise_append] at hp <;> grind
    grind -- what's going on?

theorem Array.max_eq_back [Max α] {xs : Array α} (h) (hp : xs.toList.Pairwise (fun a b => max a b = b)) :
    xs.max h = xs.back (by grind) := by
  rw [← max_toList, List.max_eq_getLast, getLast_toList]
  · exact hp
  · simp [h]

theorem List.max?_eq_getLast? [Max α] {xs : List α} (hp : xs.Pairwise (fun a b => max a b = b)) :
    xs.max? = xs.getLast? := by
  cases xs
  · simp
  · rw [max?_eq_some_max, max_eq_getLast, getLast?_eq_some_getLast]
    · simp
    · exact hp

theorem Std.min_eq_left_iff [LE α] [Min α] [Std.Refl (α := α) (· ≤ ·)]
    [Std.LawfulOrderLeftLeaningMin α] {a b : α} :
    min a b = a ↔ a ≤ b := by
  by_cases a ≤ b
  · grind [Std.LawfulOrderLeftLeaningMin.min_eq_left]
  · rename_i h
    simp only [Std.LawfulOrderLeftLeaningMin.min_eq_right _ _ h, iff_false, h]
    rintro rfl
    exact h.elim (Std.Refl.refl _)

theorem Std.max_eq_right_iff [LE α] [Max α] [Std.IsLinearOrder α] [Std.LawfulOrderMax α]
    {a b : α} :
    max a b = b ↔ a ≤ b := by
  open scoped Classical in grind [max_eq_if]

theorem List.getElem_zero_mergeSort {xs : List Int} (h) :
    xs.mergeSort[0]'h = xs.min (by grind [length_mergeSort]) := by
  rw [(xs.mergeSort_perm (· ≤ ·)).symm.min_eq, List.min_eq_head, List.head_eq_getElem]
  simp only [Std.min_eq_left_iff]
  simpa using xs.pairwise_mergeSort (by grind) (by grind) (le := (· ≤ ·))

theorem List.getElem_length_sub_one_mergeSort {xs : List Int} (h) :
    xs.mergeSort[xs.length - 1]'h = xs.max (by grind [length_mergeSort]) := by
  rw [(xs.mergeSort_perm (· ≤ ·)).symm.max_eq, List.max_eq_getLast, List.getLast_eq_getElem]
  · simp [List.length_mergeSort]
  · simp only [Std.max_eq_right_iff]
    simpa using xs.pairwise_mergeSort (by grind) (by grind) (le := (· ≤ ·))

theorem List.max_erase_le_max {xs : List Int} (h) :
    (xs.erase x).max h ≤ xs.max (by grind) := by
  simp only [List.max_le_iff]
  intro b hb
  apply List.le_max_of_mem
  exact List.mem_of_mem_erase hb

theorem Array.max_erase_le_max {xs : Array Int} {h} :
    (xs.erase x).max h ≤ xs.max (by grind) := by
  simp only [Array.max_le_iff]
  intro b hb
  apply Array.le_max_of_mem
  exact Array.mem_of_mem_erase hb

theorem List.count_dropLast [BEq α] {xs : List α} {a : α} :
    xs.dropLast.count a = xs.count a - if xs.getLast? == some a then 1 else 0 := by
  rw [← List.reverse_reverse (as := xs)]
  generalize xs.reverse = xs
  rw [dropLast_reverse, count_reverse, count_tail, getLast?_reverse, count_reverse]

theorem Array.count_pop [BEq α] {xs : Array α} {a : α} :
    xs.pop.count a = xs.count a - if xs.back? == some a then 1 else 0 := by
  rw [← count_toList, toList_pop, List.count_dropLast, getLast?_toList, count_toList]

-- verification

theorem strangeSortArray_empty :
    strangeSortArray #[] = #[] := by
  grind [strangeSortArray, List.mergeSort_nil]

theorem strangeSortArray_singleton :
    strangeSortArray #[x] = #[x] := by
  ext <;> grind [strangeSortArray, List.mergeSort_singleton, Array.size_ofFn, Array.getElem_ofFn]

theorem bla' {xs : Array Int} {h} :
    (xs.erase (xs.max h)).toList.mergeSort = xs.toList.mergeSort.dropLast := by
  apply List.Perm.eq_of_pairwise (le := (· ≤ ·))
  · grind
  · simpa using List.pairwise_mergeSort (α := Int) (le := (· ≤ ·)) (by grind) (by grind) _
  · simp only [List.dropLast_eq_take]
    apply List.Pairwise.take
    simpa using List.pairwise_mergeSort (α := Int) (le := (· ≤ ·)) (by grind) (by grind) _
  · refine List.Perm.trans (List.mergeSort_perm _ _) ?_
    rw [List.perm_iff_toArray_perm, Array.toArray_toList]
    simp only [Array.perm_iff_toList_perm]
    simp only [List.perm_iff_count, Array.count_toList]
    intro a
    rw [Array.count_erase]
    have h_mem : xs.max h ∈ xs := by grind
    rw [List.count_dropLast, List.count_toArray, (List.mergeSort_perm _ _).count_eq,
      ← List.max?_eq_getLast?, (List.mergeSort_perm _ _).max?_eq, Array.max?_toList,
      Array.max?_eq_some_max]
    · simp
    · grind
    · simp only [Std.max_eq_right_iff]
      simpa using List.pairwise_mergeSort (α := Int) (le := (· ≤ ·)) (by grind) (by grind) _

theorem blub' {xs : Array Int} {h} :
    (xs.erase (xs.min h)).toList.mergeSort = xs.toList.mergeSort.drop 1 := by
  apply List.Perm.eq_of_pairwise (le := (· ≤ ·))
  · grind
  · simpa using List.pairwise_mergeSort (α := Int) (le := (· ≤ ·)) (by grind) (by grind) _
  · apply List.Pairwise.drop
    simpa using List.pairwise_mergeSort (α := Int) (le := (· ≤ ·)) (by grind) (by grind) _
  · refine List.Perm.trans (List.mergeSort_perm _ _) ?_
    rw [← Array.perm_iff_toList_perm]
    simp only [Array.perm_iff_toList_perm]
    simp [List.perm_iff_count, Array.count_toList, - List.pop_toArray, - Array.toList_pop]
    intro a
    rw [Array.count_erase]
    have h_mem : xs.max h ∈ xs := by grind
    rw [List.count_tail, List.count_toArray, (List.mergeSort_perm _ _).count_eq,
      ← List.min?_eq_head?, (List.mergeSort_perm _ _).min?_eq, Array.min?_toList,
      Array.min?_eq_some_min]
    · simp
    · grind
    · simp only [Std.min_eq_left_iff]
      simpa using List.pairwise_mergeSort (α := Int) (le := (· ≤ ·)) (by grind) (by grind) _

theorem size_strangeSortArray {xs : Array Int} :
    (strangeSortArray xs).size = xs.size := by
  simp [strangeSortArray]

theorem strangeSortArray_of_two_le_size (h : 2 ≤ xs.size) :
    let minimum := xs.min (by grind)
    let withoutMin := xs.erase minimum
    let maximum := withoutMin.max (by grind)
    let withoutMinMax := withoutMin.erase maximum
    strangeSortArray xs = #[minimum, maximum] ++ strangeSortArray withoutMinMax := by
  intro minimum withoutMin maximum withoutMinMax
  ext
  · simp [strangeSortArray]
    grind
  · rename_i i h₁ h₂
    simp [strangeSortArray]
    match i with
    | 0 => grind [List.getElem_zero_mergeSort]
    | 1 =>
      simp [← Array.length_toList, List.getElem_length_sub_one_mergeSort, maximum, withoutMin]
      rw [Array.max_eq_iff]
      constructor
      · grind [Array.mem_of_mem_erase]
      · intro b hb
        by_cases hb' : b = minimum
        · cases hb'
          simp only [minimum]
          apply Array.min_le_of_mem
          exact Array.mem_of_mem_erase (Array.max_mem _)
        · apply Array.le_max_of_mem
          rwa [Array.mem_erase_of_ne]
          assumption
    | j + 2 =>
      have : withoutMinMax.toList.mergeSort = xs.toList.mergeSort.extract 1 (xs.toList.mergeSort.length - 1) := by
        simp only [withoutMinMax, maximum, bla']
        simp only [withoutMin, minimum, blub']
        simp only [List.extract_eq_take_drop, List.dropLast_eq_take]
        grind
      simp [this]
      grind [size_strangeSortArray]

/-!
## Prompt

```python3

def strange_sort_list(lst):
    '''
    Given list of integers, return list in strange order.
    Strange sorting, is when you start with the minimum value,
    then maximum of the remaining integers, then minimum and so on.

    Examples:
    strange_sort_list([1, 2, 3, 4]) == [1, 4, 2, 3]
    strange_sort_list([5, 5, 5, 5]) == [5, 5, 5, 5]
    strange_sort_list([]) == []
    '''
```

## Canonical solution

```python3
    res, switch = [], True
    while lst:
        res.append(min(lst) if switch else max(lst))
        lst.remove(res[-1])
        switch = not switch
    return res
```

## Tests

```python3
def check(candidate):

    # Check some simple cases
    assert candidate([1, 2, 3, 4]) == [1, 4, 2, 3]
    assert candidate([5, 6, 7, 8, 9]) == [5, 9, 6, 8, 7]
    assert candidate([1, 2, 3, 4, 5]) == [1, 5, 2, 4, 3]
    assert candidate([5, 6, 7, 8, 9, 1]) == [1, 9, 5, 8, 6, 7]
    assert candidate([5, 5, 5, 5]) == [5, 5, 5, 5]
    assert candidate([]) == []
    assert candidate([1,2,3,4,5,6,7,8]) == [1, 8, 2, 7, 3, 6, 4, 5]
    assert candidate([0,2,2,2,5,5,-5,-5]) == [-5, 5, -5, 5, 0, 2, 2, 2]
    assert candidate([111111]) == [111111]

    # Check some edge cases that are easy to work out by hand.
    assert True

```
-/
