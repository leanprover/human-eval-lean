module

def strangeSortArray (xs : Array Int) : Array Int :=
  let sorted := xs.mergeSort
  Array.ofFn (n := sorted.size)
    (fun i => if i.val % 2 = 0 then sorted[i.val / 2] else sorted[sorted.size - 1 - i.val / 2])

theorem t {xs : List Int} :
    xs.min?.all (· ∈ xs) := by
  simp only [Option.all_eq_true_iff_get]
  grind

grind_pattern t => xs.min?

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

theorem Array.Perm.max?_eq [LE α] [Max α] [Std.LawfulOrderMax α] [Std.IsLinearOrder α]
    {xs ys : Array α} (h_perm : xs.Perm ys) :
    xs.max? = ys.max? := by
  simp [← max?_toList, h_perm.toList.max?_eq]

theorem Array.Perm.min?_eq [LE α] [Min α] [Std.LawfulOrderMin α] [Std.IsLinearOrder α]
    {xs ys : Array α} (h_perm : xs.Perm ys) :
    xs.min? = ys.min? := by
  simp [← min?_toList, h_perm.toList.min?_eq]

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

theorem List.max?_eq_getLast? [Max α] {xs : List α} (hp : xs.Pairwise (fun a b => max a b = b)) :
    xs.max? = xs.getLast? := by
  cases xs
  · simp
  · rw [max?_eq_some_max, max_eq_getLast, getLast?_eq_some_getLast]
    · simp
    · exact hp

theorem Array.max_eq_back [Max α] {xs : Array α} (h) (hp : xs.toList.Pairwise (fun a b => max a b = b)) :
    xs.max h = xs.back (by grind) := by
  rw [← max_toList, List.max_eq_getLast, getLast_toList]
  · exact hp
  · simp [h]

theorem Array.max?_eq_back? [Max α] {xs : Array α} (hp : xs.toList.Pairwise (fun a b => max a b = b)) :
    xs.max? = xs.back? := by
  simp [← max?_toList, List.max?_eq_getLast? hp]

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

theorem Array.getElem_zero_mergeSort {xs : Array Int} (h) :
    xs.mergeSort[0]'h = xs.min (by grind [size_mergeSort]) := by
  simp only [mergeSort_eq_toArray_mergeSort_toList, List.getElem_toArray,
    List.getElem_zero_mergeSort, min_toList]

theorem List.getElem_length_sub_one_mergeSort {xs : List Int} (h) :
    xs.mergeSort[xs.length - 1]'h = xs.max (by grind [length_mergeSort]) := by
  rw [(xs.mergeSort_perm (· ≤ ·)).symm.max_eq, List.max_eq_getLast, List.getLast_eq_getElem]
  · simp [List.length_mergeSort]
  · simp only [Std.max_eq_right_iff]
    simpa using xs.pairwise_mergeSort (by grind) (by grind) (le := (· ≤ ·))

theorem Array.getElem_size_sub_one_mergeSort {xs : Array Int} (h) :
    xs.mergeSort[xs.size - 1]'h = xs.max (by grind [size_mergeSort]) := by
  simp only [mergeSort_eq_toArray_mergeSort_toList]
  simp only [← length_toList, List.getElem_toArray]
  rw [List.getElem_length_sub_one_mergeSort, max_toList]

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

/--
If two lists are sorted by an antisymmetric relation, and permutations of each other,
they must be equal.
-/
theorem Array.Perm.eq_of_pairwise {xs ys : Array α}
    (h : ∀ a b, a ∈ xs → b ∈ ys → le a b → le b a → a = b)
    (hpx : xs.toList.Pairwise le) (hpy : ys.toList.Pairwise le) (hp : xs.Perm ys) :
    xs = ys := by
  rw [← toList_inj]
  apply List.Perm.eq_of_pairwise (by simpa) hpx hpy (by simpa [perm_iff_toList_perm] using hp)

theorem Array.pop_eq_take {xs : Array α} :
    xs.pop = xs.take (xs.size - 1) := by
  rw [take_eq_extract, extract_eq_pop rfl]

theorem List.Pairwise.toList_arrayTake {xs : Array α} (h : xs.toList.Pairwise R) :
    (xs.take i).toList.Pairwise R := by
  simp only [Array.take_eq_extract, Array.toList_extract, extract_eq_take_drop, Nat.sub_zero,
    drop_zero]
  apply List.Pairwise.take
  exact h

theorem List.Pairwise.toList_arrayDrop {xs : Array α} (h : xs.toList.Pairwise R) :
    (xs.drop i).toList.Pairwise R := by
  simp only [Array.drop_eq_extract, Array.toList_extract, extract_eq_drop_take']
  apply List.Pairwise.drop
  apply List.Pairwise.take
  exact h

theorem Array.Perm.countP_eq [BEq α] {xs ys : Array α} (hp : xs.Perm ys) :
    xs.countP P = ys.countP P := by
  simp [← countP_toList, hp.toList.countP_eq]

theorem Array.Perm.count_eq [BEq α] {xs ys : Array α} (hp : xs.Perm ys) :
    xs.count a = ys.count a :=
  hp.countP_eq

theorem Array.head?_toList {xs : Array α} :
    xs.toList.head? = xs[0]? := by
  simp [List.head?_eq_getElem?]

@[grind =]
theorem Array.count_drop_one [BEq α] {xs : Array α} {a : α} :
      (xs.drop 1).count a = xs.count a - if xs[0]? == some a then 1 else 0 := by
    have := List.count_tail (l := xs.toList) (a := a)
    simp [← count_toList, List.take_of_length_le, this, head?_toList]

theorem Array.min?_eq_getElem?_zero {α : Type u} [Min α] {xs : Array α}
    (h : xs.toList.Pairwise (fun a b => min a b = a)) : xs.min? = xs[0]? := by
  simp [← min?_toList, List.min?_eq_head? h, List.head?_eq_getElem?]

-- verification

theorem strangeSortArray_empty :
    strangeSortArray #[] = #[] := by
  grind [strangeSortArray, Array.mergeSort_empty]

theorem strangeSortArray_singleton :
    strangeSortArray #[x] = #[x] := by
  ext <;> grind [strangeSortArray, Array.mergeSort_singleton, Array.size_ofFn, Array.getElem_ofFn]

theorem mergeSort_erase_max {xs : Array Int} {h} :
    (xs.erase (xs.max h)).mergeSort = xs.mergeSort.pop := by
  apply Array.Perm.eq_of_pairwise (le := (· ≤ ·))
  · grind
  · simpa using Array.pairwise_mergeSort (α := Int) (le := (· ≤ ·)) (by grind) (by grind)
  · simp only [Array.pop_eq_take]
    apply List.Pairwise.toList_arrayTake
    simpa using Array.pairwise_mergeSort (α := Int) (le := (· ≤ ·)) (by grind) (by grind)
  · refine Array.Perm.trans Array.mergeSort_perm ?_
    simp only [Array.perm_iff_toList_perm, List.perm_iff_count, Array.count_toList]
    intro a
    rw [Array.count_erase]
    have h_mem : xs.max h ∈ xs := by grind
    rw [Array.count_pop, Array.mergeSort_perm.count_eq,
      ← Array.max?_eq_back?, Array.mergeSort_perm.max?_eq,
      Array.max?_eq_some_max]
    · simp
    · grind
    · simp only [Std.max_eq_right_iff]
      simpa using Array.pairwise_mergeSort (α := Int) (le := (· ≤ ·)) (by grind) (by grind)

theorem mergeSort_erase_min {xs : Array Int} {h} :
    (xs.erase (xs.min h)).mergeSort = xs.mergeSort.drop 1 := by
  apply Array.Perm.eq_of_pairwise (le := (· ≤ ·))
  · grind
  · simpa using Array.pairwise_mergeSort (α := Int) (le := (· ≤ ·)) (by grind) (by grind)
  · apply List.Pairwise.toList_arrayDrop
    simpa using Array.pairwise_mergeSort (α := Int) (le := (· ≤ ·)) (by grind) (by grind)
  · refine Array.Perm.trans Array.mergeSort_perm ?_
    simp only [Array.perm_iff_toList_perm, List.perm_iff_count, Array.count_toList]
    intro a
    rw [Array.count_erase]
    have h_mem : xs.max h ∈ xs := by grind
    rw [Array.count_drop_one, Array.mergeSort_perm.count_eq,
      ← Array.min?_eq_getElem?_zero, Array.mergeSort_perm.min?_eq,
      Array.min?_eq_some_min]
    · simp
    · grind
    · simp only [Std.min_eq_left_iff]
      simpa using Array.pairwise_mergeSort (α := Int) (le := (· ≤ ·)) (by grind) (by grind)

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
    | 0 => grind [Array.getElem_zero_mergeSort]
    | 1 =>
      simp [Array.getElem_size_sub_one_mergeSort, maximum, withoutMin]
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
      have : withoutMinMax.mergeSort = xs.mergeSort.extract 1 (xs.toList.mergeSort.length - 1) := by
        simp only [withoutMinMax, maximum, mergeSort_erase_max]
        simp only [withoutMin, minimum, mergeSort_erase_min]
        -- TODO: simplify the following as soon as the `Array.take/drop` API is merged
        simp only [← Array.extract_eq_pop, Array.drop_eq_extract, Array.extract_extract]
        simp only [Nat.add_zero, Array.size_mergeSort, Array.size_extract, Std.le_refl,
          Nat.min_eq_left, List.length_mergeSort, Array.length_toList]
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
