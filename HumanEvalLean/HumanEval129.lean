module

import Std
import all Init.Data.Range.Polymorphic.RangeIterator
open Std Std.Do

def Vector.iter (xs : Vector α n) :=
    (xs.toArray.iter : Iter α)

@[simp, grind =]
theorem Vector.toList_iter {xs : Vector α n} :
    xs.iter.toList = xs.toList := by
  simp [Vector.iter, Vector.toList_toArray]

@[simp, grind =]
theorem Vector.count_iter {xs : Vector α n} :
    xs.iter.count = n := by
  simp [Vector.iter, ← Iter.size_toArray_eq_count]

/-
Zip restructuring plan:

* have zipWith
* provide proof that there's an i s.t. x = it₁.atIdxSlow? i ∧ y = it₂.atIdxSlow? i ∧
-/

def Std.Iter.enumerate [Iterator α Id β] (it : Iter (α := α) β) :=
  (it.zip (*...* : Std.Rii Nat).iter : Iter (β × Nat))

instance [Iterator α Id β] [Iterators.Productive α Id] : Membership β (Iter (α := α) β) where
  mem it x := ∃ n : Nat, it.atIdxSlow? n = some x

theorem Std.Iter.mem_toList_iff [Iterator α Id β] [Iterators.Finite α Id]
    {it : Iter (α := α) β} {x : β} :
    x ∈ it.toList ↔ x ∈ it := by
  sorry

theorem Std.Iter.atIdxSlow?_eq_getElem?_toList_take {α β} [Iterator α Id β] [Iterators.Productive α Id]
    {it : Iter (α := α) β} {k : Nat} :
    it.atIdxSlow? k = (it.take (k + 1)).toList[k]? := by
  fun_induction it.atIdxSlow? k with
  | case1 it _ _ _ h
  | case2 it _ _ _ _ _ h
  | case3 _ it _ _ h
  | case4 _ it _ h =>
    rw [Iter.toList_eq_match_step, Iter.step_take, h]
    cases _ : it.step using PlausibleIterStep.casesOn <;> grind

theorem Std.Iter.mem_zip_iff [Iterator α₁ Id β₁] [Iterator α₂ Id β₂]
    [Iterators.Productive α₁ Id] [Iterators.Productive α₂ Id]
    {it₁ : Iter (α := α₁) β₁} {it₂ : Iter (α := α₂) β₂} {p : β₁ × β₂} :
    p ∈ it₁.zip it₂ ↔ ∃ n, it₁.atIdxSlow? n = some p.1 ∧ it₂.atIdxSlow? n = some p.2 := by
  simp only [Membership.mem, atIdxSlow?_zip]
  apply Iff.intro
  · rintro ⟨n, h⟩
    cases h₁ : it₁.atIdxSlow? n <;> cases h₂ : it₂.atIdxSlow? n <;> grind
  · rintro ⟨n, h₁, h₂⟩
    cases h₁ : it₁.atIdxSlow? n <;> cases h₂ : it₂.atIdxSlow? n <;> grind

-- TODO: remove `Nat.toList_rio_zero_right_eq_nil`
@[grind =]
theorem Nat.toList_rio_zero :
    (*...0).toList = [] := by
  simp

theorem Nat.toList_take_add_one_iter_rci {m n : Nat} :
    ((m...*).iter.take (n + 1)).toList = m :: (((m + 1)...*).iter.take n).toList := by
  rw [Iter.toList_eq_match_step, Iter.step_take]
  simp only [Std.Rxi.Iterator.step_eq_step, Rxi.Iterator.step_eq_monadicStep, Rxi.Iterator.Monadic.step]
  dsimp only [Std.Rci.iter, Iter.toIterM]
  simp [PRange.Nat.succ?_eq, IterStep.mapIterator_yield, PlausibleIterStep.yield, IterM.toIter]

theorem Nat.toList_take_iter_rci {m n : Nat} :
    ((m...*).iter.take n).toList = (m...(m + n)).toList := by
  induction n generalizing m
  · grind [Iter.toList_take_zero, toList_rco_eq_nil]
  · rename_i n ih
    rw [Nat.toList_rco_eq_cons (by grind)]
    grind [Nat.toList_take_add_one_iter_rci]

theorem Nat.toList_take_iter_rii {n : Nat} :
    ((*...* : Std.Rii Nat).iter.take n).toList = (*...n).toList := by
  simpa using Nat.toList_take_iter_rci (m := 0) (n := n)

theorem Std.Iter.mem_enumerate_iff [Iterator α Id β]
    [Iterators.Finite α Id] {it : Iter (α := α) β}
    {p : β × Nat} :
    p ∈ it.enumerate ↔ it.atIdxSlow? p.2 = some p.1 := by
  simp only [enumerate, mem_zip_iff, ← getElem?_toList_eq_atIdxSlow?,
    atIdxSlow?_eq_getElem?_toList_take, Nat.toList_take_iter_rii, Nat.getElem?_toList_rio_eq_some_iff]
  grind

theorem Vector.mem_iter_iff {xs : Vector α n} {x : α} :
    x ∈ xs.iter ↔ x ∈ xs := by
  sorry

theorem Vector.atIdxSlow?_iter {xs : Vector α n} {i : Nat} :
    xs.iter.atIdxSlow? i = xs[i]? := by
  sorry

theorem Vector.mem_enumerate_iter_iff {xs : Vector α n} {p : α × Nat} :
    p ∈ xs.iter.enumerate ↔ ∃ (h : p.2 < n), xs[p.2] = p.1 := by
  rw [Iter.mem_enumerate_iff, Vector.atIdxSlow?_iter]
  grind

theorem Std.Iter.lt_count_of_mem_enumerate [Iterator α Id β]
    [IteratorLoop α Id Id] [LawfulIteratorLoop α Id Id]
    [Iterators.Finite α Id] {it : Iter (α := α) β} {p : β × Nat}
    (h : p ∈ it.enumerate) :
    p.2 < it.count := by
  simp only [enumerate] at h
  simp only [mem_zip_iff] at h
  simp only [← getElem?_toList_eq_atIdxSlow?] at h
  obtain ⟨n, hn, h⟩ := h
  simp only [List.getElem?_eq_some_iff] at hn
  obtain ⟨hn, _⟩ := hn
  simp only [atIdxSlow?_eq_getElem?_toList_take] at h
  grind [length_toList_eq_count, Nat.getElem_toList_rio, Nat.toList_take_iter_rii]

theorem Std.Iter.mem_of_mem_enumerate [Iterator α Id β] [Iterators.Productive α Id]
    {it : Iter (α := α) β} {p : β × Nat} (h : p ∈ it.enumerate) :
    p.1 ∈ it := by
  simp only [enumerate, mem_zip_iff] at h
  obtain ⟨n, hn, _⟩ := h
  exact ⟨n, hn⟩

theorem Std.Iter.toList_enumerate [Iterator α Id β] [Iterators.Finite α Id] (it : Iter (α := α) β) :
    it.enumerate.toList = it.toList.zipIdx := by
  simp only [enumerate, toList_zip_of_finite_left, Nat.toList_take_iter_rii, Nat.toList_rio_eq_toList_rco, ← List.range_eq_toList_rco]
  simp only [List.zipIdx_eq_zip_range', List.range_eq_range']

def WFGrid (grid : Vector (Vector Nat n) n) : Prop :=
  grid.flatten.toList.Perm (1...=(n * n)).toList

theorem List.isSome_findSome? {xs : List α} {f : α → Option β} :
    (xs.findSome? f).isSome = xs.any (f · |>.isSome) := by
  rw [Bool.eq_iff_iff]
  simp only [Option.isSome_iff_ne_none, ne_eq, findSome?_eq_none_iff, Classical.not_forall]
  simp only [← Option.isSome_iff_ne_none]
  grind

def coordsOf? (grid : Vector (Vector Nat n) m) (l : Nat) : Option (Nat × Nat) :=
    grid.iter.enumerate.findSome? (fun (row, x) =>
        row.iter.enumerate.findSome? (fun (cell, y) =>
            if cell = l then some (x, y) else none))

theorem isSome_coordsOf?_one {grid : Vector (Vector Nat n) n} (hn : 0 < n) (h : WFGrid grid) :
    (coordsOf? grid 1).isSome := by
  simp only [WFGrid] at h
  simp only [coordsOf?, ← Iter.findSome?_toList, Iter.toList_enumerate, Vector.toList_iter]
  simp only [List.isSome_findSome?]
  have : 1 ∈ grid.flatten.toList := h.mem_iff.mpr (by simp [Std.Rcc.mem_toList_iff_mem, Std.Rcc.mem_iff]; grind [Nat.le_mul_self n])
  simp [Vector.flatten, Vector.toList_toArray] at this
  obtain ⟨l, ⟨⟨col, h_col_mem, heq⟩, h_one_mem⟩⟩ := this
  simp only [Vector.mem_iff_getElem] at h_col_mem
  obtain ⟨x, hx, hcol⟩ := h_col_mem
  simp only [List.mem_iff_getElem] at h_one_mem
  obtain ⟨y, hy, hcell⟩ := h_one_mem
  simp only [List.any_eq_true, List.mem_zipIdx_iff_getElem?]
  exact ⟨⟨col, x⟩, by grind, ⟨1, y⟩, by grind⟩

@[grind →]
theorem coordsOf?_spec {grid : Vector (Vector Nat n) m} {l : Nat} {x y : Nat}
    (h : coordsOf? grid l = some (x, y)) :
    ∃ (_ : x < m) (_ : y < n), grid[x][y] = l := by
  simp only [coordsOf?] at h
  simp only [← Iter.findSome?_toList] at h
  obtain ⟨⟨row, x'⟩, h₁, h⟩ := List.exists_of_findSome?_eq_some h
  simp only [Iter.mem_toList_iff, Vector.mem_enumerate_iter_iff] at h₁
  obtain ⟨hx, hrow⟩ := h₁
  obtain ⟨y', h₂, h⟩ := List.exists_of_findSome?_eq_some h
  simp only [Iter.mem_toList_iff, Vector.mem_enumerate_iter_iff] at h₂
  obtain ⟨hy, hcell⟩ := h₂
  grind

def leastNeighborValue (grid : Vector (Vector Nat n) m) (x y : Nat)
    (hxy : x < m ∧ y < n := by grind) : Nat := Id.run do
    let mut val := n * n + 1
    if 0 < x then
      val := min val grid[x - 1][y]
    if 0 < y then
      val := min val grid[x][y - 1]
    if hx : x + 1 < m then
      val := min val grid[x + 1][y]
    if hy : y + 1 < n then
      val := min val grid[x][y + 1]
    return val

def minPath (grid : Vector (Vector Nat n) n) (k : Nat) : List Nat := Id.run do
  match h : coordsOf? grid 1 with
  | none => return []
  | some (x, y) =>
    let val := leastNeighborValue grid x y
    let mut result := if k % 2 = 1 then [1] else []
    for _ in *...(k / 2) do
      result := 1 :: val :: result
    return result

theorem length_minPath {grid : Vector (Vector Nat n) n} {k : Nat} (hn : 0 < n) (h : WFGrid grid) :
    (minPath grid k).length = k := by
  generalize hwp : minPath grid k = wp
  apply Id.of_wp_run_eq hwp
  mvcgen +jp -- fails if `coordsOf? grid 1` is extracted into `let bla := ...`
  invariants
  · ⇓⟨cur, xs⟩ => ⌜xs.length = if k % 2 = 1 then 2 * cur.pos + 1 else 2 * cur.pos⌝
  with grind [isSome_coordsOf?_one, Rio.length_toList, Nat.size_rio]

theorem getElem_minPath_eq_one {grid : Vector (Vector Nat n) n} {k : Nat}
    {i : Nat} {h : i < (minPath grid k).length} (hi : i % 2 = 0) :
    (minPath grid k)[i]'h = 1 := by
  simp only [List.getElem_eq_iff]
  revert i
  generalize hwp : minPath grid k = wp
  apply Id.of_wp_run_eq hwp
  mvcgen +jp -- fails if `coordsOf? grid 1` is extracted into `let bla := ...`
  invariants
  · ⇓⟨cur, xs⟩ => ⌜∀ j (hj : j < xs.length), j % 2 = 0 → xs[j] = 1⌝
  with grind

theorem getElem_minPath_of_odd {grid : Vector (Vector Nat n) n} {k : Nat} (hn : 1 < n)
    (hg : WFGrid grid)
    {i : Nat} {h : i < (minPath grid k).length} (hi : i % 2 = 1) :
    let coords := (coordsOf? grid 1).get (isSome_coordsOf?_one (by grind) hg)
    have := coordsOf?_spec (Option.some_get (isSome_coordsOf?_one (by grind) hg)).symm
    let val := (leastNeighborValue grid coords.1 coords.2 (by grind))
    (minPath grid k)[i]'h = val := by
  intro coords _ val
  simp only [List.getElem_eq_iff]
  revert i
  generalize hwf : minPath grid k = wf
  apply Id.of_wp_run_eq hwf
  mvcgen
  invariants
  · ⇓⟨cur, xs⟩ => ⌜∀ j (hj : j < xs.length), j % 2 = 1 → xs[j] = val⌝
  with grind

inductive AreNeighbors : (p q : Nat × Nat) → Prop
  | left : AreNeighbors (x + 1, y) (x, y)
  | right : AreNeighbors (x, y) (x + 1, y)
  | up : AreNeighbors (x, y) (x, y + 1)
  | down : AreNeighbors (x, y + 1) (x, y)

@[grind .]
theorem AreNeighbors.left_of_pos {x y : Nat} (h : 0 < x) :
    AreNeighbors (x, y) (x - 1, y) := by
  have := AreNeighbors.left (x := x - 1) (y := y)
  grind

@[grind .]
theorem AreNeighbors.down_of_pos {x y : Nat} (h : 0 < y) :
    AreNeighbors (x, y) (x, y - 1) := by
  have := AreNeighbors.down (x := x) (y := y - 1)
  grind

attribute [grind .] AreNeighbors.right AreNeighbors.up

-- def IsInGrid (n : Nat) (p : Nat × Nat) : Prop :=
--     p.1 < n ∧ p.2 < n

theorem exists_areNeighbors {p : Nat × Nat} (hn : 1 < n) (hxn : p.1 < n) (hyn : p.2 < n) :
    ∃ q, q.1 < n ∧ q.2 < n ∧ AreNeighbors p q := by
  by_cases hx : 0 < p.1
  · have := AreNeighbors.left (x := p.1 - 1) (y := p.2)
    exact ⟨(p.1 - 1, p.2), by grind⟩
  · have := AreNeighbors.right (x := p.1) (y := p.2)
    exact ⟨(p.1 + 1, p.2), by grind⟩

theorem le_leastNeighborValue_iff {grid : Vector (Vector Nat n) n} {x y : Nat}
    (hn : 1 < n) (hg : WFGrid grid) (hx : x < n) (hy : y < n) :
    k ≤ leastNeighborValue grid x y ↔ ∀ x' y' (_ : x' < n) (_ : y' < n), AreNeighbors (x, y) (x', y') → k ≤ grid[x'][y'] := by
  generalize hwp : leastNeighborValue grid x y = wp
  apply Id.of_wp_run_eq hwp
  mvcgen +jp
  rename_i val₀ _ val₁ _ _ val₂ _ _ val₃ _ _ val₄ _ h₁ h₂ h₃ h₄
  apply Iff.intro
  · intro h x' y' hx' hy' hnb
    cases hnb <;> grind
  · intro h
    obtain ⟨⟨x', y'⟩, hx', hy', h'⟩ := exists_areNeighbors (p := (x, y)) hn hx hy
    have hsq := h x' y' hx' hy' h'
    have : grid[x'][y'] < n * n + 1 := by
      have : grid[x'][y'] ∈ (1...=(n * n)).toList := hg.mem_iff.mp (by simp [Vector.mem_flatten]; simp only [Vector.mem_iff_getElem]; grind)
      simp only [Std.Rcc.mem_iff, Std.Rcc.mem_toList_iff_mem] at this
      grind
    have : k ≤ val₀ := by grind
    have : k ≤ val₁ := by split at h₁ <;> (simp only [h₁, le_min_iff]; grind)
    have : k ≤ val₂ := by split at h₂ <;> (simp only [h₂, le_min_iff]; grind)
    have : k ≤ val₃ := by split at h₃ <;> (simp only [h₃, le_min_iff]; grind)
    split at h₄ <;> (simp only [h₄, le_min_iff]; grind)

theorem areNeighbors_minPath {grid : Vector (Vector Nat n) n} {k i : Nat}
    (hn : 1 < n) (hg : WFGrid grid) (hi : i + 1 < k) :
    ∃ (p q : Nat × Nat) (_ : p.1 < n) (_ : p.2 < n) (_ : q.1 < n) (_ : q.2 < n),
      AreNeighbors p q ∧
      grid[p.1][p.2] = (minPath grid k)[i]! ∧
      grid[q.1][q.2] = (minPath grid k)[i + 1]! := by
  by_cases h : i % 2 = 0
  · let coordsOfFst := (coordsOf? grid 1).get!
    refine ⟨coordsOfFst, ?_⟩
    let coordsOfSnd :=
    conv =>
      congr; ext p; congr; ext q; congr; ext; congr; ext; congr; ext; congr; ext
      rw [getElem_minPath_eq_one h, getElem_minPath_of_odd (by grind) hg (by grind)]
    sorry


/-!
## Prompt

```python3

def minPath(grid, k):
    """
    Given a grid with N rows and N columns (N >= 2) and a positive integer k,
    each cell of the grid contains a value. Every integer in the range [1, N * N]
    inclusive appears exactly once on the cells of the grid.

    You have to find the minimum path of length k in the grid. You can start
    from any cell, and in each step you can move to any of the neighbor cells,
    in other words, you can go to cells which share an edge with you current
    cell.
    Please note that a path of length k means visiting exactly k cells (not
    necessarily distinct).
    You CANNOT go off the grid.
    A path A (of length k) is considered less than a path B (of length k) if
    after making the ordered lists of the values on the cells that A and B go
    through (let's call them lst_A and lst_B), lst_A is lexicographically less
    than lst_B, in other words, there exist an integer index i (1 <= i <= k)
    such that lst_A[i] < lst_B[i] and for any j (1 <= j < i) we have
    lst_A[j] = lst_B[j].
    It is guaranteed that the answer is unique.
    Return an ordered list of the values on the cells that the minimum path go through.

    Examples:

        Input: grid = [ [1,2,3], [4,5,6], [7,8,9]], k = 3
        Output: [1, 2, 1]

        Input: grid = [ [5,9,3], [4,1,6], [7,8,2]], k = 1
        Output: [1]
    """
```

## Canonical solution

```python3
    n = len(grid)
    val = n * n + 1
    for i in range(n):
        for j in range(n):
            if grid[i][j] == 1:
                temp = []
                if i != 0:
                    temp.append(grid[i - 1][j])

                if j != 0:
                    temp.append(grid[i][j - 1])

                if i != n - 1:
                    temp.append(grid[i + 1][j])

                if j != n - 1:
                    temp.append(grid[i][j + 1])

                val = min(temp)

    ans = []
    for i in range(k):
        if i % 2 == 0:
            ans.append(1)
        else:
            ans.append(val)
    return ans
```

## Tests

```python3
def check(candidate):

    # Check some simple cases
    print
    assert candidate([[1, 2, 3], [4, 5, 6], [7, 8, 9]], 3) == [1, 2, 1]
    assert candidate([[5, 9, 3], [4, 1, 6], [7, 8, 2]], 1) == [1]
    assert candidate([[1, 2, 3, 4], [5, 6, 7, 8], [9, 10, 11, 12], [13, 14, 15, 16]], 4) == [1, 2, 1, 2]
    assert candidate([[6, 4, 13, 10], [5, 7, 12, 1], [3, 16, 11, 15], [8, 14, 9, 2]], 7) == [1, 10, 1, 10, 1, 10, 1]
    assert candidate([[8, 14, 9, 2], [6, 4, 13, 15], [5, 7, 1, 12], [3, 10, 11, 16]], 5) == [1, 7, 1, 7, 1]
    assert candidate([[11, 8, 7, 2], [5, 16, 14, 4], [9, 3, 15, 6], [12, 13, 10, 1]], 9) == [1, 6, 1, 6, 1, 6, 1, 6, 1]
    assert candidate([[12, 13, 10, 1], [9, 3, 15, 6], [5, 16, 14, 4], [11, 8, 7, 2]], 12) == [1, 6, 1, 6, 1, 6, 1, 6, 1, 6, 1, 6]
    assert candidate([[2, 7, 4], [3, 1, 5], [6, 8, 9]], 8) == [1, 3, 1, 3, 1, 3, 1, 3]
    assert candidate([[6, 1, 5], [3, 8, 9], [2, 7, 4]], 8) == [1, 5, 1, 5, 1, 5, 1, 5]

    # Check some edge cases that are easy to work out by hand.
    assert candidate([[1, 2], [3, 4]], 10) == [1, 2, 1, 2, 1, 2, 1, 2, 1, 2]
    assert candidate([[1, 3], [3, 2]], 10) == [1, 3, 1, 3, 1, 3, 1, 3, 1, 3]

```
-/
