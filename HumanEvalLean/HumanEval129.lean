module

import Std
import all Init.Data.Range.Polymorphic.RangeIterator
open Std Std.Do

set_option mvcgen.warning false

/-!
## Missing Api
-/

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

def Std.Iter.zipIdx [Iterator α Id β] (it : Iter (α := α) β) :=
  (it.zip (*...* : Std.Rii Nat).iter : Iter (β × Nat))

instance [Iterator α Id β] [Iterators.Productive α Id] : Membership β (Iter (α := α) β) where
  mem it x := ∃ n : Nat, it.atIdxSlow? n = some x

theorem Std.Iter.mem_toList_iff [Iterator α Id β] [Iterators.Finite α Id]
    {it : Iter (α := α) β} {x : β} :
    x ∈ it.toList ↔ x ∈ it := by
  simp only [instMembershipIterOfProductiveId_humanEvalLean, List.mem_iff_getElem,
    List.getElem_eq_getElem?_get, getElem?_toList_eq_atIdxSlow?]
  apply Iff.intro
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, by grind⟩
  · rintro ⟨i, h⟩
    simp only [← getElem?_toList_eq_atIdxSlow?, Option.eq_some_iff_get_eq, get_getElem?,
      isSome_getElem?] at h ⊢
    exact ⟨i, h⟩

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

theorem Std.Iter.mem_zipIdx_iff [Iterator α Id β]
    [Iterators.Finite α Id] {it : Iter (α := α) β}
    {p : β × Nat} :
    p ∈ it.zipIdx ↔ it.atIdxSlow? p.2 = some p.1 := by
  simp only [zipIdx, mem_zip_iff, ← getElem?_toList_eq_atIdxSlow?,
    atIdxSlow?_eq_getElem?_toList_take, Nat.toList_take_iter_rii, Nat.getElem?_toList_rio_eq_some_iff]
  grind

theorem Array.atIdxSlow?_iter {xs : Array α} {i : Nat} :
    xs.iter.atIdxSlow? i = xs[i]? := by
  grind [=_ Iter.getElem?_toList_eq_atIdxSlow?]

theorem Vector.atIdxSlow?_iter {xs : Vector α n} {i : Nat} :
    xs.iter.atIdxSlow? i = xs[i]? := by
  simp [Vector.iter, Array.atIdxSlow?_iter]

theorem Array.mem_iter_iff {xs : Array α} {x : α} :
    x ∈ xs.iter ↔ x ∈ xs := by
  simp only [instMembershipIterOfProductiveId_humanEvalLean]
  simp only [atIdxSlow?_iter, mem_iff_getElem]
  grind

theorem Vector.mem_iter_iff {xs : Vector α n} {x : α} :
    x ∈ xs.iter ↔ x ∈ xs := by
  simp [Vector.iter, Array.mem_iter_iff]

theorem Vector.mem_zipIdx_iter_iff {xs : Vector α n} {p : α × Nat} :
    p ∈ xs.iter.zipIdx ↔ ∃ (h : p.2 < n), xs[p.2] = p.1 := by
  rw [Iter.mem_zipIdx_iff, Vector.atIdxSlow?_iter]
  grind

theorem Std.Iter.mem_of_mem_zipIdx [Iterator α Id β] [Iterators.Productive α Id]
    {it : Iter (α := α) β} {p : β × Nat} (h : p ∈ it.zipIdx) :
    p.1 ∈ it := by
  simp only [zipIdx, mem_zip_iff] at h
  obtain ⟨n, hn, _⟩ := h
  exact ⟨n, hn⟩

theorem Std.Iter.toList_zipIdx [Iterator α Id β] [Iterators.Finite α Id] (it : Iter (α := α) β) :
    it.zipIdx.toList = it.toList.zipIdx := by
  simp only [zipIdx, toList_zip_of_finite_left, Nat.toList_take_iter_rii, Nat.toList_rio_eq_toList_rco, ← List.range_eq_toList_rco]
  simp only [List.zipIdx_eq_zip_range', List.range_eq_range']

theorem Std.Iter.lt_count_of_mem_zipIdx [Iterator α Id β]
    [IteratorLoop α Id Id] [LawfulIteratorLoop α Id Id]
    [Iterators.Finite α Id] {it : Iter (α := α) β} {p : β × Nat}
    (h : p ∈ it.zipIdx) :
    p.2 < it.count := by
  simp only [zipIdx] at h
  simp only [mem_zip_iff] at h
  simp only [← getElem?_toList_eq_atIdxSlow?] at h
  obtain ⟨n, hn, h⟩ := h
  simp only [List.getElem?_eq_some_iff] at hn
  obtain ⟨hn, _⟩ := hn
  simp only [atIdxSlow?_eq_getElem?_toList_take] at h
  grind [length_toList_eq_count, Nat.getElem_toList_rio, Nat.toList_take_iter_rii]

theorem List.isSome_findSome?_eq {xs : List α} {f : α → Option β} :
    (xs.findSome? f).isSome = xs.any (f · |>.isSome) := by
  rw [Bool.eq_iff_iff]
  simp only [Option.isSome_iff_ne_none, ne_eq, findSome?_eq_none_iff, Classical.not_forall]
  simp only [← Option.isSome_iff_ne_none]
  grind

theorem Std.Rxc.Iterator.nodup_toList [LE α] [DecidableLE α]
    [PRange.UpwardEnumerable α] [Rxc.IsAlwaysFinite α] [PRange.LawfulUpwardEnumerable α]
    [PRange.LawfulUpwardEnumerableLE α]
    {it : Iter (α := Rxc.Iterator α) α} :
    it.toList.Nodup := by
  apply (Rxc.Iterator.pairwise_toList_upwardEnumerableLt it).imp
  grind [PRange.UpwardEnumerable.ne_of_lt]

theorem Std.Rcc.nodup_toList [LE α] [DecidableLE α]
    [PRange.UpwardEnumerable α] [Rxc.IsAlwaysFinite α] [PRange.LawfulUpwardEnumerable α]
    [PRange.LawfulUpwardEnumerableLE α]
    {a b : α} :
    (a...=b).toList.Nodup := by
  grind [=_ Std.Rcc.toList_iter, Std.Rxc.Iterator.nodup_toList]

theorem Vector.getElem_eq_getElem_toList {xs : Vector α n} {i : Nat} {hi : i < n} :
    xs[i] = xs.toList[i]'(by grind) := by
  simp

section Mathlib
set_option warn.sorry false

theorem List.Nodup.getElem_inj_iff {l : List α} (h : List.Nodup l)
    {i : Nat} {hi : i < l.length} {j : Nat} {hj : j < l.length} :
    l[i] = l[j] ↔ i = j := by
  sorry

protected def Nat.findX {p : Nat → Prop}  (h : ∃ n, p n) : { n // p n ∧ ∀ m < n, ¬p m } := sorry
protected def Nat.find {p : Nat → Prop} (h : ∃ n, p n) : Nat := (Nat.findX h).1
protected theorem Nat.find_spec {p : Nat → Prop} (h : ∃ n, p n) : p (Nat.find h) :=
  (Nat.findX h).2.left

-- slightly deviates from mathlib's formulation
protected theorem Nat.le_find_iff {p : Nat → Prop} (h : ∃ n, p n) {n : Nat} : n ≤ Nat.find h ↔ ∀ m, p m → n ≤ m := by
  sorry

protected theorem Nat.find_le {p : Nat → Prop} {h : ∃ n, p n} (hn : p n) : Nat.find h ≤ n :=
  sorry

end Mathlib

section Batteries
set_option warn.sorry false

/-- `IsChain R l` means that `R` holds between adjacent elements of `l`.
```
IsChain R [a, b, c, d] ↔ R a b ∧ R b c ∧ R c d
``` -/
inductive List.IsChain (R : α → α → Prop) : List α → Prop where
  /-- A list of length 0 is a chain. -/
  | nil : IsChain R []
  /-- A list of length 1 is a chain. -/
  | singleton (a : α) : IsChain R [a]
  /-- If `a` relates to `b` and `b::l` is a chain, then `a :: b :: l` is also a chain. -/
  | cons_cons (hr : R a b) (h : IsChain R (b :: l)) : IsChain R (a :: b :: l)


theorem List.isChain_iff_getElem {l : List α} :
    IsChain R l ↔ ∀ (i : Nat) (_hi : i + 1 < l.length), R l[i] l[i + 1] := by
  sorry

theorem List.isChain_of_isChain_cons (p : List.IsChain R (b :: l)) :
    List.IsChain R l := by
  sorry

end Batteries

/-!
## Implementation
-/

def coordsOf? (grid : Vector (Vector Nat n) m) (l : Nat) : Option (Nat × Nat) :=
    grid.iter.zipIdx.findSome? (fun (row, x) =>
        row.iter.zipIdx.findSome? (fun (cell, y) =>
            if cell = l then some (x, y) else none))

@[grind →]
theorem coordsOf?_spec {grid : Vector (Vector Nat n) m} {l : Nat} {p : Nat × Nat}
    (h : coordsOf? grid l = some p) :
    ∃ (_ : p.1 < m) (_ : p.2 < n), grid[p.1][p.2] = l := by
  simp only [coordsOf?, ← Iter.findSome?_toList] at h
  obtain ⟨⟨row, x'⟩, h₁, h⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨y', h₂, h⟩ := List.exists_of_findSome?_eq_some h
  grind [Iter.mem_toList_iff, Vector.mem_zipIdx_iter_iff]

def leastNeighborValue (grid : Vector (Vector Nat n) n) (coords : Nat × Nat)
    (hxy : coords.1 < n ∧ coords.2 < n := by grind) : Nat := Id.run do
  match coords with
  | (x, y) =>
    -- One of the following `if` statements will overwrite this default value because
    -- the cell at position `p` has at least one neighboring cell, and the value of all cells
    -- is at most `n * n`.
    let mut val := n * n + 1
    if 0 < x then
      val := min val grid[x - 1][y]
    if 0 < y then
      val := min val grid[x][y - 1]
    if hx : x + 1 < n then
      val := min val grid[x + 1][y]
    if hy : y + 1 < n then
      val := min val grid[x][y + 1]
    return val

def minPath (grid : Vector (Vector Nat n) n) (k : Nat) : List Nat := Id.run do
  match h : coordsOf? grid 1 with
  | some coords =>
    let val := leastNeighborValue grid coords
    let mut result := if k % 2 = 1 then [1] else []
    for _ in *...(k / 2) do
      result := 1 :: val :: result
    return result
  | none => return []

/-!
## Tests
-/

example : minPath #v[
  #v[1, 2, 3],
  #v[4, 5, 6],
  #v[7, 8, 9]] 3 = [1, 2, 1] := by native_decide

example : minPath #v[
  #v[5, 9, 3],
  #v[4, 1, 6],
  #v[7, 8, 2]] 1 = [1] := by native_decide

example : minPath #v[
  #v[1, 2, 3, 4],
  #v[5, 6, 7, 8],
  #v[9, 10, 11, 12],
  #v[13, 14, 15, 16]] 4 = [1, 2, 1, 2] := by native_decide

example : minPath #v[
  #v[6, 4, 13, 10],
  #v[5, 7, 12, 1],
  #v[3, 16, 11, 15],
  #v[8, 14, 9, 2]] 7 = [1, 10, 1, 10, 1, 10, 1] := by native_decide

example : minPath #v[
  #v[8, 14, 9, 2],
  #v[6, 4, 13, 15],
  #v[5, 7, 1, 12],
  #v[3, 10, 11, 16]] 5 = [1, 7, 1, 7, 1] := by native_decide

example : minPath #v[
  #v[11, 8, 7, 2],
  #v[5, 16, 14, 4],
  #v[9, 3, 15, 6],
  #v[12, 13, 10, 1]] 9 = [1, 6, 1, 6, 1, 6, 1, 6, 1] := by native_decide

example : minPath #v[
  #v[12, 13, 10, 1],
  #v[9, 3, 15, 6],
  #v[5, 16, 14, 4],
  #v[11, 8, 7, 2]] 12 = [1, 6, 1, 6, 1, 6, 1, 6, 1, 6, 1, 6] := by native_decide

example : minPath #v[
  #v[2, 7, 4],
  #v[3, 1, 5],
  #v[6, 8, 9]] 8 = [1, 3, 1, 3, 1, 3, 1, 3] := by native_decide

example : minPath #v[
  #v[6, 1, 5],
  #v[3, 8, 9],
  #v[2, 7, 4]] 8 = [1, 5, 1, 5, 1, 5, 1, 5] := by native_decide

example : minPath #v[
  #v[1, 2],
  #v[3, 4]] 10 = [1, 2, 1, 2, 1, 2, 1, 2, 1, 2] := by native_decide

example : minPath #v[
  #v[1, 3],
  #v[3, 2]] 10 = [1, 3, 1, 3, 1, 3, 1, 3, 1, 3] := by native_decide

/-!
## Verification

We model the grid as `grid : Vector (Vector Nat n) n` such that `grid.flatten` is a permutation of
`1...=(n * n)`. This property is captured in the `WFGrid` predicate. Moreover, we are allowed to
assume that the grid has a side length `n ≥ 2`.

The following lemmas fully characterize and formally verify `minPath`:

* `length_minPath`: The length of the path returned by `minPath` is exactly `k`.
* `map_getElem_minCoordPath`: `minCoordPath` is the list of coordinates of `minPath`'s entries.
* `isChain_areNeighbors_minCoordPath`: Consecutive elements of `minCoordPath` are neighbors.
* `minPath_le_of_isChain_areNeighbors`: The path returned by `minPath` is lexicographically minimal
-/

/--
States that the given grid is well-formed in the sense that its entries are exactly the numbers
from `1` to `n * n` in arbitrary order.
-/
def WFGrid (grid : Vector (Vector Nat n) n) : Prop :=
  grid.flatten.toList.Perm (1...=(n * n)).toList

/--
States that the two pairs of coordinates are next to each other, either horizontally or vertically.
This relation does not impose any bounds on the coordinates.
-/
inductive AreNeighbors : (p q : Nat × Nat) → Prop
  | left : AreNeighbors (x + 1, y) (x, y)
  | right : AreNeighbors (x, y) (x + 1, y)
  | up : AreNeighbors (x, y) (x, y + 1)
  | down : AreNeighbors (x, y + 1) (x, y)

/--
The list of coordinates of `minPath`'s entries.
-/
def minCoordPath (grid : Vector (Vector Nat n) n) (k : Nat) : List (Nat × Nat) :=
    (minPath grid k).map (fun val => (coordsOf? grid val).get!)

theorem getElem!_mem_rcc {grid : Vector (Vector Nat n) n} (hg : WFGrid grid) (hx : x < n) (hy : y < n) :
    grid[x]![y]! ∈ 1...=(n * n) := by
  simp only [← Std.Rcc.mem_toList_iff_mem]
  apply hg.mem_iff.mp
  simp only [Vector.mem_toList_iff]
  apply Vector.mem_flatten_of_mem (xs := grid[x]) <;> grind

theorem getElem_mem_rcc {grid : Vector (Vector Nat n) n} (hg : WFGrid grid) (hx : x < n) (hy : y < n) :
    grid[x][y] ∈ 1...=(n * n) := by
  have := getElem!_mem_rcc hg hx hy
  grind

theorem getElem_grid_inj {grid : Vector (Vector Nat n) n}
    (hg : WFGrid grid) {p q : Nat × Nat} (hp : p.1 < n ∧ p.2 < n) (hq : q.1 < n ∧ q.2 < n)
    (h : grid[p.1][p.2] = grid[q.1][q.2]) :
    p = q := by
  have hnodup : List.Nodup grid.flatten.toList := by
    apply hg.nodup_iff.mpr
    apply Rcc.nodup_toList
  suffices n * p.1 + p.2 = n * q.1 + q.2 by
    ext
    · have (p : Nat × Nat) (hp : p.1 < n ∧ p.2 < n) : p.1 = (n * p.1 + p.2) / n := by
        simp only [Nat.mul_add_div (show 0 < n by grind)]
        grind [Nat.div_eq_zero_iff]
      grind
    · have (p : Nat × Nat) (hp : p.1 < n ∧ p.2 < n) : p.2 = (n * p.1 + p.2) % n := by
        simp [Nat.mod_eq_of_lt hp.2]
      grind
  have (p : Nat × Nat) (h : p.1 < n ∧ p.2 < n) : n * p.1 + p.2 < n * n := by
    have : n * n = n * (n - 1) + n * 1 := by rw [← Nat.mul_add, Nat.sub_add_cancel (by grind)]
    have : n * p.1 ≤ n * (n - 1) := Nat.mul_le_mul_left n (by grind)
    grind
  have (p : Nat × Nat) (h : p.1 < n ∧ p.2 < n) :
      haveI := this p h; grid[p.fst][p.snd] = grid.flatten[n * p.fst + p.snd] := by
    haveI := this p h
    simp only [Vector.getElem_flatten, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt h.2]
    have hn0 : 0 < n := by grind
    simp only [Nat.mul_add_div hn0]
    grind [Nat.div_eq_zero_iff]
  rw [this p hp, this q hq] at h
  simp only [Vector.getElem_eq_getElem_toList] at h
  rwa [← hnodup.getElem_inj_iff]

theorem AreNeighbors.symm {p q} (h : AreNeighbors p q) : AreNeighbors q p := by
  grind [AreNeighbors]

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

theorem exists_areNeighbors {p : Nat × Nat} (hn : 1 < n) (hp : p.1 < n ∧ p.2 < n) :
    ∃ q, (q.1 < n ∧ q.2 < n) ∧ AreNeighbors p q := by
  by_cases hx : 0 < p.1
  · have := AreNeighbors.left (x := p.1 - 1) (y := p.2)
    exact ⟨(p.1 - 1, p.2), by grind⟩
  · have := AreNeighbors.right (x := p.1) (y := p.2)
    exact ⟨(p.1 + 1, p.2), by grind⟩

theorem exists_exists_areNeighbors {grid : Vector (Vector Nat n) n}
    {p : Nat × Nat} (hn : 1 < n) (hp : p.1 < n ∧ p.2 < n) :
    ∃ (k : Nat) (q : Nat × Nat) (_ : q.1 < n ∧ q.2 < n), k = grid[q.1][q.2] ∧ AreNeighbors p q := by
  grind [exists_areNeighbors]

theorem le_leastNeighborValue_iff {grid : Vector (Vector Nat n) n} {coords : Nat × Nat}
    (hn : 1 < n) (hg : WFGrid grid) (hc : coords.1 < n ∧ coords.2 < n) :
    k ≤ leastNeighborValue grid coords ↔ ∀ coords' (_ : coords'.1 < n ∧ coords'.2 < n), AreNeighbors coords coords' → k ≤ grid[coords'.1][coords'.2] := by
  generalize hwp : leastNeighborValue grid coords = wp
  apply Id.of_wp_run_eq hwp
  mvcgen +jp
  rename_i val₀ _ val₁ _ _ val₂ _ _ val₃ _ _ val₄ _ h₁ h₂ h₃ h₄
  apply Iff.intro
  · intro h coords' hcoords' hnb
    cases hnb <;> grind
  · intro h
    obtain ⟨q, hq, h'⟩ := exists_areNeighbors (p := coords) hn hc
    have hsq := h q hq h'
    have : grid[q.1][q.2] < n * n + 1 := by
      have : grid[q.1][q.2] ∈ (1...=(n * n)).toList := hg.mem_iff.mp (by simp [Vector.mem_flatten]; simp only [Vector.mem_iff_getElem]; grind)
      simp only [Std.Rcc.mem_iff, Std.Rcc.mem_toList_iff_mem] at this
      grind
    replace h (x' y' : Nat) (hlt : x' < n ∧ y' < n) (hnb : AreNeighbors coords (x', y')) :
        k ≤ grid[x'][y'] := h (x', y') hlt hnb
    have : k ≤ val₀ := by grind
    have : k ≤ val₁ := by split at h₁ <;> (simp only [h₁, le_min_iff]; grind)
    have : k ≤ val₁ := by split at h₁ <;> (simp only [h₁, le_min_iff]; grind)
    have : k ≤ val₂ := by split at h₂ <;> (simp only [h₂, le_min_iff]; grind)
    have : k ≤ val₃ := by split at h₃ <;> (simp only [h₃, le_min_iff]; grind)
    split at h₄ <;> (simp only [h₄, le_min_iff]; grind)

theorem leastNeighborValue_eq_natFind {grid : Vector (Vector Nat n) n} {p : Nat × Nat}
    (hn : 1 < n) (hg : WFGrid grid) (hp : p.1 < n ∧ p.2 < n) :
    leastNeighborValue grid p = Nat.find (exists_exists_areNeighbors (grid := grid) hn hp) := by
  apply le_antisymm
  · simp only [Nat.le_find_iff]
    grind [le_leastNeighborValue_iff]
  · simp only [le_leastNeighborValue_iff hn hg hp]
    intro q hq hnb
    apply Nat.find_le
    grind

theorem leastNeighborValue_mem_rcc {grid : Vector (Vector Nat n) n} {p : Nat × Nat}
    (hn : 1 < n) (hg : WFGrid grid) (hp : p.1 < n ∧ p.2 < n) :
    leastNeighborValue grid p ∈ 1...=(n * n) := by
  rw [leastNeighborValue_eq_natFind hn hg hp]
  have := Nat.find_spec (exists_exists_areNeighbors (grid := grid) hn hp)
  grind [getElem_mem_rcc]

theorem leastNeighborValue_le {grid : Vector (Vector Nat n) n} {p q : Nat × Nat}
    (hn : 1 < n) (hg : WFGrid grid) (hp : p.1 < n ∧ p.2 < n) (hq : q.1 < n ∧ q.2 < n)
    (hnb : AreNeighbors p q) :
    leastNeighborValue grid p ≤ grid[q.1][q.2] := by
  rw [leastNeighborValue_eq_natFind hn hg hp]
  apply Nat.find_le
  grind

theorem isSome_coordsOf? {grid : Vector (Vector Nat n) n} (h : WFGrid grid)
    (hl : l ∈ 1...=(n * n)) :
    (coordsOf? grid l).isSome := by
  simp only [WFGrid] at h
  have : l ∈ grid.flatten.toList := h.mem_iff.mpr (by simpa [Std.Rcc.mem_toList_iff_mem])
  simp [Vector.flatten, Vector.toList_toArray] at this
  obtain ⟨xs, ⟨⟨col, h_col_mem, heq⟩, h_l_mem⟩⟩ := this
  simp only [Vector.mem_iff_getElem] at h_col_mem
  obtain ⟨x, hx, hcol⟩ := h_col_mem
  simp only [List.mem_iff_getElem] at h_l_mem
  obtain ⟨y, hy, hcell⟩ := h_l_mem
  simp only [coordsOf?, ← Iter.findSome?_toList, Iter.toList_zipIdx, Vector.toList_iter,
    List.isSome_findSome?_eq, List.any_eq_true, List.mem_zipIdx_iff_getElem?]
  exact ⟨⟨col, x⟩, by grind, ⟨l, y⟩, by grind⟩

theorem isSome_coordsOf?_one {grid : Vector (Vector Nat n) n} (hn : 0 < n) (h : WFGrid grid) :
    (coordsOf? grid 1).isSome := by
  apply isSome_coordsOf? h
  grind [Rcc.mem_iff, Nat.le_mul_self n]

theorem get!_coordsOf?_getElem {grid : Vector (Vector Nat n) n} {p : Nat × Nat}
    (hg : WFGrid grid) (hx : p.1 < n ∧ p.2 < n) :
    (coordsOf? grid grid[p.1][p.2]).get! = p := by
  have hl : grid[p.1][p.2] ∈ 1...=(n * n) := by grind [getElem_mem_rcc]
  have := isSome_coordsOf? hg hl
  have := coordsOf?_spec (p := (coordsOf? grid grid[p.1][p.2]).get!) (l := grid[p.1][p.2]) (grid := grid) (by grind [Option.some_get!])
  apply getElem_grid_inj hg <;> grind

theorem areNeighbors_coordsOf?_leastNeighborValue {grid : Vector (Vector Nat n) n} {p : Nat × Nat}
    (hn : 1 < n) (hg : WFGrid grid) (hp : p.1 < n ∧ p.2 < n) :
    AreNeighbors p (coordsOf? grid (leastNeighborValue grid p)).get! := by
  rw [leastNeighborValue_eq_natFind hn hg hp]
  have := Nat.find_spec (exists_exists_areNeighbors (grid := grid) hn hp)
  grind [get!_coordsOf?_getElem]

theorem get_coordsOf?_bounds {grid : Vector (Vector Nat n) n} {l : Nat} {h} :
    ((coordsOf? grid l).get h).fst < n ∧ ((coordsOf? grid l).get h).snd < n := by
  have : coordsOf? grid l = some ((coordsOf? grid l).get!.fst, (coordsOf? grid l).get!.snd) := by grind [Option.some_get!]
  grind [coordsOf?_spec]

theorem get!_coordsOf?_bounds {grid : Vector (Vector Nat n) n} {l : Nat}
    (hg : WFGrid grid) (hl : l ∈ 1...=(n * n)) :
    (coordsOf? grid l).get!.fst < n ∧ (coordsOf? grid l).get!.snd < n := by
  grind [coordsOf?_spec, Option.some_get!, isSome_coordsOf?]

theorem getElem_get!_coordsOf? {grid : Vector (Vector Nat n) n} {l : Nat} (hg : WFGrid grid)
    (hl : l ∈ 1...=n * n) :
    letI coords := (coordsOf? grid l).get!
    haveI := get!_coordsOf?_bounds hg hl
    grid[coords.1][coords.2] = l := by
  have := isSome_coordsOf? hg hl
  have : coordsOf? grid l = some ((coordsOf? grid l).get!.fst, (coordsOf? grid l).get!.snd) := by grind [Option.some_get!]
  grind [coordsOf?_spec]

theorem getElem!_get!_coordsOf? {grid : Vector (Vector Nat n) n} {l : Nat}
    (hg : WFGrid grid) (hl : l ∈ 1...=n * n) :
    letI coords := (coordsOf? grid l).get!
    haveI := get!_coordsOf?_bounds hg hl
    grid[coords.1]![coords.2]! = l := by
  have := isSome_coordsOf? hg hl
  have : coordsOf? grid l = some ((coordsOf? grid l).get!.fst, (coordsOf? grid l).get!.snd) := by grind [Option.some_get!]
  grind [coordsOf?_spec]

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
    let val := (leastNeighborValue grid coords (by grind))
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

theorem getElem_minPath_mem_rcc {grid : Vector (Vector Nat n) n} {k : Nat} (hn : 1 < n)
    (hg : WFGrid grid) {i : Nat} {h : i < (minPath grid k).length} :
    (minPath grid k)[i]'h ∈ 1...=(n * n) := by
  have : 1 < n * n := lt_of_lt_of_le hn (Nat.le_mul_self n)
  by_cases i % 2 = 0
  · rw [getElem_minPath_eq_one (by grind)]
    grind [Std.Rcc.mem_iff]
  · rw [getElem_minPath_of_odd hn hg (by grind)]
    have (h : _) := get_coordsOf?_bounds (grid := grid) (l := 1) (h := h)
    grind [leastNeighborValue_mem_rcc]

theorem map_getElem_minCoordPath {grid : Vector (Vector Nat n) n} {k : Nat}
    (hn : 1 < n) (hg : WFGrid grid) :
    (minCoordPath grid k).map (fun coord => grid[coord.1]![coord.2]!) = minPath grid k := by
  simp only [minCoordPath, List.map_map]
  apply List.ext_getElem
  · grind
  · simp
    intro i hi _
    rw [getElem!_get!_coordsOf? (n := n) (by grind)]
    exact getElem_minPath_mem_rcc (by grind) hg

theorem areNeighbors_minPath {grid : Vector (Vector Nat n) n} {k i : Nat}
    (hn : 1 < n) (hg : WFGrid grid) (hi : i + 1 < k) :
    let coords₁ := (coordsOf? grid ((minPath grid k)[i]'(by grind [length_minPath]))).get!
    let coords₂ := (coordsOf? grid ((minPath grid k)[i + 1]'(by grind [length_minPath]))).get!
    AreNeighbors coords₁ coords₂ := by
  intro coords₁ coords₂
  have := coordsOf?_spec (grid := grid) (l := 1) (p := (coordsOf? grid 1).get!) (by grind [Option.some_get!, isSome_coordsOf?_one])
  by_cases h : i % 2 = 0
  · simp only [coords₁, coords₂]
    rw [getElem_minPath_eq_one (by grind), getElem_minPath_of_odd hn hg (by grind)]
    simp only [Option.get_eq_get!]
    grind [areNeighbors_coordsOf?_leastNeighborValue]
  · simp only [coords₁, coords₂]
    rw [getElem_minPath_of_odd hn hg (by grind), getElem_minPath_eq_one (by grind)]
    simp only [Option.get_eq_get!]
    grind [areNeighbors_coordsOf?_leastNeighborValue, AreNeighbors.symm]

theorem isChain_areNeighbors_minCoordPath {grid : Vector (Vector Nat n) n} {k : Nat}
    (hn : 1 < n) (hg : WFGrid grid) :
    (minCoordPath grid k).IsChain AreNeighbors := by
  simp only [List.isChain_iff_getElem]
  intro i hi
  have := areNeighbors_minPath (n := n) (k := k) (i := i) (by grind) hg (by grind [length_minPath, minCoordPath])
  simp only [minCoordPath, List.getElem_map]
  grind

theorem minPath_one {grid : Vector (Vector Nat n) n} (hn : 1 < n) (hg : WFGrid grid) :
    minPath grid 1 = [1] := by
  apply List.ext_getElem
  · grind [length_minPath]
  · grind [getElem_minPath_eq_one]

theorem minPath_add_two {grid : Vector (Vector Nat n) n} (hn : 1 < n) (hg : WFGrid grid) :
    let coords := (coordsOf? grid 1).get (isSome_coordsOf?_one (by grind) hg)
    have := coordsOf?_spec (Option.some_get (isSome_coordsOf?_one (by grind) hg)).symm
    let val := (leastNeighborValue grid coords (by grind))
    minPath grid (k + 2) = 1 :: val :: minPath grid k := by
  apply List.ext_getElem
  · grind [length_minPath]
  · intro i h₁ h₂
    by_cases hi : i % 2 = 0
    · grind [getElem_minPath_eq_one]
    · grind [getElem_minPath_of_odd]

theorem minPath_le_of_isChain_areNeighbors {grid : Vector (Vector Nat n) n} {k : Nat}
    (hn : 1 < n) (hg : WFGrid grid) {cs : List (Nat × Nat)} (hcl : cs.length = k)
    (hcb : ∀ c ∈ cs, c.1 < n ∧ c.2 < n)
    (hcc : cs.IsChain AreNeighbors) :
    (minPath grid k) ≤ cs.map (fun coord => grid[coord.1]![coord.2]!) := by
  have := length_minPath (grid := grid) (k := k) (by grind) hg
  match k with
  | 0 => grind
  | 1 =>
    match cs with
    | [] => grind
    | [c] =>
      specialize hcb c (List.mem_singleton_self _)
      simp only [minPath_one hn hg, List.map_singleton, List.cons_le_cons_iff, List.nil_le, and_true]
      have : grid[c.fst]![c.snd]! ∈ 1...=(n * n) := by grind [getElem!_mem_rcc]
      grind [Rcc.mem_iff]
    | _ :: _ :: _ => grind
  | k + 2 =>
    match cs, hcc with
    | [], _ | [_], _ => grind
    | c₁ :: c₂ :: cs, .cons_cons hnb hcc =>
      simp only [minPath_add_two hn hg, List.map_cons, List.cons_le_cons_iff]
      have : grid[c₁.fst]![c₁.snd]! ∈ 1...=(n * n) := by grind [getElem!_mem_rcc]
      by_cases 1 < grid[c₁.fst]![c₁.snd]!
      · grind
      · let coords := (coordsOf? grid 1).get!
        have := coordsOf?_spec (grid := grid) (p := coords) (l := 1) (by grind [Option.some_get!, isSome_coordsOf?_one])
        have : c₁ = (coordsOf? grid 1).get! := by
          apply getElem_grid_inj hg (by grind) (by grind)
          grind [Rcc.mem_iff]
        have : leastNeighborValue grid coords (by grind) ≤ grid[c₂.fst]![c₂.snd]! := by
          rw [getElem!_pos (h := by grind), getElem!_pos (h := by grind)]
          apply leastNeighborValue_le (by grind) hg (by grind) (by grind)
          grind
        have := minPath_le_of_isChain_areNeighbors hn hg (k := k) (cs := cs)  (by grind) (by grind) (by grind [List.isChain_of_isChain_cons])
        grind [Rcc.mem_iff, Option.get_eq_get!]

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
