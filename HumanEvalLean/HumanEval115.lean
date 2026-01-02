module

public import Std
open Std

/-!
## Implementation
-/

def maxFill (grid : Array (Vector Nat n)) (capacity : Nat) : Nat :=
  grid.iter.map (fun well => (well.sum + capacity - 1) / capacity) |>.fold (init := 0) (· + ·)

/-!
# Tests
-/

example : maxFill #[#v[0,0,1,0], #v[0,1,0,0], #v[1,1,1,1]]              1 = 6 := by native_decide
example : maxFill #[#v[0,0,1,1], #v[0,0,0,0], #v[1,1,1,1], #v[0,1,1,1]] 2 = 5 := by native_decide
example : maxFill #[#v[0,0,0],   #v[0,0,0]]                             5 = 0 := by native_decide
example : maxFill #[#v[1,1,1,1], #v[1,1,1,1]]                           2 = 4 := by native_decide
example : maxFill #[#v[1,1,1,1], #v[1,1,1,1]]                           9 = 2 := by native_decide

/-!
## Verification

This problem's implementation is not very complex and it is not clear how a specification
should look like.
-/

def Vector.modify (xs : Vector α n) (i : Nat) (f : α → α) : Vector α n :=
  ⟨xs.toArray.modify i f, by grind⟩

def WellAction (n c : Nat) := { mask : Vector Nat n // mask.sum ≤ c }
def WellAction.apply (a : WellAction n c) (well : Vector Nat n) : Vector Nat n :=
  (well.zip a.val).map (fun (given, lower) => given - lower)

def Action (m n c : Nat) := Fin m × WellAction n c
def Action.apply (a : Action m n c) (grid : Vector (Vector Nat n) m) : Vector (Vector Nat n) m :=
  grid.modify a.1 a.2.apply

def IsWellEmpty (well : Vector Nat n) : Bool := well.all (· = 0)
def IsGridEmpty (grid : Vector (Vector Nat n) m) : Bool := grid.all IsWellEmpty

def IsMin (P : Nat → Prop) (n : Nat) : Prop := P n ∧ ∀ m, P m → n ≤ m

def MinimalGridActions (grid : Vector (Vector Nat n) m) (c : Nat) (result : Nat) : Prop :=
  IsMin
    (fun r => ∃ as : List (Action m n c),
        IsGridEmpty (as.foldr (init := grid) Action.apply) ∧ r = as.length)
    result

def MinimalWellActions (well : Vector Nat n) (c : Nat) (result : Nat) : Prop :=
  IsMin
    (fun r => ∃ as : List (WellAction n c),
        IsWellEmpty (as.foldr (init := well) WellAction.apply) ∧ r = as.length)
    result

@[ext]
structure AbstractWell where
  val : Nat

abbrev AbstractWell.IsEmpty (well : AbstractWell) : Prop :=
  well.val = 0

def AbstractWellAction (c : Nat) := Fin (c + 1)
def AbstractWellAction.apply (a : AbstractWellAction c) (well : AbstractWell) : AbstractWell :=
  AbstractWell.mk (well.val - a.val)

def MinimalAbstractWellActions (well : AbstractWell) (c : Nat) (result : Nat) : Prop :=
  IsMin (fun r => ∃ as : List (AbstractWellAction c),
      (as.foldr (init := well) AbstractWellAction.apply).IsEmpty ∧ r = as.length) result

def abstract (well : Vector Nat n) : AbstractWell :=
  AbstractWell.mk well.sum

def liftAction.go (xs : List Nat) (k : Nat) : List Nat :=
  match xs with
  | [] => []
  | x :: xs => min x k :: liftAction.go xs (k - min x k)

theorem liftAction.length_go {xs k} :
    (liftAction.go xs k).length = xs.length := by
  induction xs generalizing k <;> grind [go]

theorem liftAction.sum_go {xs k} :
    (liftAction.go xs k).sum = min k xs.sum := by
  induction xs generalizing k <;> grind [go]

-- theorem liftAction.sum_go {xs k} (h : k ≤ xs.sum) :
--     (liftAction.go xs k).sum = k := by
--   induction xs generalizing k <;> grind [go]

@[simp, grind =]
theorem Vector.sum_toList {xs : Vector Nat α} :
    xs.toList.sum = xs.sum := by
  sorry

@[simp, grind =]
theorem Vector.toList_zip {as : Vector α n} {bs : Vector β n} :
    (Vector.zip as bs).toList = List.zip as.toList bs.toList := by
  rcases as with ⟨as, rfl⟩
  rcases bs with ⟨bs, h⟩
  simp

def AbstractWellAction.lift (well : Vector Nat n) (a : AbstractWellAction c) : WellAction n c :=
  ⟨⟨(liftAction.go well.toList a.val).toArray,
      by grind [liftAction.length_go]⟩, by grind [liftAction.sum_go, Vector.sum_mk]⟩

theorem sum_sub_sum_apply_lt {well : Vector Nat n} {a : WellAction n c} :
    well.sum - (a.apply well).sum < c + 1 := by
  simp only [WellAction.apply, ← Vector.sum_toList, Vector.toList_map, Vector.toList_zip]
  have : well.toList.length = n := by grind
  generalize well.toList = ws at *
  clear well
  induction ws generalizing n a c
  · grind
  · rename_i w ws ih
    match a with
    | ⟨⟨⟨[]⟩, _⟩, _⟩ => grind
    | ⟨⟨⟨a :: as⟩, _⟩, _⟩ =>
      specialize ih (n := n - 1) (c := c - a) (a := ⟨⟨⟨as⟩, by grind⟩, by grind [Vector.sum_mk]⟩)
      grind [List.zip_cons_cons, Vector.sum_mk]

def abstractAction (well : Vector Nat n) (a : WellAction n c) : AbstractWellAction c :=
  ⟨well.sum - (a.apply well).sum, by apply sum_sub_sum_apply_lt⟩

theorem abstract_apply_liftAction {well : Vector Nat n} {a : AbstractWellAction c} :
    abstract ((a.lift well).apply well) = a.apply (abstract well) := by
  ext
  simp only [abstract, WellAction.apply, AbstractWellAction.apply]
  simp only [← Vector.sum_toList, Vector.toList_map, Vector.toList_zip, AbstractWellAction.lift,
    Vector.toList_mk]
  induction well.toList generalizing a
  · grind [liftAction.go, List.zip_nil_right]
  · rename_i w ws ih
    specialize ih (a := ⟨a.val - min w a.val, by grind⟩)
    grind [liftAction.go, List.zip_cons_cons]

theorem apply_abstractAction_abstract {well : Vector Nat n} {a : WellAction n c} :
    (abstractAction well a).apply (abstract well) = abstract (a.apply well) := by
  ext
  simp only [abstract, WellAction.apply, AbstractWellAction.apply, abstractAction]
  simp only [← Vector.sum_toList, Vector.toList_map, Vector.toList_zip]
  have : well.toList.length = n := by grind
  generalize well.toList = ws at *
  clear well
  induction ws generalizing n a c
  · grind [List.zip_nil_left]
  · rename_i w ws ih
    match a with
    | ⟨⟨⟨[]⟩, _⟩, _⟩ => grind
    | ⟨⟨⟨a :: as⟩, _⟩, _⟩ =>
      specialize ih (n := n - 1) (c := c - a) (a := ⟨⟨⟨as⟩, by grind⟩, by grind [Vector.sum_mk]⟩)
      grind [List.zip_cons_cons, Vector.sum_mk]

def liftActions (well : Vector Nat n) (as : List (AbstractWellAction c)) :
    List (WellAction n c) :=
  match as with
  | [] => []
  | a :: as => a.lift ((liftActions well as).foldr (init := well) WellAction.apply) :: liftActions well as

def abstractActions (well : Vector Nat n) (as : List (WellAction n c)) :
    List (AbstractWellAction c) :=
  match as with
  | [] => []
  | a :: as => abstractAction (as.foldr (init := well) WellAction.apply) a :: abstractActions well as

theorem abstract_apply_liftActions {well : Vector Nat n} {as : List (AbstractWellAction c)} :
    abstract (((liftActions well as).foldr (init := well) WellAction.apply)) = as.foldr (init := abstract well) AbstractWellAction.apply := by
  induction as
  · grind [liftActions]
  · grind [liftActions, abstract_apply_liftAction]

theorem apply_abstractActions_abstract {well : Vector Nat n} {as : List (WellAction n c)} :
    (abstractActions well as).foldr (init := abstract well) AbstractWellAction.apply = abstract (as.foldr (init := well) WellAction.apply) := by
  induction as
  · grind [abstractActions]
  · grind [abstractActions, apply_abstractAction_abstract]

def optimalAbstractActions (well : AbstractWell) (c : Nat) : List (AbstractWellAction c) :=
  List.replicate ((well.val + c - 1) / c) ⟨c, by grind⟩

theorem AbstractWellAction.apply_list {well : AbstractWell} {as : List (AbstractWellAction c)} :
    as.foldr (init := well) AbstractWellAction.apply = AbstractWell.mk (well.val - (as.map (·.val)).sum) := by
  induction as generalizing well
  · simp
  · grind [AbstractWellAction.apply]

theorem isEmpty_apply_optimalAbstractActions {well : AbstractWell} {c : Nat} (hc : c > 0) :
    ((optimalAbstractActions well c).foldr (init := well) AbstractWellAction.apply).IsEmpty := by
  rw [AbstractWellAction.apply_list]
  simp [AbstractWell.IsEmpty, optimalAbstractActions]
  sorry

def optimalActions (well : Vector Nat n) (c : Nat) : List (WellAction n c) :=
  liftActions well (optimalAbstractActions (abstract well) c)

theorem List.exists_mem_and {P : α → Prop} {l : List α} :
    (∃ a, a ∈ l ∧ P a) ↔ (∃ (n : Nat), ∃ h, P (l[n]'h)) := by
  refine ⟨fun ⟨a, h, h'⟩ => ?_, fun ⟨n, h, h'⟩ => ⟨l[n], by simp, h'⟩⟩
  obtain ⟨i, h'', rfl⟩ := List.getElem_of_mem h
  exact ⟨_, _, h'⟩

theorem List.sum_eq_zero {l : List Nat} : l.sum = 0 ↔
    ∀ (i : Nat) (hi : i < l.length), l[i] = 0 := by
  rw [← Decidable.not_iff_not]
  simp [← Nat.pos_iff_ne_zero, Nat.sum_pos_iff_exists_pos, List.exists_mem_and]

theorem Vector.sum_eq_zero {xs : Vector Nat n} : xs.sum = 0 ↔ ∀ (i : Nat) (hi : i < n), xs[i] = 0 := by
  rw [← Vector.sum_toList, List.sum_eq_zero]
  grind

theorem isWellEmpty_iff_isEmpty_abstract {well : Vector Nat n} :
    IsWellEmpty well ↔ (abstract well).IsEmpty := by
  grind [abstract, IsWellEmpty, Vector.sum_eq_zero]

theorem isWellEmpty_apply_optimalActions {well : Vector Nat n} {c : Nat} (hc : c > 0) :
    IsWellEmpty ((optimalActions well c).foldr (init := well) WellAction.apply) := by
  grind [isWellEmpty_iff_isEmpty_abstract, optimalActions, abstract_apply_liftActions,
    isEmpty_apply_optimalAbstractActions]

theorem length_optimalAbstractActions {well : AbstractWell} {c : Nat} :
    (optimalAbstractActions well c).length = (well.val + c - 1) / c := by
  grind [optimalAbstractActions]

theorem length_liftActions {well : Vector Nat n} {as : List (AbstractWellAction c)} :
    (liftActions well as).length = as.length := by
  induction as <;> grind [liftActions]

theorem length_optimalActions {well : Vector Nat n} {c : Nat} :
    (optimalActions well c).length = (well.sum + c - 1) / c := by
  grind [optimalActions, length_liftActions, length_optimalAbstractActions, abstract]

theorem val_le_of_isEmpty_apply_list {well : AbstractWell} {c : Nat} {as : List (AbstractWellAction c)}
    (h : (as.foldr (init := well) AbstractWellAction.apply).IsEmpty) :
    well.val ≤ (as.map (·.val)).sum := by
  grind [AbstractWellAction.apply_list]

theorem le_length_of_isEmpty_apply_list {well : AbstractWell} {c : Nat} {as : List (AbstractWellAction c)}
    (h : (as.foldr (init := well) AbstractWellAction.apply).IsEmpty) :
    (well.val + c - 1) / c ≤ as.length := by
  have := val_le_of_isEmpty_apply_list h


def nextAction (well : Vector Nat n) (c : Nat) (d : Nat) (h : c ≤ d) : WellAction n d :=
  let inner := go well.toList c
  ⟨⟨inner.val.toArray, ?ha⟩, ?hb⟩
where
  go (ws : List Nat) (c : Nat) : { ws' : List Nat // ws'.length = ws.length ∧ ws'.sum = min ws.sum c ∧ ∀ (i : Nat) h h', ws'[i]'h ≤ ws[i]'h' } :=
    match ws with
    | [] => ⟨[], rfl, by grind⟩
    | w :: ws =>
      ⟨min w c :: go ws (c - min w c), by simp [(go ws (c - min w c)).property], by have := (go ws (c - min w c)).property.2; generalize (go ws (c - min w c)).val = k at *; grind⟩
  finally
    case ha => simpa using inner.property.1
    case hb =>
      have := inner.property.2
      simp only [Vector.sum_mk, List.sum_toArray, this, ge_iff_le]
      omega

theorem e {well : Vector Nat n} {c d : Nat} (h : c ≤ d) {i : Nat} {h'} :
    (nextAction well c d h).val[i]'h' + ((nextAction well c d h).apply well)[i]'h' = well[i] := by
  have := (nextAction.go well.toList c).property.2.2
  simp only [nextAction, Vector.getElem_mk, List.getElem_toArray, WellAction.apply,
    Vector.getElem_map, Vector.getElem_zip]
  grind

theorem f {well : Vector Nat n} {c d : Nat} (h : c ≤ d) :
    (nextAction well c d h).val.sum + ((nextAction well c d h).apply well).sum = well.sum := by
  sorry

def optActions (well : Vector Nat n) (c : Nat) (d : Nat) (h : c ≤ d) : List (WellAction n d) :=
  let a := nextAction well c d h
  if a.val.sum > 0 then
    optActions (a.apply well) c d h
  else
    []
termination_by well.toList.sum
decreasing_by
  grind [f]

theorem c {well : Vector Nat n} {c : Nat} (hc : 0 < c) :
    IsWellEmpty ((optActions well c c (by grind)).foldr (init := well) WellAction.apply) := by
  sorry

theorem b {well : Vector Nat n} {r} (h : MinimalWellActions well c r) :
    r = (well.sum + c - 1) / c := by
  apply Nat.le_antisymm
  · apply h.2
    let as : List (WellAction n c) :=

theorem List.sum_length_filter {xs : List α} {f : α → Fin n} :
    (Vector.ofFn (fun i : Fin n => xs.filter (f · = i) |>.length)).sum = xs.length := by
  sorry

theorem Vector.map_ofFn {f : Fin n → α} {g : α → β} :
    (Vector.ofFn f).map g = Vector.ofFn (g ∘ f) := by
  sorry

theorem bla {grid : Vector (Vector Nat n) m} {as : List (Action m n)} {i : Fin m} :
    (as.foldr (init := grid) Action.apply)[i.val] = (as.filter (·.1 = i) |>.map (·.2) |>.foldr (init := grid[i.val]) WellAction.apply) := by
  simp only [List.foldr_map, List.foldr_filter]
  apply Eq.symm
  apply List.foldr_hom (f := fun g => g[i.val])
  simp [Action.apply, Vector.modify, Array.getElem_modify, Fin.val_inj]

theorem bla' {grid : Vector (Vector Nat n) m} {as : List (Action m n)} :
    (as.foldr (init := grid) Action.apply) = Vector.ofFn (fun i => (as.filter (·.1 = i) |>.map (·.2) |>.foldr (init := grid[i.val]) WellAction.apply)) := by
  grind [bla]

theorem a {grid : Vector (Vector Nat n) m} {r} :
    MinimalGridActions grid r ↔
      ∃ rs : Vector Nat m, r = rs.sum ∧ ∀ i : Fin m, MinimalWellActions grid[i] (rs[i]) := by
  simp only [MinimalGridActions, MinimalWellActions, bla', IsGridEmpty, Fin.getElem_fin]
  apply Iff.intro
  · intro h
    obtain ⟨as, has, rfl⟩ := h.1
    let partition := Vector.ofFn (fun i : Fin m => as.filter (·.1 = i))
    have hrs := List.sum_length_filter (xs := as) (f := (·.1))
    refine ⟨partition.map (·.length), by simpa [partition, Vector.map_ofFn] using hrs.symm, ?_⟩
    intro i
    apply And.intro
    · refine ⟨partition[i].map (·.2), ?_, ?_⟩
      · simp [partition]
        simp at has
        specialize has i.val i.isLt
        simpa using has
      · simp
    · rintro _ ⟨as', has', rfl⟩
      have := h.2 (as.length + as'.length - (Vector.map (fun x => x.length) partition)[↑i])
      simp at this

  apply Iff.intro
  · intro h
    obtain ⟨as, has, rfl⟩ := h.1
    let partition := Vector.ofFn (fun i : Fin m => as.filter (·.1 = i))
    have hrs := List.sum_length_filter (xs := as) (f := (·.1))
    refine ⟨partition.map (·.length), by simpa [partition, Vector.map_ofFn] using hrs.symm, ?_⟩
    intro i
    apply And.intro
    · refine ⟨partition[i].map (·.2), ?_⟩
      apply And.intro
      · simp only [Fin.getElem_fin, Vector.getElem_ofFn, partition]
        let g₂ (a : Action m n) (w : Vector Nat n) : Vector Nat n :=
          if a.fst = i then a.snd.apply w else w
        simp [IsGridEmpty] at has
        specialize has i.val i.isLt
        rw [← List.foldr_hom (f := fun gr => gr[i.val]) (g₂ := g₂)] at has; rotate_left
        · simp [Action.apply, Vector.modify, g₂, Array.getElem_modify, Fin.val_inj]
        simp only [g₂] at has
        simpa [List.foldr_map, List.foldr_filter]
      · simp
    · rintro k ⟨as', has'⟩
      sorry



/-!
## Prompt

```python3

def max_fill(grid, capacity):
    import math
    """
    You are given a rectangular grid of wells. Each row represents a single well,
    and each 1 in a row represents a single unit of water.
    Each well has a corresponding bucket that can be used to extract water from it,
    and all buckets have the same capacity.
    Your task is to use the buckets to empty the wells.
    Output the number of times you need to lower the buckets.

    Example 1:
        Input:
            grid : [[0,0,1,0], [0,1,0,0], [1,1,1,1]]
            bucket_capacity : 1
        Output: 6

    Example 2:
        Input:
            grid : [[0,0,1,1], [0,0,0,0], [1,1,1,1], [0,1,1,1]]
            bucket_capacity : 2
        Output: 5

    Example 3:
        Input:
            grid : [[0,0,0], [0,0,0]]
            bucket_capacity : 5
        Output: 0

    Constraints:
        * all wells have the same length
        * 1 <= grid.length <= 10^2
        * 1 <= grid[:,1].length <= 10^2
        * grid[i][j] -> 0 | 1
        * 1 <= capacity <= 10
    """
```

## Canonical solution

```python3
    return sum([math.ceil(sum(arr)/capacity) for arr in grid])
```

## Tests

```python3
def check(candidate):


    # Check some simple cases
    assert True, "This prints if this assert fails 1 (good for debugging!)"
    assert candidate([[0,0,1,0], [0,1,0,0], [1,1,1,1]], 1) == 6, "Error"
    assert candidate([[0,0,1,1], [0,0,0,0], [1,1,1,1], [0,1,1,1]], 2) == 5, "Error"
    assert candidate([[0,0,0], [0,0,0]], 5) == 0, "Error"

    # Check some edge cases that are easy to work out by hand.
    assert True, "This prints if this assert fails 2 (also good for debugging!)"
    assert candidate([[1,1,1,1], [1,1,1,1]], 2) == 4, "Error"
    assert candidate([[1,1,1,1], [1,1,1,1]], 9) == 2, "Error"

```
-/
