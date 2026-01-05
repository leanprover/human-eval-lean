module

public import Std
open Std

/-!
## Implementation
-/

def maxFill (grid : Vector (Vector Nat n) m) (capacity : Nat) : Nat :=
  grid.toArray.iter
    |>.map (fun well => (well.sum + capacity - 1) / capacity)
    |>.fold (init := 0) (· + ·)

/-!
# Tests
-/

example : maxFill #v[#v[0,0,1,0], #v[0,1,0,0], #v[1,1,1,1]]              1 = 6 := by native_decide
example : maxFill #v[#v[0,0,1,1], #v[0,0,0,0], #v[1,1,1,1], #v[0,1,1,1]] 2 = 5 := by native_decide
example : maxFill #v[#v[0,0,0],   #v[0,0,0]]                             5 = 0 := by native_decide
example : maxFill #v[#v[1,1,1,1], #v[1,1,1,1]]                           2 = 4 := by native_decide
example : maxFill #v[#v[1,1,1,1], #v[1,1,1,1]]                           9 = 2 := by native_decide

/-!
## Verification

The objective of the verification is to prove that `maxFill` satisfies a very literal formalization
of the prompt: `maxFill` computes the total number of "actions" needed to clear all wells in the
grid. Here, "actions" on individual wells are represented by the `WellAction` structure, which
provides information about how much water is removed from which columns, while maintaining that
the total amount of removed water is bounded by the capacity.

The main work consists in reducing this model to a simpler, more abstract one, where each well
only contains information about the total amount of contained water, without the distribution
of it along the columns. Consequently, actions (`AbstractWellAction`) consist solely of the total
amount of water removed. In this model, it is much easier to verify the minimal number of
actions needed.
-/

/-!
### Potential library lemmas
-/

attribute [grind =] Vector.sum_mk List.zip_cons_cons List.zip_nil_right List.zip_nil_left

-- this is in Mathlib
theorem Nat.div_add_div_le_add_div (a b c : Nat) : a / c + b / c ≤ (a + b) / c := by
  by_cases h : 0 < c
  · rw [← (Nat.mul_le_mul_right_iff (show 0 < c by grind)), Nat.add_mul]
    simp only [Nat.div_mul_self_eq_mod_sub_self]
    have (a b c d : Nat) (h : b ≤ a) (h' : d ≤ c) : (a - b) + (c - d) = (a + c) - (b + d) := by grind
    rw [this, Nat.sub_le_sub_iff_left]
    · rw [Nat.add_mod]
      apply Nat.mod_le
    · apply Nat.mod_le
    · apply Nat.mod_le
    · apply Nat.mod_le
  · grind

theorem Nat.le_add_sub_one_div (a b : Nat) (hb : b > 0) :
    a ≤ (a + b - 1) / b * b := by
  have := Nat.div_add_mod' a b |>.symm
  rw [this, Nat.add_sub_assoc hb, Nat.add_assoc]
  refine Nat.le_trans (m := a / b * b / b * b + (a % b + (b - 1)) / b * b) ?_ ?_
  · rw [Nat.mul_div_cancel _ hb, Nat.add_le_add_iff_left]
    by_cases h : a % b = 0
    · grind
    · have : b ≤ a % b + (b - 1) := by grind
      have : b ≤ (a % b + (b - 1)) / b * b := by
        apply Nat.le_mul_of_pos_left
        exact Nat.div_pos this hb
      have : a % b < b := by exact Nat.mod_lt a hb
      grind
  · rw [← Nat.add_mul]
    apply Nat.mul_le_mul_right
    apply Nat.div_add_div_le_add_div

def Vector.modify (xs : Vector α n) (i : Nat) (f : α → α) : Vector α n :=
  ⟨xs.toArray.modify i f, by grind⟩

@[simp, grind =]
theorem Vector.sum_toList {xs : Vector Nat α} :
    xs.toList.sum = xs.sum := by
  rw [← Vector.mk_toArray (xs := xs), Vector.toList_mk, Vector.sum_mk, Array.sum_eq_sum_toList]

@[simp, grind =]
theorem Vector.sum_toArray {xs : Vector Nat α} :
    xs.toArray.sum = xs.sum := by
  rw [Vector.sum_mk]

@[simp, grind =]
theorem Vector.toList_zip {as : Vector α n} {bs : Vector β n} :
    (Vector.zip as bs).toList = List.zip as.toList bs.toList := by
  rcases as with ⟨as, rfl⟩
  rcases bs with ⟨bs, h⟩
  simp

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

theorem List.sum_eq_foldl {xs : List Nat} :
    xs.sum = xs.foldl (init := 0) (· + ·) := by
  rw [← List.reverse_reverse (as := xs)]
  generalize xs.reverse = xs
  induction xs <;> grind

theorem Array.sum_eq_foldl {xs : Array Nat} :
    xs.sum = xs.foldl (init := 0) (· + ·) := by
  rw [← Array.toArray_toList (xs := xs)]
  grind [List.sum_eq_foldl]

theorem Vector.ofFn_getElem {xs : Vector α n} :
    Vector.ofFn (fun i : Fin n => xs[i.val]) = xs := by
  grind

theorem Array.map_ofFn {f : Fin n → α} {g : α → β} :
    (Array.ofFn f).map g = Array.ofFn (g ∘ f) := by
  apply Array.ext_getElem?
  grind [Array.getElem?_ofFn]

/-!
### The concrete model

This model is as close to the prompt as possible.
-/

def WellAction (n c : Nat) := { mask : Vector Nat n // mask.sum ≤ c }
def WellAction.apply (a : WellAction n c) (well : Vector Nat n) : Vector Nat n :=
  (well.zip a.val).map (fun (given, lower) => given - lower)

def IsWellEmpty (well : Vector Nat n) : Bool := well.all (· = 0)

def IsMin (P : Nat → Prop) (n : Nat) : Prop := P n ∧ ∀ m, P m → n ≤ m

def MinimalWellActions (well : Vector Nat n) (c : Nat) (result : Nat) : Prop :=
  IsMin
    (fun r => ∃ as : List (WellAction n c),
        IsWellEmpty (as.foldr (init := well) WellAction.apply) ∧ r = as.length)
    result

/-!
### The abstract model

This model is simpler and easier to handle. It is equivalent in relevant ways to the concrete model,
as will be shown.
-/

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

/-!
### Conversions between the concrete and abstract model
-/

def abstract (well : Vector Nat n) : AbstractWell :=
  AbstractWell.mk well.sum

/--
A helper for defining `liftAction` that is defined recursively on the list representation
of the well.
-/
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

def liftAction (well : Vector Nat n) (a : AbstractWellAction c) : WellAction n c :=
  ⟨⟨(liftAction.go well.toList a.val).toArray,
      by grind [liftAction.length_go]⟩, by grind [liftAction.sum_go]⟩

@[grind =]
theorem abstract_apply_liftAction {well : Vector Nat n} {a : AbstractWellAction c} :
    abstract ((liftAction well a).apply well) = a.apply (abstract well) := by
  ext
  simp only [abstract, WellAction.apply, AbstractWellAction.apply]
  simp only [← Vector.sum_toList, Vector.toList_map, Vector.toList_zip, liftAction,
    Vector.toList_mk]
  induction well.toList generalizing a
  · grind [liftAction.go]
  · rename_i w ws ih
    specialize ih (a := ⟨a.val - min w a.val, by grind⟩)
    grind [liftAction.go]

def liftActions (well : Vector Nat n) (as : List (AbstractWellAction c)) :
    List (WellAction n c) :=
  match as with
  | [] => []
  | a :: as =>
    liftAction ((liftActions well as).foldr (init := well) WellAction.apply) a :: liftActions well as

@[grind =]
theorem length_liftActions {well : Vector Nat n} {as : List (AbstractWellAction c)} :
    (liftActions well as).length = as.length := by
  induction as <;> grind [liftActions]

@[grind =]
theorem abstract_apply_liftActions {well : Vector Nat n} {as : List (AbstractWellAction c)} :
    abstract (((liftActions well as).foldr (init := well) WellAction.apply)) = as.foldr (init := abstract well) AbstractWellAction.apply := by
  induction as <;> grind [liftActions]

theorem WellAction.sum_sub_sum_apply_lt {well : Vector Nat n} {a : WellAction n c} :
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
      specialize ih (n := n - 1) (c := c - a) (a := ⟨⟨⟨as⟩, by grind⟩, by grind⟩)
      grind

def abstractAction (well : Vector Nat n) (a : WellAction n c) : AbstractWellAction c :=
  ⟨well.sum - (a.apply well).sum, by apply WellAction.sum_sub_sum_apply_lt⟩

@[grind =]
theorem apply_abstractAction_abstract {well : Vector Nat n} {a : WellAction n c} :
    (abstractAction well a).apply (abstract well) = abstract (a.apply well) := by
  ext
  simp only [abstract, WellAction.apply, AbstractWellAction.apply, abstractAction]
  simp only [← Vector.sum_toList, Vector.toList_map, Vector.toList_zip]
  have : well.toList.length = n := by grind
  generalize well.toList = ws at *
  clear well
  induction ws generalizing n a c
  · grind
  · rename_i w ws ih
    match a with
    | ⟨⟨⟨[]⟩, _⟩, _⟩ => grind
    | ⟨⟨⟨a :: as⟩, _⟩, _⟩ =>
      specialize ih (n := n - 1) (c := c - a) (a := ⟨⟨⟨as⟩, by grind⟩, by grind⟩)
      grind

def abstractActions (well : Vector Nat n) (as : List (WellAction n c)) :
    List (AbstractWellAction c) :=
  match as with
  | [] => []
  | a :: as => abstractAction (as.foldr (init := well) WellAction.apply) a :: abstractActions well as

@[grind =]
theorem length_abstractActions {well : Vector Nat n} {as : List (WellAction n c)} :
    (abstractActions well as).length = as.length := by
  induction as <;> grind [abstractActions]

@[grind =]
theorem apply_abstractActions_abstract {well : Vector Nat n} {as : List (WellAction n c)} :
    (abstractActions well as).foldr (init := abstract well) AbstractWellAction.apply = abstract (as.foldr (init := well) WellAction.apply) := by
  induction as <;> grind [abstractActions]

theorem AbstractWellAction.apply_list {well : AbstractWell} {as : List (AbstractWellAction c)} :
    as.foldr (init := well) AbstractWellAction.apply = AbstractWell.mk (well.val - (as.map (·.val)).sum) := by
  induction as generalizing well
  · simp
  · grind [AbstractWellAction.apply]

@[grind =]
theorem isWellEmpty_iff_isEmpty_abstract {well : Vector Nat n} :
    IsWellEmpty well ↔ (abstract well).IsEmpty := by
  grind [abstract, IsWellEmpty, Vector.sum_eq_zero]

theorem minimalAbstractWellActions_abstract_iff {well : Vector Nat n} {c : Nat} {r : Nat} :
    MinimalAbstractWellActions (abstract well) c r ↔ MinimalWellActions well c r := by
  simp only [MinimalAbstractWellActions, MinimalWellActions, iff_iff_eq]
  congr; ext
  apply Iff.intro
  · rintro ⟨as, has, rfl⟩
    refine ⟨liftActions well as, ?_, ?_⟩ <;> grind
  · rintro ⟨as, has, rfl⟩
    refine ⟨abstractActions well as, ?_, ?_⟩ <;> grind

theorem val_le_of_isEmpty_apply_list {well : AbstractWell} {c : Nat} {as : List (AbstractWellAction c)}
    (h : (as.foldr (init := well) AbstractWellAction.apply).IsEmpty) :
    well.val ≤ (as.map (·.val)).sum := by
  grind [AbstractWellAction.apply_list]

theorem le_length_of_isEmpty_apply_list {well : AbstractWell} {c : Nat} {as : List (AbstractWellAction c)}
    (h : (as.foldr (init := well) AbstractWellAction.apply).IsEmpty) (hc : c > 0) :
    (well.val + c - 1) / c ≤ as.length := by
  have : (as.map (·.val)).sum ≤ as.length * c := by
    clear h
    induction as
    · grind
    · simp only [List.length_cons]
      grind
  have := val_le_of_isEmpty_apply_list h
  have : (well.val + c - 1) / c ≤ (as.length * c + c - 1) / c := Nat.div_le_div_right (by grind)
  have : (as.length * c + c - 1) / c ≤ as.length := (Nat.div_le_iff_le_mul hc).mpr (le_refl _)
  grind

/-!
### Determining the minimal number of actions
-/

def optimalAbstractActions (well : AbstractWell) (c : Nat) : List (AbstractWellAction c) :=
  List.replicate ((well.val + c - 1) / c) ⟨c, by grind⟩

theorem length_optimalAbstractActions {well : AbstractWell} {c : Nat} :
    (optimalAbstractActions well c).length = (well.val + c - 1) / c := by
  grind [optimalAbstractActions]

theorem isEmpty_apply_optimalAbstractActions {well : AbstractWell} {c : Nat} (hc : c > 0) :
    ((optimalAbstractActions well c).foldr (init := well) AbstractWellAction.apply).IsEmpty := by
  rw [AbstractWellAction.apply_list]
  simp [AbstractWell.IsEmpty, optimalAbstractActions, Nat.sub_eq_zero_iff_le]
  apply Nat.le_add_sub_one_div
  exact hc

theorem minimalAbstractWellActions {well : AbstractWell} {c : Nat} (hc : 0 < c) :
    MinimalAbstractWellActions well c ((well.val + c - 1) / c) := by
  apply And.intro
  · exact ⟨optimalAbstractActions well c,
      isEmpty_apply_optimalAbstractActions hc, length_optimalAbstractActions.symm⟩
  · rintro _ ⟨as', has', rfl⟩
    exact le_length_of_isEmpty_apply_list has' hc

theorem minimalWellActions {well : Vector Nat n} {c : Nat} (hc : 0 < c) :
    MinimalWellActions well c ((well.sum + c - 1) / c) := by
  have := minimalAbstractWellActions (well := abstract well) hc
  grind [abstract, minimalAbstractWellActions_abstract_iff]

/-!
### The correctness theorem
-/

/--
The function `maxFill` computes the minimal numer of well actions needed to empty all wells.
-/
theorem maxFill_eq_sum_minimalWellActions {grid : (Vector (Vector Nat n) m)} {c : Nat}
    {hc : c > 0} :
    ∃ rs : Vector Nat m, (∀ (i : Nat) (_ : i < m), MinimalWellActions grid[i] c rs[i]) ∧
        maxFill grid c = rs.sum := by
  refine ⟨.ofFn fun i => (grid[i.val].sum + c - 1) / c, ?_, ?_⟩
  · grind [minimalWellActions]
  · simp only [maxFill]
    -- Should rename `Array.toArray_toIter` to `Array.toArray_iter`
    rw [← Iter.foldl_toArray, Iter.toArray_map, Array.toArray_toIter, ← Array.sum_eq_foldl]
    conv => lhs; rw [← Vector.ofFn_getElem (xs := grid), Vector.toArray_ofFn, Array.map_ofFn]
    rw [← Vector.sum_toArray, Vector.toArray_ofFn, Function.comp_def]

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
