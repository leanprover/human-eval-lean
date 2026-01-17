-- This can't be a module right now because `Rxi.Iterator.Monadic.Step` is not exposed
import Std

open Std Std.PRange

def solution (xs : List Int) : Int :=
  ((0 : Nat)...*).iter.zip xs.iter
    |>.filter (fun (i, _) => i % 2 = 0)
    |>.fold (init := 0) (fun sum (_, x) => sum + x)

attribute [grind =] Iter.toList_take_zero Nat.succ?_eq

public theorem Rxi.Iterator.toList_take_eq_match
    [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    {it : Iter (α := Rxi.Iterator α) α} :
    (it.take n).toList =  match n, it.internalState.next with
      | 0, _ | _, none => []
      | n + 1, some a =>
          a :: ((⟨⟨UpwardEnumerable.succ? a⟩⟩ : Iter (α := Rxi.Iterator α) α).take n).toList := by
  apply Eq.symm
  simp only [Iter.toList_eq_match_step (it := it.take n), Iter.step_take]
  cases n
  · grind
  · simp only
    cases it.step using PlausibleIterStep.casesOn <;> rename_i heq
    · rename_i it' _
      rcases it with ⟨⟨next⟩⟩ | _
      · simp [Iter.IsPlausibleStep, IterM.IsPlausibleStep, Iterator.IsPlausibleStep] at heq
        simp [Rxi.Iterator.Monadic.step, Iter.toIterM] at heq -- ugly
      · simp [Iter.IsPlausibleStep, IterM.IsPlausibleStep, Iterator.IsPlausibleStep] at heq
        simp [Rxi.Iterator.Monadic.step, Iter.toIterM] at heq -- ugly
        cases heq.2
        cases it'
        simp at heq
        simp [heq]
    · simp [Iter.IsPlausibleStep, IterM.IsPlausibleStep, Iterator.IsPlausibleStep] at heq
      simp [Rxi.Iterator.Monadic.step, Iter.toIterM] at heq -- ugly
      split at heq <;> contradiction
    · simp [Iter.IsPlausibleStep, IterM.IsPlausibleStep, Iterator.IsPlausibleStep] at heq
      simp [Rxi.Iterator.Monadic.step, Iter.toIterM] at heq -- ugly
      split at heq
      · simp [*]
      · contradiction

theorem Nat.toList_take_iter_rci_eq_match {m n : Nat} :
    ((m...*).iter.take n).toList =
      match n with
      | 0 => []
      | n + 1 => m :: (((m + 1)...*).iter.take n).toList := by
  rw [Rxi.Iterator.toList_take_eq_match]
  cases n <;> grind [Rci.iter]

@[grind =]
theorem Nat.toList_take_zero_iter_rci {m : Nat} :
    ((m...*).iter.take 0).toList = [] := by
  rw [Nat.toList_take_iter_rci_eq_match]

@[grind =]
theorem Nat.toList_take_add_one_iter_rci {m n : Nat} :
    ((m...*).iter.take (n + 1)).toList = m :: (((m + 1)...*).iter.take n).toList := by
  rw [Nat.toList_take_iter_rci_eq_match]

@[grind =]
theorem Nat.toList_rco_self {m : Nat} :
    (m...m).toList = [] := by
  simp [toList_rco_eq_nil]

@[grind =]
theorem Nat.toList_take_iter_rci {m n : Nat} :
    (((m : Nat)...*).iter.take n).toList = ((m : Nat)...(m + n : Nat)).toList := by
  induction n generalizing m <;> grind [Nat.toList_rco_eq_cons, Nat.toList_take_add_one_iter_rci]

@[grind =]
theorem List.map_swap_zip {xs : List α} {ys : List β} :
    (ys.zip xs).map Prod.swap = xs.zip ys := by
  induction xs generalizing ys
  · grind [zip_nil_right, zip_nil_left]
  · cases ys
    · grind [zip_nil_left, zip_nil_right]
    · grind [zip_cons_cons, Prod.swap_prod_mk]

theorem solution_spec {xs : List Int} :
    solution xs = (xs.mapIdx (fun i x => if i % 2 = 0 then x else 0)).sum :=
  match xs with
  | [] => by
    simp [solution, ← Iter.foldl_toList]
    rw [Iter.toList_zip_of_finite_right]
    grind [List.toList_iter, List.length_nil, List.zip_nil_right]
  | [x] => by
    simp [solution, ← Iter.foldl_toList]
    rw [Iter.toList_zip_of_finite_right]
    simp [Nat.toList_take_iter_rci]
  | x :: y :: xs => by
    have := solution_spec (xs := xs)
    simp [solution, ← Iter.foldl_toList] at this ⊢
    rw [Iter.toList_zip_of_finite_right]
    simp [Nat.toList_take_iter_rci, Nat.toList_rco_eq_cons]
    -- ugh, foldr would have been nicer


theorem solution_spec {xs : List Int} :
    solution xs = (xs.mapIdx (fun i x => if i % 2 = 0 then x else 0)).sum := by
  simp [solution, ← Iter.foldl_toList]
  rw [Iter.toList_zip_of_finite_right]
  simp [Nat.toList_take_iter_rci]
  rw [List.mapIdx_eq_zipIdx_map, List.zipIdx_eq_zip_range', List.range'_eq_toList_rco]
  simp
  rw [← List.map_swap_zip]
  induction xs
  · simp
  · simp [Nat.toList_rco_eq_cons]


/-!
## Prompt

```python3

def solution(lst):
    """Given a non-empty list of integers, return the sum of all of the odd elements that are in even positions.


    Examples
    solution([5, 8, 7, 1]) ==> 12
    solution([3, 3, 3, 3, 3]) ==> 9
    solution([30, 13, 24, 321]) ==>0
    """
```

## Canonical solution

```python3
    return sum([x for idx, x in enumerate(lst) if idx%2==0 and x%2==1])
```

## Tests

```python3
def check(candidate):

    # Check some simple cases
    assert candidate([5, 8, 7, 1])    == 12
    assert candidate([3, 3, 3, 3, 3]) == 9
    assert candidate([30, 13, 24, 321]) == 0
    assert candidate([5, 9]) == 5
    assert candidate([2, 4, 8]) == 0
    assert candidate([30, 13, 23, 32]) == 23
    assert candidate([3, 13, 2, 9]) == 3

    # Check some edge cases that are easy to work out by hand.

```
-/
