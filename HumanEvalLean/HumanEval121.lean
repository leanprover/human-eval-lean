-- This can't be a module right now because `Rxi.Iterator.Monadic.Step` is not exposed
import Std

open Std Std.PRange Std.Do

set_option mvcgen.warning false

/-!
## Implementation 1
-/

def solution'' (xs : List Int) : Int :=
  go xs 0
where go (xs : List Int) (acc : Int) :=
  match xs with
  | [] => acc
  | [x] => if x % 2 = 1 then acc + x else acc
  | x :: _ :: ys =>
    if x % 2 = 1 then go ys (acc + x) else go ys acc

/-!
## Tests 1
-/

example : solution'' [5, 8, 7, 1] = 12 := by decide
example : solution'' [3, 3, 3, 3, 3] = 9 := by decide
example : solution'' [30, 13, 24, 321] = 0 := by decide
example : solution'' [5, 9] = 5 := by decide
example : solution'' [2, 4, 8] = 0 := by decide
example : solution'' [30, 13, 23, 32] = 23 := by decide
example : solution'' [3, 13, 2, 9] = 3 := by decide

/-!
## Verification 1
-/

theorem solution''_aux {xs : List Int} {acc : Int} :
    solution''.go xs acc = acc + (xs.mapIdx (fun i x => if i % 2 = 0 ∧ x % 2 = 1 then x else 0)).sum := by
  fun_induction solution''.go xs acc <;> grind

theorem solution''_spec {xs : List Int} :
    solution'' xs = (xs.mapIdx (fun i x => if i % 2 = 0 ∧ x % 2 = 1 then x else 0)).sum := by
  simp [solution'', solution''_aux]

/-!
## Implementation 2
-/

def solution' (xs : List Int) : Int := Id.run do
  let mut even := true
  let mut sum := 0
  for x in xs do
    if even ∧ x % 2 = 1 then
      sum := sum + x
    even := ! even
  return sum

/-!
## Tests 2
-/

example : solution' [5, 8, 7, 1] = 12 := by decide
example : solution' [3, 3, 3, 3, 3] = 9 := by decide
example : solution' [30, 13, 24, 321] = 0 := by decide
example : solution' [5, 9] = 5 := by decide
example : solution' [2, 4, 8] = 0 := by decide
example : solution' [30, 13, 23, 32] = 23 := by decide
example : solution' [3, 13, 2, 9] = 3 := by decide

/-!
## Verification 2
-/

theorem List.sum_append_int {l₁ l₂ : List Int} : (l₁ ++ l₂).sum = l₁.sum + l₂.sum := by
  induction l₁ generalizing l₂ <;> simp_all [Int.add_assoc]

theorem solution'_spec {xs : List Int} :
    solution' xs = (xs.mapIdx (fun i x => if i % 2 = 0 ∧ x % 2 = 1 then x else 0)).sum := by
  generalize h : solution' xs = r
  apply Id.of_wp_run_eq h
  mvcgen
  · exact ⇓⟨cur, even, sum⟩ => ⌜even = (cur.prefix.length % 2 = 0) ∧ sum = (cur.prefix.mapIdx (fun i x => if i % 2 = 0 ∧ x % 2 = 1 then x else 0)).sum⌝
  · mleave
    simp [List.sum_append_int]
    grind
  · simp [List.sum_append_int]
    grind
  · grind
  · grind

/-!
## Implementation 3
-/

def solution (xs : List Int) : Int :=
  ((0 : Nat)...*).iter.zip xs.iter
    |>.filter (fun (i, x) => i % 2 = 0 ∧ x % 2 = 1)
    |>.fold (init := 0) (fun sum (_, x) => sum + x)

/-!
## Tests 3
-/

example : solution [5, 8, 7, 1] = 12 := by native_decide
example : solution [3, 3, 3, 3, 3] = 9 := by native_decide
example : solution [30, 13, 24, 321] = 0 := by native_decide
example : solution [5, 9] = 5 := by native_decide
example : solution [2, 4, 8] = 0 := by native_decide
example : solution [30, 13, 23, 32] = 23 := by native_decide
example : solution [3, 13, 2, 9] = 3 := by native_decide

/-!
## Verification 3
-/

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

attribute [grind =] List.zip_nil_right List.toList_iter Iter.toList_filter List.sum_append_int
  List.zip_cons_cons

theorem solution_nil :
    solution [] = 0 := by
  -- fails:
  -- grind [solution, =_ Iter.foldl_toList, ! . Iter.toList_zip_of_finite_right]

  -- succeeds:
  -- grind =>
  --   instantiate only [solution]
  --   finish [=_ Iter.foldl_toList, ! . Iter.toList_zip_of_finite_right]

  simp [solution, ← Iter.foldl_toList, Iter.toList_zip_of_finite_right]

theorem solution_append_singleton {xs : List Int} {x : Int} :
    solution (xs ++ [x]) =
      if xs.length % 2 = 0 ∧ x % 2 = 1 then solution xs + x else solution xs := by
  simp only [solution, Bool.decide_and, ← Iter.foldl_toList,
    Iter.toList_filter, Iter.toList_zip_of_finite_right, List.toList_iter, List.length_append,
    List.length_cons, List.length_nil, Nat.zero_add, Nat.toList_take_iter_rci]
  rw [Nat.toList_rco_succ_right_eq_append (by simp), List.zip_append (by simp)]
  grind

theorem solution_spec {xs : List Int} :
    solution xs = (xs.mapIdx (fun i x => if i % 2 = 0 ∧ x % 2 = 1 then x else 0)).sum := by
  rw [← List.reverse_reverse (as := xs)]
  induction xs.reverse
  · simp [solution_nil]
  · simp only [List.reverse_cons]
    grind [solution_append_singleton]

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
