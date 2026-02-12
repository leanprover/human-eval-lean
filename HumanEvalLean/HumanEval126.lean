module

import Std
open Std Std.Do

set_option mvcgen.warning false

/-!
## Implementation
-/

def isSorted (xs : Array Nat) : Bool := Id.run do
  if h : xs.size > 0 then
    let mut last := xs[0]
    let mut repeated := false
    for x in xs[1...*] do
      match compare last x with
      | .lt =>
        last := x
        repeated := false
      | .eq =>
        if repeated then
          return false
        else
          repeated := true
      | .gt =>
        return false
  return true

/-!
## Tests
-/

example : isSorted #[5] = true := by native_decide
example : isSorted #[1, 2, 3, 4, 5] = true := by native_decide
example : isSorted #[1, 3, 2, 4, 5] = false := by native_decide
example : isSorted #[1, 2, 3, 4, 5, 6] = true := by native_decide
example : isSorted #[1, 2, 3, 4, 5, 6, 7] = true := by native_decide
example : isSorted #[1, 3, 2, 4, 5, 6, 7] = false := by native_decide
example : isSorted #[] = true := by native_decide
example : isSorted #[1] = true := by native_decide
example : isSorted #[3, 2, 1] = false := by native_decide
example : isSorted #[1, 2, 2, 2, 3, 4] = false := by native_decide
example : isSorted #[1, 2, 3, 3, 3, 4] = false := by native_decide
example : isSorted #[1, 2, 2, 3, 3, 4] = true := by native_decide
example : isSorted #[1, 2, 3, 4] = true := by native_decide

/-!
## Missing API
-/

instance : LawfulOrderOrd Nat where
  isLE_compare := by grind [Nat.isLE_compare]
  isGE_compare := by grind [Nat.isGE_compare]

attribute [grind .] List.Pairwise.nil

grind_pattern compare_eq_lt => compare a b, Ordering.lt where
  guard compare a b = .lt

grind_pattern compare_eq_eq => compare a b, Ordering.eq where
  guard compare a b = .eq

grind_pattern compare_eq_gt => compare a b, Ordering.gt where
  guard compare a b = .gt

/-!
## Verification
-/

theorem pairwise_append_of_trans {xs ys : List α} {R : α → α → Prop} [Trans R R R] :
    (xs ++ ys).Pairwise R ↔ xs.Pairwise R ∧ ys.Pairwise R ∧ (∀ (hxs : xs ≠ []) (hys : ys ≠ []), R (xs.getLast hxs) (ys.head hys)) := by
  rw [List.pairwise_append]
  apply Iff.intro
  · grind
  · rintro ⟨hpxs, hpys, h⟩
    refine ⟨hpxs, hpys, fun x hx y hy => ?_⟩
    rw [List.pairwise_iff_getElem] at hpxs hpys
    specialize h (by grind) (by grind)
    simp only [List.getLast_eq_getElem, List.head_eq_getElem] at h
    rw [List.mem_iff_getElem] at hx hy
    obtain ⟨i, hi, rfl⟩ := hx
    obtain ⟨j, hj, rfl⟩ := hy
    have h₁ : i < xs.length - 1 → R xs[i] xs[xs.length - 1] := by grind
    have h₂ : 0 < j → R ys[0] ys[j] := by grind
    by_cases hi' : i = xs.length - 1 <;> by_cases hj' : j = 0
    · grind
    · exact Trans.trans (r := R) (by grind) (h₂ (by grind))
    · exact Trans.trans (s := R) (h₁ (by grind)) (by grind)
    · exact Trans.trans (h₁ (by grind)) (Trans.trans h (h₂ (by grind)))

theorem pairwise_cons_of_trans {x : α} {xs : List α} {R : α → α → Prop} [Trans R R R] :
    (x :: xs).Pairwise R ↔ (∀ (hxs : xs ≠ []), R x (xs.head hxs)) ∧ xs.Pairwise R := by
  have := pairwise_append_of_trans (R := R) (xs := [x]) (ys := xs)
  grind

theorem sorted_of_isSorted {xs : Array Nat} (h : isSorted xs) : xs.toList.Pairwise (· ≤ ·) := by
  revert h -- Without reverting, we will not be able to use that the return value is `true` to show
           --that early returns cannot happen.
  generalize hwp : isSorted xs = wp
  rw [← Array.toArray_toList (xs := xs)] at *
  generalize xs.toList = xs at *
  apply Id.of_wp_run_eq hwp
  mvcgen
  invariants
  | inv1 => .withEarlyReturn
      (fun cur ⟨last, _⟩ =>
        ⌜(xs[0] :: cur.prefix).getLast? = some last ∧ (xs[0] :: cur.prefix).Pairwise (· ≤ ·)⌝)
      (fun ret _ => ⌜ret = false⌝)
  case vc1 =>
    simp only [pairwise_cons_of_trans, pairwise_append_of_trans] at *
    grind
  case vc3 =>
    simp only [pairwise_cons_of_trans, pairwise_append_of_trans] at *
    grind
  all_goals grind [List.getElem_zero, List.drop_one]

theorem count_le_two_of_isSorted {xs : Array Nat} {x : Nat} (h : isSorted xs) : xs.count x ≤ 2 := by
  have hp : xs.toList.Pairwise (· ≤ ·) := sorted_of_isSorted h
  rw [List.pairwise_iff_getElem] at hp
  revert h
  generalize hwp : isSorted xs = wp
  rw [← Array.toArray_toList (xs := xs)] at *
  generalize xs.toList = xs at *
  apply Id.of_wp_run_eq hwp
  mvcgen
  invariants
  | inv1 => .withEarlyReturn
    (fun cur ⟨last, repeated⟩ => ⌜(xs[0] :: cur.prefix).getLast? = some last ∧ (xs[0] :: cur.prefix).count x ≤ (if (last = x ∧ repeated) ∨ x < last then 2 else 1)⌝)
    (fun ret _ => ⌜ret = false⌝)
  case vc1 pref cur suff _ _ _ _ _ _ _ =>
    simp only [← List.cons_append]
    -- We generalize to simplify the problem.
    generalize hpref' : xs[0] :: pref = pref' at *
    have : xs = pref' ++ cur :: suff := by grind [List.getElem_zero, List.drop_one]
    clear hpref'
    simp only [List.count_append, List.count_singleton]
    have : ¬ cur ∈ pref' := by grind [List.mem_iff_getElem]
    split <;> grind [List.count_eq_zero]
  case vc6 a b c d e f =>
    grind [List.getElem_zero, List.drop_one]
  all_goals (clear hp; grind)

theorem not_pairwise_or_exists_count_of_isSorted_eq_false {xs : Array Nat} (h : isSorted xs = false) :
    ¬ xs.toList.Pairwise (· ≤ ·) ∨ (∃ x, xs.count x ≥ 3) := by
  revert h
  generalize hwf : isSorted xs = wf
  rw [← Array.toArray_toList (xs := xs)] at *
  generalize xs.toList = xs at *
  apply Id.of_wp_run_eq hwf
  mvcgen
  invariants
  | inv1 => .withEarlyReturn
      (fun cur ⟨last, repeated⟩ => ⌜(xs[0] :: cur.prefix).getLast? = some last ∧ (repeated → (xs[0] :: cur.prefix).count last ≥ 2)⌝)
      (fun ret ⟨last, repeated⟩ => ⌜¬ xs.Pairwise (· ≤ ·) ∨ xs.count last ≥ 3⌝)
  case vc2 pref cur suff _ _ _ _ _ _ _ _ =>
    have : xs = xs[0] :: pref ++ cur :: suff := by grind [List.getElem_zero, List.drop_one]
    grind
  case vc4 pref cur suff _ _ _ last _ _ _ =>
    have : xs = xs[0] :: pref ++ cur :: suff := by grind [List.getElem_zero, List.drop_one]
    have : ∃ (i j : Nat), i < j ∧ ∃ hi, ∃ hj, (xs[j]'hj) < (xs[i]'hi) := ⟨pref.length, pref.length + 1, by grind⟩
    simp [List.pairwise_iff_getElem, this]
  case vc7 =>
    -- Because the `xs.toArray.count` call is under an `∃` binder in the goal, `grind`'s
    -- congruence closure is not able to use `List.count_toArray`.
    simp only [List.count_toArray] at *
    grind

  all_goals grind

theorem isSorted_iff {xs : Array Nat} :
    isSorted xs ↔ xs.toList.Pairwise (· ≤ ·) ∧ ∀ x, xs.count x ≤ 2 := by
  grind [sorted_of_isSorted, count_le_two_of_isSorted,
    not_pairwise_or_exists_count_of_isSorted_eq_false]

/-!
## Prompt

```python3

def is_sorted(lst):
    '''
    Given a list of numbers, return whether or not they are sorted
    in ascending order. If list has more than 1 duplicate of the same
    number, return False. Assume no negative numbers and only integers.

    Examples
    is_sorted([5]) ➞ True
    is_sorted([1, 2, 3, 4, 5]) ➞ True
    is_sorted([1, 3, 2, 4, 5]) ➞ False
    is_sorted([1, 2, 3, 4, 5, 6]) ➞ True
    is_sorted([1, 2, 3, 4, 5, 6, 7]) ➞ True
    is_sorted([1, 3, 2, 4, 5, 6, 7]) ➞ False
    is_sorted([1, 2, 2, 3, 3, 4]) ➞ True
    is_sorted([1, 2, 2, 2, 3, 4]) ➞ False
    '''
```

## Canonical solution

```python3
    count_digit = dict([(i, 0) for i in lst])
    for i in lst:
        count_digit[i]+=1
    if any(count_digit[i] > 2 for i in lst):
        return False
    if all(lst[i-1] <= lst[i] for i in range(1, len(lst))):
        return True
    else:
        return False


```

## Tests

```python3
def check(candidate):

    # Check some simple cases
    assert candidate([5]) == True
    assert candidate([1, 2, 3, 4, 5]) == True
    assert candidate([1, 3, 2, 4, 5]) == False
    assert candidate([1, 2, 3, 4, 5, 6]) == True
    assert candidate([1, 2, 3, 4, 5, 6, 7]) == True
    assert candidate([1, 3, 2, 4, 5, 6, 7]) == False, "This prints if this assert fails 1 (good for debugging!)"
    assert candidate([]) == True, "This prints if this assert fails 2 (good for debugging!)"
    assert candidate([1]) == True, "This prints if this assert fails 3 (good for debugging!)"
    assert candidate([3, 2, 1]) == False, "This prints if this assert fails 4 (good for debugging!)"

    # Check some edge cases that are easy to work out by hand.
    assert candidate([1, 2, 2, 2, 3, 4]) == False, "This prints if this assert fails 5 (good for debugging!)"
    assert candidate([1, 2, 3, 3, 3, 4]) == False, "This prints if this assert fails 6 (good for debugging!)"
    assert candidate([1, 2, 2, 3, 3, 4]) == True, "This prints if this assert fails 7 (good for debugging!)"
    assert candidate([1, 2, 3, 4]) == True, "This prints if this assert fails 8 (good for debugging!)"

```
-/
