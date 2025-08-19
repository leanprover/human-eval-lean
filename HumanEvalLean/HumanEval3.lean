import Std.Tactic.Do

def belowZero (l : List Int) : Bool :=
  go 0 l
where
  go (cur : Int) (remaining : List Int) : Bool :=
    if cur < 0 then
      true
    else
      match remaining with
      | [] => false
      | l::rem => go (cur + l) rem

def doBelowZero (operations : List Int) : Bool := Id.run do
  let mut balance := 0
  for op in operations do
    balance := balance + op
    if balance < 0 then
      return true
  return false

namespace List

structure HasPrefix (P : List α → Prop) (l : List α) : Prop where
  exists_take : ∃ n, P (l.take n)

theorem hasPrefix_iff {P : List α → Prop} {l : List α} :
    l.HasPrefix P ↔ ∃ n, P (l.take n) := by
  grind [HasPrefix]

@[simp, grind]
theorem hasPrefix_nil {P : List α → Prop} : [].HasPrefix P ↔ P [] := by
  simp [hasPrefix_iff]

@[simp, grind]
theorem hasPrefix_of_nil {P : List α → Prop} {l : List α} (h : P []) : l.HasPrefix P :=
  ⟨⟨0, by simpa⟩⟩

@[simp, grind]
theorem hasPrefix_of_all {P : List α → Prop} {l : List α} (h : P l) : l.HasPrefix P :=
  ⟨⟨l.length, by simpa⟩⟩

@[grind]
theorem hasPrefix_cons {P : List α → Prop} {a : α} {l : List α} :
    (a :: l).HasPrefix P ↔ P [] ∨ l.HasPrefix (fun l' => P (a :: l')) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨n, hn⟩⟩
    refine (Nat.eq_zero_or_pos n).elim (by rintro rfl; simp_all) (fun hnp => Or.inr ⟨⟨n - 1, ?_⟩⟩)
    rwa [take_cons hnp] at hn
  · rintro (h|⟨⟨n, hn⟩⟩)
    · exact hasPrefix_of_nil h
    · exact ⟨n + 1, by simpa⟩

@[grind]
theorem hasPrefix_append {P : List α → Prop} {l l' : List α} :
    (l ++ l').HasPrefix P ↔ l.HasPrefix P ∨ l'.HasPrefix (fun l'' => P (l ++ l'')) := by
  induction l generalizing P with grind

@[grind]
theorem sum_append_singleton_int {l₁ : List Int} {x : Int} : (l₁ ++ [x]).sum = l₁.sum + x := by
  simp [List.sum, ← List.foldr_assoc]

end List

theorem belowZero_iff {l : List Int} : belowZero l ↔ ∃ n, (l.take n).sum < 0 := by
  suffices ∀ c, belowZero.go c l ↔ ∃ n, c + (l.take n).sum < 0 by simpa using this 0
  intro c
  rw [← List.hasPrefix_iff (P := fun l => c + l.sum < 0)]
  fun_induction belowZero.go with grind

open Std.Do
set_option mvcgen.warning false

theorem doBelowZero_iff {l : List Int} : doBelowZero l ↔ l.HasPrefix (fun l => l.sum < 0) := by
  generalize h : doBelowZero l = res
  apply Id.of_wp_run_eq h
  mvcgen
  case inv1 =>
    exact Invariant.withEarlyReturn
      (fun xs bal => ⌜bal = xs.prefix.sum ∧ ¬ xs.prefix.HasPrefix (fun l => l.sum < 0)⌝)
      (fun r bal => ⌜r = true ∧ l.HasPrefix (fun l => l.sum < 0)⌝)
  all_goals mleave; grind

/-!
## Prompt

```python3
from typing import List


def below_zero(operations: List[int]) -> bool:
    """ You're given a list of deposit and withdrawal operations on a bank account that starts with
    zero balance. Your task is to detect if at any point the balance of account fallls below zero, and
    at that point function should return True. Otherwise it should return False.
    >>> below_zero([1, 2, 3])
    False
    >>> below_zero([1, 2, -4, 5])
    True
    """
```

## Canonical solution

```python3
    balance = 0

    for op in operations:
        balance += op
        if balance < 0:
            return True

    return False
```

## Tests

```python3


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    assert candidate([]) == False
    assert candidate([1, 2, -3, 1, 2, -3]) == False
    assert candidate([1, 2, -4, 5, 6]) == True
    assert candidate([1, -1, 2, -2, 5, -5, 4, -4]) == False
    assert candidate([1, -1, 2, -2, 5, -5, 4, -5]) == True
    assert candidate([1, -2, 2, -2, 5, -5, 4, -4]) == True
```
-/
