import Std.Data.Iterators
import Init.Notation
import Std.Tactic.Do

open Std.Iterators

/-!
## Implementation
-/

def isPrime (n : Nat) : Bool :=
    let divisors := (1...<n).iter.filter (· ∣ n)
    divisors.fold (init := 0) (fun count _ => count + 1) = 1

def x_or_y (n : Int) (x y : α) : α := Id.run do
  let some n := n.toNat? | return y
  if isPrime n then
    return x
  else
    return y

/-- info: [2, 3, 5, 7, 11, 13, 17, 19] -/
#guard_msgs in
#eval (1...20).iter.filter isPrime |>.toList

/-!
## Tests
-/

example : x_or_y 15 8 5 = 5 := by native_decide
example : x_or_y 3 33 5212 = 33 := by native_decide
example : x_or_y 1259 3 52 = 3 := by native_decide
example : x_or_y 7919 (-1) 12 = -1 := by native_decide
example : x_or_y 3609 1245 583 = 583 := by native_decide
example : x_or_y 91 56 129 = 129 := by native_decide
example : x_or_y 6 34 1234 = 1234 := by native_decide
example : x_or_y 1 2 0 = 0 := by native_decide
example : x_or_y 2 2 0 = 2 := by native_decide

/-!
## Verification
-/

def IsPrime (n : Nat) : Prop :=
  1 < n ∧ ∀ d : Nat, d ∣ n → d = 1 ∨ d = n

theorem pos_of_divides_of_pos {k n : Nat} (h : k ∣ n) (h' : n > 0) : k > 0 := by
  grind [Nat.dvd_iff_div_mul_eq]

theorem le_of_divides_of_pos {k n : Nat} (h : k ∣ n) (h' : n > 0) : k ≤ n := by
  false_or_by_contra
  have : n / k = 0 := by grind [Nat.div_eq_zero_iff]
  grind [Nat.dvd_iff_div_mul_eq]

theorem isPrime_eq_true_iff {n : Nat} :
    isPrime n = true ↔ (List.filter (fun x => decide (x ∣ n)) (1...n).toList).length = 1 := by
  simp [isPrime, ← Iter.foldl_toList]

theorem ClosedOpen.toList_eq_nil_of_le {m n : Nat} (h : n ≤ m) :
    (m...n).toList = [] := by
  simp [Std.PRange.toList_eq_nil_iff, Std.PRange.BoundedUpwardEnumerable.init?,
    Std.PRange.SupportsUpperBound.IsSatisfied, show n ≤ m by grind]

theorem ClosedOpen.toList_self_eq_nil {n : Nat} :
    (n...n).toList = [] := by
  simp [toList_eq_nil_of_le]

theorem ClosedOpen.toList_succ_eq_append {m n : Nat} (h : m ≤ n) :
    (m...(n + 1)).toList = (m...n).toList ++ [n] := by
  rw [show n = m + (n - m) by grind] at ⊢
  rw [show n = m + (n - m) by grind] at h
  generalize n - m = n at ⊢ h
  induction n generalizing m with
  | zero =>
    simp only [Nat.add_zero]
    simp [Std.PRange.toList_eq_match (r := m...(m + 1)),
      Std.PRange.toList_eq_match (r := m<...(m + 1)),
      Std.PRange.SupportsUpperBound.IsSatisfied,
      show m < m + 1 by grind, show ¬ m + 1 < m + 1 by grind,
      toList_self_eq_nil]
  | succ n ih =>
    simp only [show m + (n + 1) = m + n + 1 by grind,
      Std.PRange.toList_eq_match (r := m...(m + n + 2)),
      Std.PRange.toList_eq_match (r := m...(m + n + 1)),
      Std.PRange.SupportsUpperBound.IsSatisfied,
      show m < m + n + 2 by grind, show m < m + n + 1 by grind, ↓reduceIte,
      List.cons_append, List.cons.injEq, true_and]
    rw [Std.PRange.toList_open_eq_toList_closed_of_isSome_succ?,
      Std.PRange.toList_open_eq_toList_closed_of_isSome_succ?]
    · simp only [Std.PRange.UpwardEnumerable.succ?, Option.get_some,
      show m + n + 1 = (m + 1) + n by grind, show m + n + 2 = (m + 1) + n + 1 by grind]
      apply ih
      grind
    · simp [Std.PRange.UpwardEnumerable.succ?]
    · simp [Std.PRange.UpwardEnumerable.succ?]

theorem toList_rangeMk_closed_open_append_toList_rangeMk_closed_open (l m n : Nat)
    (hlm : l ≤ m) (hmn : m ≤ n) :
    (l...m).toList ++ (m...n).toList = (l...n).toList := by
  rw [show n = m + (n - m) by grind]
  generalize n - m = n
  induction n with
  | zero =>
    suffices (m...m).toList = [] by simp [this]
    simp [Std.PRange.toList_eq_nil_iff, Std.PRange.BoundedUpwardEnumerable.init?,
        Std.PRange.SupportsUpperBound.IsSatisfied]
  | succ n ih =>
    rw [show m + (n + 1) = (m + n) + 1 by grind]
    rw [ClosedOpen.toList_succ_eq_append (by grind), ClosedOpen.toList_succ_eq_append (by grind)]
    simp [← ih]

theorem isPrime_iff {n : Nat} :
    isPrime n ↔ IsPrime n := by
  simp only [isPrime_eq_true_iff]
  by_cases hn : n ≥ 2; rotate_left
  · rw [ClosedOpen.toList_eq_nil_of_le (by grind)]
    grind [IsPrime]
  have := toList_rangeMk_closed_open_append_toList_rangeMk_closed_open 1 2 n
    (by grind) (by grind [IsPrime])
  simp only [← this, ClosedOpen.toList_succ_eq_append (Nat.le_refl 1), ClosedOpen.toList_self_eq_nil]
  simp only [List.nil_append, List.cons_append, Nat.one_dvd, decide_true, List.filter_cons_of_pos,
    List.length_cons, Nat.add_eq_right, List.length_eq_zero_iff, List.filter_eq_nil_iff,
    decide_eq_true_eq] -- these come from `simp?`
  simp only [Std.PRange.mem_toList_iff_mem, Std.PRange.mem_iff_isSatisfied,
    Std.PRange.SupportsLowerBound.IsSatisfied, Std.PRange.SupportsUpperBound.IsSatisfied, IsPrime]
  apply Iff.intro
  · intro h
    apply And.intro
    · exact hn
    · intro d hd
      have : 0 < d := pos_of_divides_of_pos hd (by grind)
      have : d ≤ n := le_of_divides_of_pos hd (by grind)
      specialize h d
      grind
  · grind

open scoped Classical in
theorem x_or_y_of_isPrime {n : Int} {x y : α} :
    x_or_y n x y = if n ≥ 0 ∧ IsPrime n.toNat then x else y := by
  generalize hwp : x_or_y n x y = w
  apply Std.Do.Id.of_wp_run_eq hwp
  mvcgen
  · grind [isPrime_iff, Int.mem_toNat?]
  · grind [isPrime_iff, Int.mem_toNat?]
  · suffices n < 0 by grind
    rename_i _ h₁ h₂
    specialize h₁ n.toNat
    cases h₂
    grind [Int.mem_toNat?]

/-!
## Prompt

```python3

def x_or_y(n, x, y):
    """A simple program which should return the value of x if n is
    a prime number and should return the value of y otherwise.

    Examples:
    for x_or_y(7, 34, 12) == 34
    for x_or_y(15, 8, 5) == 5

    """
```

## Canonical solution

```python3
    if n == 1:
        return y
    for i in range(2, n):
        if n % i == 0:
            return y
            break
    else:
        return x
```

## Tests

```python3
def check(candidate):

    # Check some simple cases
    assert candidate(7, 34, 12) == 34
    assert candidate(15, 8, 5) == 5
    assert candidate(3, 33, 5212) == 33
    assert candidate(1259, 3, 52) == 3
    assert candidate(7919, -1, 12) == -1
    assert candidate(3609, 1245, 583) == 583
    assert candidate(91, 56, 129) == 129
    assert candidate(6, 34, 1234) == 1234


    # Check some edge cases that are easy to work out by hand.
    assert candidate(1, 2, 0) == 0
    assert candidate(2, 2, 0) == 2

```
-/
