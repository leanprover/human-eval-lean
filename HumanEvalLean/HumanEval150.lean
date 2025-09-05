import Std.Data.Iterators
import Init.Notation
import Std.Tactic.Do

open Std.Iterators

/-!
## Implementation
-/

def isPrime (n : Nat) : Bool :=
  let divisors := (2...<n).iter.takeWhile (fun i => i * i ≤ n) |>.filter (· ∣ n)
  2 ≤ n ∧ divisors.fold (init := 0) (fun count _ => count + 1) = 0

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
  2 ≤ n ∧ ∀ d : Nat, d ∣ n → d = 1 ∨ d = n

theorem le_of_divides_of_pos {k n : Nat} (h : k ∣ n) (h' : n > 0) : k ≤ n := by
  false_or_by_contra
  have : n / k = 0 := by grind [Nat.div_eq_zero_iff]
  grind [Nat.dvd_iff_div_mul_eq]

theorem isPrime_eq_true_iff {n : Nat} :
    isPrime n = true ↔ 2 ≤ n ∧
        (List.filter (· ∣ n) (List.takeWhile (fun i => i * i ≤ n) (2...n).toList)).length = 0 := by
  simp [isPrime, ← Iter.foldl_toList]

theorem isPrime_iff_mul_self {n : Nat} :
    IsPrime n ↔ (2 ≤ n ∧ ∀ (a : Nat), 2 ≤ a ∧ a < n → a ∣ n → n < a * a) := by
  rw [IsPrime]
  by_cases hn : 2 ≤ n; rotate_left; grind
  apply Iff.intro
  · grind
  · rintro ⟨hn, h⟩
    refine ⟨hn, fun d hd => ?_⟩
    · have : 0 < d := Nat.pos_of_dvd_of_pos hd (by grind)
      have : d ≤ n := Nat.le_of_dvd (by grind) hd
      false_or_by_contra
      by_cases hsq : d * d ≤ n
      · specialize h d
        grind
      · replace h := h (n / d) ?_ ?_; rotate_left
        · have : d ≥ 2 := by grind
          refine ⟨?_, Nat.div_lt_self (n := n) (k := d) (by grind) (by grind)⟩
          false_or_by_contra; rename_i hc
          have : n / d * d ≤ 1 * d := Nat.mul_le_mul_right d (Nat.le_of_lt_succ (Nat.lt_of_not_ge hc))
          grind [Nat.dvd_iff_div_mul_eq]
        · exact Nat.div_dvd_of_dvd hd
        simp only [Nat.not_le] at hsq
        have := Nat.mul_lt_mul_of_lt_of_lt h hsq
        replace : n * n < ((n / d) * d) * ((n / d) * d) := by grind
        rw [Nat.dvd_iff_div_mul_eq] at hd
        grind

theorem ClosedOpen.toList_eq_nil_of_le {m n : Nat} (h : n ≤ m) :
    (m...n).toList = [] := by
  simp [Std.PRange.toList_eq_nil_iff, Std.PRange.BoundedUpwardEnumerable.init?,
    Std.PRange.SupportsUpperBound.IsSatisfied, show n ≤ m by grind]

theorem List.takeWhile_eq_filter {P : α → Bool} {xs : List α}
    (h : xs.Pairwise (fun x y => P y → P x)) :
    xs.takeWhile P = xs.filter P := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [takeWhile_cons, filter_cons]
    simp only [pairwise_cons] at h
    split
    · simp [*]
    · simpa [*] using h

theorem isPrime_eq_true_iff_isPrime {n : Nat} :
    isPrime n ↔ IsPrime n := by
  simp only [isPrime_eq_true_iff]
  by_cases hn : 2 ≤ n; rotate_left
  · rw [ClosedOpen.toList_eq_nil_of_le (by grind)]
    grind [IsPrime]
  rw [List.takeWhile_eq_filter]; rotate_left
  · apply Std.PRange.pairwise_toList_le.imp
    intro a b hab hb
    have := Nat.mul_self_le_mul_self hab
    grind
  simp [Std.PRange.mem_toList_iff_mem, Std.PRange.mem_iff_isSatisfied,
    Std.PRange.SupportsLowerBound.IsSatisfied, Std.PRange.SupportsUpperBound.IsSatisfied,
    isPrime_iff_mul_self]

open Classical in
theorem x_or_y_of_isPrime {n : Int} {x y : α} :
    x_or_y n x y = if n ≥ 0 ∧ IsPrime n.toNat then x else y := by
  generalize hwp : x_or_y n x y = w
  apply Std.Do.Id.of_wp_run_eq hwp
  mvcgen
  · grind [isPrime_eq_true_iff_isPrime, Int.mem_toNat?]
  · grind [isPrime_eq_true_iff_isPrime, Int.mem_toNat?]
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
