module

import all Init.Data.Repr -- to be removed as soon as all of this is upstreamed to stdlib

public section

section Batteries -- https://github.com/leanprover-community/batteries/pull/1267

namespace Nat

@[simp]
theorem isDigit_digitChar : n.digitChar.isDigit = decide (n < 10) :=
  match n with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => by simp [digitChar]
  | _ + 10 => by
    simp only [digitChar, ↓reduceIte, Nat.reduceEqDiff]
    (repeat' split) <;> simp

private theorem isDigit_of_mem_toDigitsCore
    (hc : c ∈ cs → c.isDigit) (hb₁ : 0 < b) (hb₂ : b ≤ 10) (h : c ∈ toDigitsCore b fuel n cs) :
    c.isDigit := by
  induction fuel generalizing n cs with rw [toDigitsCore] at h
  | zero => exact hc h
  | succ _ ih =>
    split at h
    case' isFalse => apply ih (fun h => ?_) h
    all_goals
      cases h with
      | head      => simp [Nat.lt_of_lt_of_le (mod_lt _ hb₁) hb₂]
      | tail _ hm => exact hc hm

theorem isDigit_of_mem_toDigits (hb₁ : 0 < b) (hb₂ : b ≤ 10) (hc : c ∈ toDigits b n) : c.isDigit :=
  isDigit_of_mem_toDigitsCore (fun _ => by contradiction) hb₁ hb₂ hc

private theorem toDigitsCore_of_lt_base (hb : n < b) (hf : n < fuel) :
    toDigitsCore b fuel n cs = n.digitChar :: cs := by
  unfold toDigitsCore
  split <;> simp_all [mod_eq_of_lt]

theorem toDigits_of_lt_base (h : n < b) : toDigits b n = [n.digitChar] :=
  toDigitsCore_of_lt_base h (lt_succ_self _)

theorem toDigits_zero : (b : Nat) → toDigits b 0 = ['0']
  | 0     => rfl
  | _ + 1 => toDigits_of_lt_base (zero_lt_succ _)

private theorem toDigitsCore_append :
    toDigitsCore b fuel n cs₁ ++ cs₂ = toDigitsCore b fuel n (cs₁ ++ cs₂) := by
  induction fuel generalizing n cs₁ with simp only [toDigitsCore]
  | succ => split <;> simp_all

private theorem toDigitsCore_eq_of_lt_fuel (hb : 1 < b) (h₁ : n < fuel₁) (h₂ : n < fuel₂) :
    toDigitsCore b fuel₁ n cs = toDigitsCore b fuel₂ n cs := by
  cases fuel₁ <;> cases fuel₂ <;> try contradiction
  simp only [toDigitsCore, Nat.div_eq_zero_iff]
  split
  · simp
  · have := Nat.div_lt_self (by omega : 0 < n) hb
    exact toDigitsCore_eq_of_lt_fuel hb (by omega) (by omega)

private theorem toDigitsCore_toDigitsCore
    (hb : 1 < b) (hn : 0 < n) (hd : d < b) (hf : b * n + d < fuel) (hnf : n < nf) (hdf : d < df) :
    toDigitsCore b nf n (toDigitsCore b df d cs) = toDigitsCore b fuel (b * n + d) cs := by
  cases fuel with
  | zero => contradiction
  | succ fuel =>
    rw [toDigitsCore]
    split
    case isTrue h =>
      have : b ≤ b * n + d := Nat.le_trans (Nat.le_mul_of_pos_right _ hn) (le_add_right _ _)
      cases Nat.div_eq_zero_iff.mp h <;> omega
    case isFalse =>
      have h : (b * n + d) / b = n := by
        rw [mul_add_div (by omega), Nat.div_eq_zero_iff.mpr (.inr hd), Nat.add_zero]
      have := (Nat.lt_mul_iff_one_lt_left hn).mpr hb
      simp only [toDigitsCore_of_lt_base hd hdf, mul_add_mod_self_left, mod_eq_of_lt hd, h]
      apply toDigitsCore_eq_of_lt_fuel hb hnf (by omega)

theorem toDigits_append_toDigits (hb : 1 < b) (hn : 0 < n) (hd : d < b) :
    (toDigits b n) ++ (toDigits b d) = toDigits b (b * n + d) := by
  rw [toDigits, toDigitsCore_append]
  exact toDigitsCore_toDigitsCore hb hn hd (lt_succ_self _) (lt_succ_self _) (lt_succ_self _)

end Nat

end Batteries

abbrev Digit := { c : Char // c.isDigit }

namespace Nat

def digits (n : Nat) : List Digit :=
  n.toDigits (base := 10)
    |>.attachWith (·.isDigit) fun _ h => Nat.isDigit_of_mem_toDigits (by decide) (by decide) h

theorem digits_of_lt_10 (h : n < 10) : n.digits = [⟨n.digitChar, by simp_all⟩] := by
  simp [digits, toDigits_of_lt_base h]

theorem digits_append_digits (hn : 0 < n) (hd : d < 10) :
    n.digits ++ d.digits = (10 * n + d).digits := by
  simp [digits, ← toDigits_append_toDigits, *]

end Nat

structure Tally where
  even : Nat
  odd  : Nat
deriving Inhabited

namespace Tally

instance : Add Tally where
  add t₁ t₂ := { even := t₁.even + t₂.even, odd := t₁.odd + t₂.odd }

@[simp]
theorem empty_add (t : Tally) : ⟨0, 0⟩ + t = t := by
  simp only [(· + ·), Add.add]
  simp

@[simp]
theorem add_even (t₁ t₂ : Tally) : (t₁ + t₂).even = t₁.even + t₂.even := by
  simp only [(· + ·), Add.add]

@[simp]
theorem add_odd (t₁ t₂ : Tally) : (t₁ + t₂).odd = t₁.odd + t₂.odd := by
  simp only [(· + ·), Add.add]

theorem add_comm (t₁ t₂ : Tally) : t₁ + t₂ = t₂ + t₁ := by
  simp only [(· + ·), Add.add]
  simp +arith

theorem add_assoc (t₁ t₂ : Tally) : t₁ + t₂ + t₃ = t₁ + (t₂ + t₃) := by
  simp only [(· + ·), Add.add]
  simp +arith

def total (t : Tally) : Nat :=
  t.even + t.odd

@[simp]
theorem total_add (t₁ t₂ : Tally) : (t₁ + t₂).total = t₁.total + t₂.total := by
  simp +arith [total]

def log (t : Tally) (d : Digit) : Tally :=
  match d.val with
  | '0' | '2' | '4' | '6' | '8' => { t with even := t.even + 1 }
  | _                           => { t with odd  := t.odd  + 1 }

theorem log_add (t₁ t₂ : Tally) (d : Digit) : (t₁.log d) + t₂ = (t₁ + t₂).log d := by
  simp only [log]
  split
  all_goals
    simp only [(· + ·), Add.add]
    simp +arith

theorem log_digitChar (h : d < 10) (t : Tally) :
    t.log ⟨d.digitChar, by simp_all⟩ = t + ⟨1 - d % 2, d % 2⟩ := by
  match d with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => rfl
  | _ + 10                                => contradiction

-- Folding `log` over a given tally `init` produces the same tally as folding `log` over `⟨0, 0⟩`
-- and adding that to `init`.
theorem log_foldl {ds : List Digit} (init : Tally) :
    (ds.foldl log init) = (ds.foldl log ⟨0, 0⟩) + init := by
  induction ds generalizing init
  case nil          => simp
  case cons hd _ ih => simp +arith [List.foldl_cons, ih (log _ hd), add_assoc, log_add]

-- Folding `log` over a given tally `init` produces the same total digit count as folding `log` over
-- `⟨0, 0⟩` and adding that to `init`.
theorem log_total_foldl {ds : List Digit} (init : Tally) :
    (ds.foldl log init).total = (ds.foldl log ⟨0, 0⟩).total + init.total := by
  rw [log_foldl]
  simp

-- Applying `log` increases a tally's total by `1`.
theorem log_total (d : Digit) (t : Tally) : (t.log d).total = t.total + 1 := by
  rw [log]
  split <;> simp +arith [total]

def count (n : Nat) : Tally :=
  n.digits.foldl log ⟨0, 0⟩

-- The tally total produced by `count` matches the number of digits in the input.
theorem count_total_eq_length : (count n).total = n.digits.length := by
  rw [count]
  generalize n.digits = ds
  induction ds
  case nil     => rfl
  case cons ih => rw [List.foldl_cons, List.length_cons, log_total_foldl, ih, log_total]; rfl

theorem count_of_lt_10 (hd : d < 10) : count d = ⟨1 - d % 2, d % 2⟩ := by
  simp [count, Nat.digits_of_lt_10, log_digitChar, hd]

theorem count_add (hn : 0 < n) (hd : d < 10) : count n + count d = count (10 * n + d) := by
  simp only [count, ← Nat.digits_append_digits hn hd, List.foldl_append]
  conv => rhs; rw [log_foldl]
  apply add_comm

theorem count_decompose (hn : 0 < n) (hd : d < 10) :
    count (10 * n + d) = count n + ⟨1 - d % 2, d % 2⟩ := by
  rw [← count_of_lt_10 hd, count_add hn hd]

def evenOddCount (i : Int) : Tally :=
  count i.natAbs

example : evenOddCount (-12) = ⟨1, 1⟩     := rfl
example : evenOddCount 123 = ⟨1, 2⟩       := rfl
example : evenOddCount 7 = ⟨0, 1⟩         := rfl
example : evenOddCount (-78) = ⟨1, 1⟩     := rfl
example : evenOddCount 3452 = ⟨2, 2⟩      := rfl
example : evenOddCount 346211 = ⟨3, 3⟩    := rfl
example : evenOddCount (-345821) = ⟨3, 3⟩ := rfl
example : evenOddCount (-2) = ⟨1, 0⟩      := rfl
example : evenOddCount (-45347) = ⟨2, 3⟩  := rfl
example : evenOddCount 0 = ⟨1, 0⟩         := rfl

/-!
## Prompt

```python3

def even_odd_count(num):
    """Given an integer. return a tuple that has the number of even and odd digits respectively.

     Example:
        even_odd_count(-12) ==> (1, 1)
        even_odd_count(123) ==> (1, 2)
    """
```

## Canonical solution

```python3
    even_count = 0
    odd_count = 0
    for i in str(abs(num)):
        if int(i)%2==0:
            even_count +=1
        else:
            odd_count +=1
    return (even_count, odd_count)
```

## Tests

```python3
def check(candidate):

    # Check some simple cases
    assert candidate(7) == (0, 1)
    assert candidate(-78) == (1, 1)
    assert candidate(3452) == (2, 2)
    assert candidate(346211) == (3, 3)
    assert candidate(-345821) == (3, 3)
    assert candidate(-2) == (1, 0)
    assert candidate(-45347) == (2, 3)
    assert candidate(0) == (1, 0)


    # Check some edge cases that are easy to work out by hand.
    assert True

```
-/
