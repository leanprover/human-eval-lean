section Batteries

-- https://github.com/leanprover-community/batteries/pull/1267
@[simp] theorem isDigit_digitChar : n.digitChar.isDigit = decide (n < 10) := sorry
theorem Nat.mem_toDigits_base_10_isDigit (h : c ∈ toDigits 10 n) : c.isDigit := sorry

theorem Nat.toDigits_10_of_lt_10 (h : n < 10) : toDigits 10 n = [n.digitChar] := by
  sorry

theorem Nat.toDigits_10_decompose (h : d < 10) (n : Nat) :
    toDigits 10 (10 * n + d) = (toDigits 10 n) ++ (toDigits 10 d) :=
  sorry

@[simp]
theorem Nat.toDigits_10_natAbs_cast (n : Nat) : toDigits 10 (n : Int).natAbs = toDigits 10 n :=
  sorry

end Batteries

abbrev Digit := { c : Char // c.isDigit }

namespace Nat

def digits (n : Nat) : List Digit :=
  n.toDigits (base := 10)
    |>.attach
    |>.map fun ⟨j, h⟩ => ⟨j, Nat.mem_toDigits_base_10_isDigit h⟩

theorem digits_of_lt_10 (h : n < 10) : n.digits = [⟨n.digitChar, by simp_all⟩] := by
  sorry

theorem digits_decompose (h : d < 10) (n : Nat) : (10 * n + d).digits = n.digits ++ d.digits := by
  simp [digits]
  -- PROBLEM: When appending lists with `attach`es, the membership witnesses change.
  -- rw [toDigits_10_decompose h]
  sorry

end Nat

@[simp]
theorem Int.digits_natAbs_cast (n : Nat) : (n : Int).natAbs.digits = n.digits := by
  simp [Nat.digits]

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
  sorry

theorem log_digitChar (h : d < 10) (t : Tally) :
    t.log ⟨d.digitChar, by simp_all⟩ = t + ⟨1 - d % 2, d % 2⟩ :=
  sorry

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

theorem count_decompose (hd : d < 10) : count (10 * n + d) = count n + count d := by
  simp only [count, Int.digits_natAbs_cast, Nat.digits_decompose hd, List.foldl_append]
  rw [log_foldl, add_comm]

theorem count_decompose' (hd : d < 10) : count (10 * n + d) = count n + ⟨1 - d % 2, d % 2⟩ := by
  rw [← count_of_lt_10 hd, count_decompose hd]

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
