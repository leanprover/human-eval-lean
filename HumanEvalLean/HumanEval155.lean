section Batteries -- https://github.com/leanprover-community/batteries/pull/1267

@[simp]
theorem Nat.isDigit_digitChar : n.digitChar.isDigit = decide (n < 10) :=
  sorry

theorem Nat.isDigit_of_mem_toDigits (hb₁ : 0 < b) (hb₂ : b ≤ 10) (hc : c ∈ toDigits b n) :
    c.isDigit :=
  sorry

theorem Nat.toDigits_of_lt_base (h : n < b) : toDigits b n = [n.digitChar] :=
  sorry

theorem Nat.toDigits_append_toDigits (hb₁ : 1 < b) (hb₂ : b ≤ 10) (hn : 0 < n) (hd : d < b) :
    (toDigits b n) ++ (toDigits b d) = toDigits b (b * n + d) := by
  sorry

end Batteries

abbrev Digit := { c : Char // c.isDigit }

namespace Nat

def digits (n : Nat) : List Digit :=
  n.toDigits (base := 10)
    |>.attach
    |>.map fun ⟨j, h⟩ => ⟨j, Nat.isDigit_of_mem_toDigits (by decide) (by decide) h⟩

theorem digits_of_lt_10 (h : n < 10) : n.digits = [⟨n.digitChar, by simp_all⟩] := by
  simp only [digits, List.map_eq_singleton_iff, Subtype.mk.injEq, Subtype.exists, exists_and_right,
             exists_eq_right]
  rw [toDigits_of_lt_base h]
  exists List.mem_singleton_self _

theorem digits_append_digits (hn : 0 < n) (hd : d < 10) :
    n.digits ++ d.digits = (10 * n + d).digits := by
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
