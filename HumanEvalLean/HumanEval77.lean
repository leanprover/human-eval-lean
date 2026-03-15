module

public section

open Std

/-! ## Implementation -/

def isCubeOfRange (x : Int) (lower : Int) (upper : Int) : Bool :=
    if upper ≤ lower + 1 then
      lower ^ 3 = x
    else
      let mid := (lower + upper) / 2
      isCubeOfRange x lower mid || isCubeOfRange x mid upper
termination_by (upper - lower).toNat

def isCube (x : Int) : Bool :=
  isCubeOfRange x (- Int.natAbs x) (Int.natAbs x + 1)

/-! ## Tests -/

example : isCube 1 = true := by native_decide
example : isCube 2 = false := by native_decide
example : isCube (-1) = true := by native_decide
example : isCube 64 = true := by native_decide
example : isCube 180 = false := by native_decide
example : isCube 1000 = true := by native_decide
example : isCube 0 = true := by native_decide
example : isCube 1729 = false := by native_decide

/-! ## Missing API -/

theorem Int.natAbs_le_iff {x y : Int} :
    x.natAbs ≤ y ↔ x ≤ y ∧ -x ≤ y := by
  grind

theorem Int.le_pow {x : Int} (h : 0 ≤ x) (hn : 0 < n) :
    x ≤ x ^ n := by
  have : x.toNat ≤ x.toNat ^ n := Nat.le_pow (by grind)
  grind

protected theorem Int.mul_le_mul_iff_of_pos_left {a b c : Int} (ha : 0 < a) : a * b ≤ a * c ↔ b ≤ c :=
  ⟨(le_of_mul_le_mul_left · ha), (Int.mul_le_mul_of_nonneg_left · (Int.le_of_lt ha))⟩

protected theorem Int.mul_nonneg_iff_of_pos_left {a b : Int} (ha : 0 < a) : 0 ≤ a * b ↔ 0 ≤ b := by
  simpa using (Int.mul_le_mul_iff_of_pos_left ha : a * 0 ≤ a * b ↔ 0 ≤ b)

protected theorem Int.mul_nonneg_iff {a b : Int} :
    0 ≤ a * b ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 := by
  constructor
  · intro h
    cases hcmp : compare 0 a
    · rw [Int.mul_nonneg_iff_of_pos_left (by grind)] at h
      grind
    · grind
    · let a' := -a
      let b' := -b
      replace h : 0 ≤ a' * b' := by grind
      have : 0 < a' := by grind
      rw [Int.mul_nonneg_iff_of_pos_left (by grind)] at h
      grind
  · rintro (h | h)
    · exact Int.mul_nonneg (by grind) (by grind)
    · exact Int.mul_nonneg_of_nonpos_of_nonpos (by grind) (by grind)

protected theorem Int.mul_pos_iff {a b : Int} :
    0 < a * b ↔ 0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0 := by
  let a' := -a
  suffices ¬ 0 ≤ a' * b ↔ a' < 0 ∧ 0 < b ∨ 0 < a' ∧ b < 0 by grind
  rw [Int.mul_nonneg_iff]
  grind

protected theorem Int.mul_neg_iff_of_neg_right {a b : Int} (hb : b < 0) : a * b < 0 ↔ 0 < a := by
  suffices ¬ 0 ≤ a * b ↔ 0 < a by grind
  rw [Int.mul_nonneg_iff]
  grind

protected theorem Int.mul_self_nonneg {a : Int} :
    0 ≤ a * a := by
  rw [Int.mul_nonneg_iff]
  grind

protected theorem Int.mul_self_pos {a : Int} (h : a ≠ 0) :
    0 < a * a := by
  rw [Int.mul_pos_iff]
  grind

/-! ## Verification -/

private theorem isCubeOfRange_iff (h : lower < upper) :
    isCubeOfRange x lower upper ↔ ∃ y ∈ lower...upper, y ^ 3 = x := by
  fun_induction isCubeOfRange x lower upper <;> grind [Rco.mem_iff]

private theorem Int.pow_three_lt_pow_three {x y : Int} (h : x < y) :
    x ^ 3 < y ^ 3 := by
  simp only [show ∀ x : Int, x ^ 3 = x * x * x by grind]
  by_cases 0 ≤ x
  · apply Int.mul_lt_mul'
    · apply Int.mul_self_le_mul_self (by grind) (by grind)
    · grind
    · grind
    · have : 0 < y := by grind
      apply Int.mul_pos (by grind) (by grind)
  · by_cases 0 ≤ y
    · have : x * x * x < 0 := by
        rw [Int.mul_neg_iff_of_neg_right]
        · apply Int.mul_self_pos (by grind)
        · grind
      have : 0 ≤ y * y * y := by
        apply Int.mul_nonneg
        · apply Int.mul_self_nonneg
        · assumption
      grind
    · let x' := -x
      let y' := -y
      suffices y' * y' * y' < x' * x' * x' by grind
      apply Int.mul_lt_mul'
      · apply Int.mul_self_le_mul_self (by grind) (by grind)
      · grind
      · grind
      · have : 0 < x' := by grind
        apply Int.mul_pos (by grind) (by grind)

private theorem Int.pow_three_le_pow_three_iff {x y : Int} :
    x ^ 3 ≤ y ^ 3 ↔ x ≤ y := by
  have := Int.pow_three_lt_pow_three (x := x) (y := y)
  have := Int.pow_three_lt_pow_three (x := y) (y := x)
  cases hcmp : compare x y <;> grind

theorem isCube_iff :
    isCube x ↔ ∃ y, y ^ 3 = x := by
  rw [isCube, isCubeOfRange_iff]
  · constructor
    · grind
    · rintro ⟨y, hy⟩
      refine ⟨y, ?_, hy⟩
      simp only [Rco.mem_iff, ← hy, Int.natAbs_pow, Int.natCast_pow, Int.lt_add_one_iff,
        Int.neg_le_iff, and_comm, ← Int.natAbs_le_iff]
      exact Int.le_pow (by grind) (by grind)
  · grind

/-!
## Prompt

```python3

def iscube(a):
    '''
    Write a function that takes an integer a and returns True
    if this ingeger is a cube of some integer number.
    Note: you may assume the input is always valid.
    Examples:
    iscube(1) ==> True
    iscube(2) ==> False
    iscube(-1) ==> True
    iscube(64) ==> True
    iscube(0) ==> True
    iscube(180) ==> False
    '''
```

## Canonical solution

```python3
    a = abs(a)
    return int(round(a ** (1. / 3))) ** 3 == a
```

## Tests

```python3
def check(candidate):

    # Check some simple cases
    assert candidate(1) == True, "First test error: " + str(candidate(1))
    assert candidate(2) == False, "Second test error: " + str(candidate(2))
    assert candidate(-1) == True, "Third test error: " + str(candidate(-1))
    assert candidate(64) == True, "Fourth test error: " + str(candidate(64))
    assert candidate(180) == False, "Fifth test error: " + str(candidate(180))
    assert candidate(1000) == True, "Sixth test error: " + str(candidate(1000))


    # Check some edge cases that are easy to work out by hand.
    assert candidate(0) == True, "1st edge test error: " + str(candidate(0))
    assert candidate(1729) == False, "2nd edge test error: " + str(candidate(1728))

```
-/
