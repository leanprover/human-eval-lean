module

public section

/-!
## Implementation
-/

private def isSimplePowerHelper (x n : Nat) (hx : 0 < x) (hn : 1 < n) : Bool :=
  if _ : x = 1 then
    true
  else if hdvd : n ∣ x then
    isSimplePowerHelper (x / n) n (Nat.pos_of_dvd_of_pos (Nat.div_dvd_of_dvd hdvd) hx) hn
  else
    false
termination_by x
decreasing_by
  rw [Nat.div_lt_iff_lt_mul (by grind), Nat.lt_mul_iff_one_lt_right hx]
  grind

def isSimplePower (x n : Nat) : Bool :=
  if _ : n = 0 then
    x ≤ 1
  else if _ : n = 1 then
    x = 1
  else if _ : x = 0 then
    false
  else
    isSimplePowerHelper x n (by grind) (by grind)

/-!
## Tests
-/

example : isSimplePower 16 2 = true := by cbv
example : isSimplePower 143214 16 = false := by cbv
example : isSimplePower 4 2 = true := by cbv
example : isSimplePower 9 3 = true := by cbv
example : isSimplePower 16 4 = true := by cbv
example : isSimplePower 24 2 = false := by cbv
example : isSimplePower 128 4 = false := by cbv
example : isSimplePower 12 6 = false := by cbv
example : isSimplePower 1 1 = true := by cbv
example : isSimplePower 1 12 = true := by cbv

/-!
## Verification
-/

private theorem isSimplePowerHelper_iff :
    isSimplePowerHelper x n hx hn ↔ ∃ i, n ^ i = x := by
  fun_induction isSimplePowerHelper x n hx hn
  · simp
  · rename_i ih
    rw [ih]
    constructor
    · rintro ⟨i, hi⟩
      refine ⟨i + 1, ?_⟩
      simp only [Nat.pow_add, Nat.pow_one]
      rw [hi, Nat.div_mul_cancel ‹_›]
    · rintro ⟨i, hi⟩
      match i with
      | 0 => grind
      | i + 1 =>
        refine ⟨i, ?_⟩
        rw [Nat.eq_div_iff_mul_eq_left (by grind) ‹_›]
        grind
  · simp only [Bool.false_eq_true, false_iff, not_exists]
    intro i
    match i with
    | 0 => grind
    | i' + 1 =>
      have := Nat.dvd_mul_left n (n ^ i')
      grind

theorem isSimplePower_iff :
    isSimplePower x n ↔ ∃ i, n ^ i = x := by
  fun_cases isSimplePower
  · rename_i hn
    cases hn
    constructor
    · intro h
      match x with
      | 0 => exact ⟨1, by grind⟩
      | 1 => exact ⟨0, by grind⟩
      | _ + 2 => grind
    · rintro ⟨i, hi⟩
      match i with
      | 0 | _ + 1 => grind
  · simp_all [eq_comm]
  · simp_all
  · apply isSimplePowerHelper_iff

/-!
## Prompt

```python3

def is_simple_power(x, n):
    """Your task is to write a function that returns true if a number x is a simple
    power of n and false in other cases.
    x is a simple power of n if n**int=x
    For example:
    is_simple_power(1, 4) => true
    is_simple_power(2, 2) => true
    is_simple_power(8, 2) => true
    is_simple_power(3, 2) => false
    is_simple_power(3, 1) => false
    is_simple_power(5, 3) => false
    """
```

## Canonical solution

```python3
    if (n == 1):
        return (x == 1)
    power = 1
    while (power < x):
        power = power * n
    return (power == x)
```

## Tests

```python3
def check(candidate):

    # Check some simple cases
    assert candidate(16, 2)== True, "This prints if this assert fails 1 (good for debugging!)"
    assert candidate(143214, 16)== False, "This prints if this assert fails 1 (good for debugging!)"
    assert candidate(4, 2)==True, "This prints if this assert fails 1 (good for debugging!)"
    assert candidate(9, 3)==True, "This prints if this assert fails 1 (good for debugging!)"
    assert candidate(16, 4)==True, "This prints if this assert fails 1 (good for debugging!)"
    assert candidate(24, 2)==False, "This prints if this assert fails 1 (good for debugging!)"
    assert candidate(128, 4)==False, "This prints if this assert fails 1 (good for debugging!)"
    assert candidate(12, 6)==False, "This prints if this assert fails 1 (good for debugging!)"

    # Check some edge cases that are easy to work out by hand.
    assert candidate(1, 1)==True, "This prints if this assert fails 2 (also good for debugging!)"
    assert candidate(1, 12)==True, "This prints if this assert fails 2 (also good for debugging!)"

```
-/
