module

/-!
## Implementation

There is nothing to implement: The standard library provides `Int.gcd` out of the box.

## Tests
-/

example : Int.gcd 3 7 = 1 := by native_decide
example : Int.gcd 10 15 = 5 := by native_decide
example : Int.gcd 49 14 = 7 := by native_decide
example : Int.gcd 144 60 = 12 := by native_decide

/-!
## Verification
-/

/-- info: Int.dvd_gcd_iff {a b : Int} {c : Nat} : c ∣ a.gcd b ↔ ↑c ∣ a ∧ ↑c ∣ b -/
#guard_msgs in
#check Int.dvd_gcd_iff

/-- info: Int.dvd_coe_gcd_iff {a b c : Int} : c ∣ ↑(a.gcd b) ↔ c ∣ a ∧ c ∣ b -/
#guard_msgs in
#check Int.dvd_coe_gcd_iff

theorem Int.gcd_le_of_dvd {a b : Int} {c : Nat}
    (h : (c : Int) ∣ a ∧ (c : Int) ∣ b) (hpos : 0 < a ∨ 0 < b) :
    c ≤ a.gcd b := by
  apply Nat.le_of_dvd <;> grind [Int.dvd_gcd_iff]

/-!
## Prompt

```python3


def greatest_common_divisor(a: int, b: int) -> int:
    """ Return a greatest common divisor of two integers a and b
    >>> greatest_common_divisor(3, 5)
    1
    >>> greatest_common_divisor(25, 15)
    5
    """
```

## Canonical solution

```python3
    while b:
        a, b = b, a % b
    return a
```

## Tests

```python3


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    assert candidate(3, 7) == 1
    assert candidate(10, 15) == 5
    assert candidate(49, 14) == 7
    assert candidate(144, 60) == 12
```
-/
