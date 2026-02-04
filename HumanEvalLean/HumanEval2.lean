module

/-!
# Problem 2

## Implementation
-/

def truncateNumber (x : Rat) : Rat :=
  x - x.floor

/-!
## Tests
-/

example : truncateNumber (7/2) = 1/2 := by native_decide
example : truncateNumber (133/100) = 33/100 := by native_decide
example : truncateNumber (123456/1000) = 456/1000 := by native_decide

/-!
## Missing API
-/

theorem Rat.intCast_le_floor {x : Rat} {y : Int} :
    x.floor + y ≤ (x + y).floor := by
  simp only [Rat.le_floor_iff]
  grind [Rat.floor_le]

theorem Rat.floor_add_intCast {x : Rat} {y : Int} :
    (x + y).floor = x.floor + y := by
  apply Std.le_antisymm
  · have := intCast_le_floor (x := x + y) (y := - y)
    grind
  · apply intCast_le_floor

theorem Rat.floor_sub_one {x : Rat} :
    (x - 1).floor = x.floor - 1 := by
  have := floor_add_intCast (x := x) (y := - 1)
  grind

theorem Rat.lt_floor {x : Rat} :
    x - 1 < x.floor := by
  rw [← Rat.floor_lt_iff, Rat.floor_sub_one]
  grind

/-!
## Verification
-/

/--
{lean}`x.floor` is the largest integer less than or equal to `x`.
In other words, if {given}`k : Int` is less than or equal to `x`, then `k ≤ x.floor`.
-/
theorem le_floor_of_le_self {x : Rat} {k : Int} (h : k ≤ x) :
    k ≤ x.floor :=
  Rat.le_floor_iff.mpr h

/--
Every rational number `x` is the sum of `x.floor` and `truncateNumber x`.
-/
theorem floor_add_truncateNumber :
    x.floor + truncateNumber x = x := by
  grind [truncateNumber]

theorem zero_le_truncateNumber :
    0 ≤ truncateNumber x := by
  grind [Rat.floor_le, truncateNumber]

theorem truncateNumber_lt_one :
    truncateNumber x < 1 := by
  grind [Rat.lt_floor, truncateNumber]

/-!
## Prompt

```python3


def truncate_number(number: float) -> float:
    """ Given a positive floating point number, it can be decomposed into
    and integer part (largest integer smaller than given number) and decimals
    (leftover part always smaller than 1).

    Return the decimal part of the number.
    >>> truncate_number(3.5)
    0.5
    """
```

## Canonical solution

```python3
    return number % 1.0
```

## Tests

```python3


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    assert candidate(3.5) == 0.5
    assert abs(candidate(1.33) - 0.33) < 1e-6
    assert abs(candidate(123.456) - 0.456) < 1e-6
```
-/
