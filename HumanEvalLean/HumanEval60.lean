module

public import Std
open Std

set_option cbv.warning false

/-! ## Implementation 1 -/

def sumToN (n : Nat) : Nat :=
  (n + 1) * n / 2

/-! ## Tests 1 -/

example : sumToN 1 = 1 := by cbv
example : sumToN 6 = 21 := by cbv
example : sumToN 11 = 66 := by cbv
example : sumToN 30 = 465 := by cbv
example : sumToN 100 = 5050 := by cbv

/-! ## Verification 1 -/

theorem sumToN_zero :
    sumToN 0 = 0 := by
  cbv

theorem sumToN_add_one :
    sumToN (n + 1) = sumToN n + n + 1 := by
  grind [sumToN]

/-! ## Implementation 2 -/

def sumToN' (n : Nat) : Nat :=
    (1...=n).iter.fold (init := 0) (· + ·)

/-! ## Tests 2 -/

example : sumToN' 1 = 1 := by native_decide
example : sumToN' 6 = 21 := by native_decide
example : sumToN' 11 = 66 := by native_decide
example : sumToN' 30 = 465 := by native_decide
example : sumToN' 100 = 5050 := by native_decide

/-! ## Verification 2 -/

theorem sumToN'_zero :
    sumToN' 0 = 0 := by
  simp [sumToN', ← Iter.foldl_toList]

theorem sumToN'_add_one :
    sumToN' (n + 1) = sumToN' n + n + 1 := by
  simp [sumToN', ← Iter.foldl_toList, Nat.toList_rcc_eq_toList_rco, Nat.add_assoc]

theorem sumToN_eq_sumToN' :
    sumToN n = sumToN' n := by
  induction n <;> grind [sumToN_zero, sumToN'_zero, sumToN_add_one, sumToN'_add_one]

/-!
## Prompt

```python3


def sum_to_n(n: int):
    """sum_to_n is a function that sums numbers from 1 to n.
    >>> sum_to_n(30)
    465
    >>> sum_to_n(100)
    5050
    >>> sum_to_n(5)
    15
    >>> sum_to_n(10)
    55
    >>> sum_to_n(1)
    1
    """
```

## Canonical solution

```python3
    return sum(range(n + 1))
```

## Tests

```python3


METADATA = {}


def check(candidate):
    assert candidate(1) == 1
    assert candidate(6) == 21
    assert candidate(11) == 66
    assert candidate(30) == 465
    assert candidate(100) == 5050

```
-/
