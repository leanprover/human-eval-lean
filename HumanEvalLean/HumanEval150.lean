module

import Std.Data.Iterators
import Init.Notation
import Std.Tactic.Do

import HumanEvalLean.Common.IsPrime

open Std

set_option mvcgen.warning false

/-!
## Implementation
-/

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

example {n d : Nat} (h : n / d * d = n) (h' : n * n < n / d * d * (n / d * d)) : False := by
  rw [h] at h' -- Why do we need this?
  grind

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
