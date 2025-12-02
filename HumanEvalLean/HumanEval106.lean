module

import Std.Tactic.Do
-- Sadly, it's apparently currently impossible to easily prove the size of a
-- `Nat` range without unfolding internal stuff. This should be fixed in the standard library.
import all Init.Data.Iterators.Consumers.Loop

/-!
This file provides two solutions for problem 106: a naïve one and an efficient one.
-/

open Std.Do

section NaiveImpl

/-!
## A naïve implementation
-/

def f (n : Nat) : List Nat := Id.run do
  let mut ret : List Nat := []
  for i in 1...=n do
    if i % 2 = 0 then
      let mut x := 1
      for j in 1...=i do x := x * j
      ret := x :: ret
    else
      let mut x := 0
      for j in 1...=i do x := x + j
      ret := x :: ret
  return ret.reverse

/-!
### Tests
-/

example : f 5 = [1, 2, 6, 24, 15] := by native_decide
example : f 7 = [1, 2, 6, 24, 15, 720, 28] := by native_decide
example : f 1 = [1] := by native_decide
example : f 3 = [1, 2, 6] := by native_decide

/-!
### Verification
-/

def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => factorial n * (n + 1)

def triangle : Nat → Nat
  | 0 => 0
  | n + 1 => triangle n + (n + 1)

example : factorial 1 = 1 := by decide
example : factorial 4 = 24 := by decide
example : triangle 1 = 1 := by decide
example : triangle 4 = 10 := by decide

theorem length_f {n : Nat} :
    (f n).length = n := by
  generalize hwp : f n = w
  apply Std.Do.Id.of_wp_run_eq hwp
  mvcgen
  all_goals try infer_instance
  case inv1 => exact ⇓⟨cur, xs⟩ => ⌜xs.length = cur.prefix.length⌝
  case inv2 => exact ⇓⟨cur, xs⟩ => ⌜True⌝ -- factorial loop
  case inv3 => exact ⇓⟨cur, xs⟩ => ⌜True⌝ -- sum loop
  all_goals simp_all -- relies on `Nat.length_toList_rcc`

theorem f_eq_fac {n : Nat} {k : Nat} (hlt : k < n) :
    (f n)[k]'(by grind [length_f]) = if k % 2 = 0 then triangle (k + 1) else factorial (k + 1) := by
  rw [List.getElem_eq_iff]
  generalize hwp : f n = w
  apply Std.Do.Id.of_wp_run_eq hwp
  mvcgen
  all_goals try infer_instance

  -- OUTER LOOP
  case inv1 =>
    exact ⇓⟨cur, xs⟩ => ⌜xs.length = cur.prefix.length ∧
        ((_ : k < xs.length) → xs[xs.length - 1 - k] =
          if k % 2 = 0 then triangle (k + 1) else factorial (k + 1))⌝
  case vc7 => simp -- base case
  case vc8 => grind [Nat.length_toList_rcc] -- postcondition

  -- FACTORIAL LOOP
  case inv2 => exact ⇓⟨cur, x⟩ => ⌜x = factorial cur.prefix.length⌝
  case vc2 => simp [factorial] -- base case
  case vc3 => -- step
    simp_all only [Std.Rcc.eq_succMany?_of_toList_eq_append_cons ‹_›, Std.PRange.succMany?,
      Nat.length_toList_rcc]
    grind
  case vc1 => -- postcondition
    simp_all [Std.Rcc.eq_succMany?_of_toList_eq_append_cons ‹_›, factorial, Nat.add_comm 1]
  -- SUM LOOP
  case inv3 => exact ⇓⟨cur, x⟩ => ⌜x = triangle cur.prefix.length⌝
  case vc5 => simp [triangle] -- base case
  case vc6 => -- step
    simp_all only [Std.Rcc.eq_succMany?_of_toList_eq_append_cons ‹_›, Std.PRange.succMany?,
      Nat.length_toList_rcc]
    grind
  case vc4 => -- postcondition
    simp_all [Std.Rcc.eq_succMany?_of_toList_eq_append_cons ‹_›, triangle, Nat.add_comm 1]

end NaiveImpl

section EfficientImpl

/-!
## An efficient implementation
-/

def f' (n : Nat) : Array Nat := Id.run do
  if n ≤ 2 then
    return #[1, 2].take n
  let mut ret : Array Nat := .emptyWithCapacity n
  ret := ret.push 1 -- 1st entry should be `triangle 1`
  ret := ret.push 2 -- 2nd entry should be `factorial 2`
  for i in 2...<n do
    if i % 2 = 1 then
      -- It would be nicer if we could use `ret[i - 2]`, but it is unclear how to use the
      -- invariants `ret.size ≥ 2` and `i = ret.size` intrinsically.
      ret := ret.push (ret[i - 2]! * i * (i + 1))
    else
      ret := ret.push (ret[i - 2]! + 2 * i + 1)
  return ret

/-!
### Tests
-/

example : f' 5 = #[1, 2, 6, 24, 15] := by native_decide
example : f' 7 = #[1, 2, 6, 24, 15, 720, 28] := by native_decide
example : f' 1 = #[1] := by native_decide
example : f' 3 = #[1, 2, 6] := by native_decide

/-!
### Verification
-/

theorem size_f' {n : Nat} :
    (f' n).size = n := by
  generalize hwp : f' n = w
  apply Std.Do.Id.of_wp_run_eq hwp
  mvcgen
  all_goals try infer_instance
  case inv1 => exact ⇓⟨cur, xs⟩ => ⌜xs.size = cur.prefix.length + 2⌝
  all_goals try (simp_all; done) -- relies on `Nat.size_Rcc`
  grind [Nat.not_le, Nat.length_toList_rco]

theorem f'_eq_fac {n : Nat} {k : Nat} (hlt : k < n) :
    (f' n)[k]'(by grind [size_f']) = if k % 2 = 0 then triangle (k + 1) else factorial (k + 1) := by
  rw [Array.getElem_eq_iff]
  generalize hwp : f' n = w
  apply Std.Do.Id.of_wp_run_eq hwp
  mvcgen
  all_goals try infer_instance
  case inv1 =>
    exact ⇓⟨cur, xs⟩ => ⌜xs.size = cur.prefix.length + 2 ∧ ∀ j : Nat, (_ : j < xs.size) →
        (j % 2 = 1 → xs[j] = factorial (j + 1)) ∧ (j % 2 = 0 → xs[j] = triangle (j + 1))⌝
  case vc1 hn => -- verification of the early return
    -- the return value is a prefix of `[1, 2]` and `k` is the index that needs to be verified
    match k with
    | 0 => grind [triangle]
    | 1 => grind [factorial]
    | n + 2 => grind
  case vc4 => -- base case of the loop
    grind [triangle, factorial]
  case vc2 hmod h => -- `then` branch
    have := Std.Rco.eq_succMany?_of_toList_eq_append_cons ‹_›
    simp only [Std.PRange.UpwardEnumerable.succMany?] at this
    grind [factorial]
  case vc3 => -- `else` branch
    have := Std.Rco.eq_succMany?_of_toList_eq_append_cons ‹_›
    simp only [Std.PRange.UpwardEnumerable.succMany?] at this
    grind [triangle]
  case vc5 => -- postcondition
    grind [Nat.not_le, Nat.length_toList_rco]

end EfficientImpl

/-!
## Prompt

```python3

def f(n):
    """ Implement the function f that takes n as a parameter,
    and returns a list of size n, such that the value of the element at index i is the factorial of i if i is even
    or the sum of numbers from 1 to i otherwise.
    i starts from 1.
    the factorial of i is the multiplication of the numbers from 1 to i (1 * 2 * ... * i).
    Example:
    f(5) == [1, 2, 6, 24, 15]
    """
```

## Canonical solution

```python3
    ret = []
    for i in range(1,n+1):
        if i%2 == 0:
            x = 1
            for j in range(1,i+1): x *= j
            ret += [x]
        else:
            x = 0
            for j in range(1,i+1): x += j
            ret += [x]
    return ret
```

## Tests

```python3
def check(candidate):

    assert candidate(5) == [1, 2, 6, 24, 15]
    assert candidate(7) == [1, 2, 6, 24, 15, 720, 28]
    assert candidate(1) == [1]
    assert candidate(3) == [1, 2, 6]
```
-/
