module

import Lean.LibrarySuggestions.Default

import Std.Tactic.Do

/-!
This file provides three solutions for problem 106, progressing from most simple to most efficient.
-/

set_option mvcgen.warning false

open Std.Do

-- missing grind annotations
attribute [grind =] Nat.length_toList_rco Std.PRange.Nat.succMany?_eq Nat.not_le

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

@[grind =]
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => factorial n * (n + 1)

@[grind =]
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

theorem getElem_f {n : Nat} {k : Nat} (hlt : k < n) :
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
  grind

theorem getElem_f' {n : Nat} {k : Nat} (hlt : k < n) :
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
    | 0 => grind
    | 1 => grind
    | n + 2 => grind
  case vc4 => -- base case of the loop
    grind
  case vc2 hmod h => -- `then` branch
    have := Std.Rco.eq_succMany?_of_toList_eq_append_cons ‹_›
    simp only [Std.PRange.UpwardEnumerable.succMany?] at this
    grind
  case vc3 => -- `else` branch
    have := Std.Rco.eq_succMany?_of_toList_eq_append_cons ‹_›
    simp only [Std.PRange.UpwardEnumerable.succMany?] at this
    grind
  case vc5 => -- postcondition
    grind

end EfficientImpl

section MoreEfficientImpl

/-!
## An efficient implementation avoiding `[·]!`
-/

def f'' (n : Nat) : Array Nat := Id.run do
  if n ≤ 2 then
    return #[1, 2].take n
  let mut ret : Array Nat := .emptyWithCapacity n
  ret := ret.push 1 -- 1st entry should be `triangle 1`
  ret := ret.push 2 -- 2nd entry should be `factorial 2`
  let mut even := 1 -- `triangle 1 = 1`
  let mut odd := 2 -- `factorial 2 = 2`
  for i in 2...<n do
    if i % 2 = 1 then
      odd := odd * i * (i + 1) -- `factorial (i + 1) = factorial (i - 1) * i * i + 1`
      ret := ret.push odd
    else
      even := even + 2 * i + 1 -- `triangle (i + 1) = triangle (i - 1) * i * i + 1`
      ret := ret.push even
  return ret

/-!
### Tests
-/

example : f'' 5 = #[1, 2, 6, 24, 15] := by native_decide
example : f'' 7 = #[1, 2, 6, 24, 15, 720, 28] := by native_decide
example : f'' 1 = #[1] := by native_decide
example : f'' 3 = #[1, 2, 6] := by native_decide

/-!
### Verification
-/

theorem size_f'' {n : Nat} :
    (f'' n).size = n := by
  generalize hwp : f'' n = w
  apply Std.Do.Id.of_wp_run_eq hwp
  mvcgen
  all_goals try infer_instance
  case inv1 => exact ⇓⟨cur, _, _, xs⟩ => ⌜xs.size = cur.prefix.length + 2⌝
  all_goals grind

def lastFactorial (n : Nat) := factorial (n / 2 * 2)
def lastTriangle (n : Nat) := triangle ((n - 1) / 2 * 2 + 1)

@[grind =] theorem lastTriangle_two : lastTriangle 2 = 1 := by decide
@[grind =] theorem lastFactorial_two : lastFactorial 2 = 2 := by decide

@[grind →]
theorem lastTriangle_of_odd (h : n % 2 = 1) : lastTriangle n = triangle n := by
  grind [lastTriangle]

@[grind →]
theorem lastFactorial_of_even (h : n % 2 = 0) : lastFactorial n = factorial n := by
  grind [lastFactorial]

theorem lastTriangle_add_one (h : n % 2 = 1) :
    lastTriangle (n + 1) = lastTriangle n := by
  grind [lastTriangle]

@[grind =]
theorem lastFactorial_add_one_of_odd (h : n % 2 = 1) :
    lastFactorial (n + 1) = lastFactorial n * n * (n + 1) := by
  have : (n + 1) / 2 * 2 = n / 2 * 2 + 2 := by grind
  grind [lastFactorial]

@[grind =]
theorem lastTriangle_add_one_of_odd (h : n % 2 = 1) :
    lastTriangle (n + 1) = lastTriangle n := by
  grind [lastTriangle]

@[grind =]
theorem lastTriangle_add_one_of_even (h : n % 2 = 0) (h' : 0 < n) :
    lastTriangle (n + 1) = lastTriangle n + 2 * n + 1 := by
  have : n / 2 * 2 = (n - 1) / 2 * 2 + 2 := by grind
  grind [lastTriangle]

@[grind =]
theorem lastFactorial_add_one_of_even (h : n % 2 = 0) :
    lastFactorial (n + 1) = lastFactorial n := by
  grind [lastFactorial]

theorem getElem_f'' {n : Nat} {k : Nat} (hlt : k < n) :
    (f'' n)[k]'(by grind [size_f'']) = if k % 2 = 0 then triangle (k + 1) else factorial (k + 1) := by
  rw [Array.getElem_eq_iff]
  generalize hwp : f'' n = w
  apply Std.Do.Id.of_wp_run_eq hwp
  mvcgen
  all_goals try infer_instance
  case inv1 =>
    exact ⇓⟨cur, even, odd, xs⟩ => ⌜xs.size = cur.prefix.length + 2 ∧ odd = lastFactorial xs.size ∧ even = lastTriangle xs.size ∧ ∀ j : Nat, (_ : j < xs.size) →
        (j % 2 = 1 → xs[j] = factorial (j + 1)) ∧ (j % 2 = 0 → xs[j] = triangle (j + 1))⌝
  case vc1 hn => -- verification of the early return
    -- the return value is a prefix of `[1, 2]` and `k` is the index that needs to be verified
    match k with
    | 0 => grind
    | 1 => grind
    | n + 2 => grind
  case vc4 => -- base case of the loop
    grind
  case vc2 hmod h => -- `then` branch
    have := Std.Rco.eq_succMany?_of_toList_eq_append_cons ‹_›
    grind
  case vc3 => -- `else` branch
    have := Std.Rco.eq_succMany?_of_toList_eq_append_cons ‹_›
    grind
  case vc5 => -- postcondition
    grind

end MoreEfficientImpl

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
