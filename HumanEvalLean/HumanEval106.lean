module

import Std.Tactic.Do
-- Sadly, it's apparently currently impossible to easily prove the size of a
-- `Nat` range without unfolding internal stuff. This should be fixed in the standard library.
import all Init.Data.Iterators.Consumers.Loop

open Std.Do

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
## Tests
-/

example : f 5 = [1, 2, 6, 24, 15] := by native_decide
example : f 7 = [1, 2, 6, 24, 15, 720, 28] := by native_decide
example : f 1 = [1] := by native_decide
example : f 3 = [1, 2, 6] := by native_decide

/-!
## Standard library wishlist

The following lemmas halp with the verification and would be nice to have in the standard library.
-/

@[simp]
theorem Std.PRange.length_toList_eq_size [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [SupportsLowerBound sl α] [SupportsUpperBound su α] [BoundedUpwardEnumerable sl α]
    [HasFiniteRanges su α] [RangeSize su α] [LawfulRangeSize su α]
    {r : PRange ⟨sl, su⟩ α} :
    r.toList.length = r.size := by
  simp [PRange.toList, PRange.size]

@[simp]
theorem Nat.size_Rco {a b : Nat} :
    (a...b).size = b - a := by
  simp [Std.PRange.size, Std.Iterators.Iter.size, Std.Iterators.IteratorSize.size,
    Std.PRange.Internal.iter, Std.Iterators.Iter.toIterM, Std.PRange.RangeSize.size]

@[simp]
theorem Nat.size_Rcc {a b : Nat} :
    (a...=b).size = b + 1- a := by
  simp [Std.PRange.size, Std.Iterators.Iter.size, Std.Iterators.IteratorSize.size,
    Std.PRange.Internal.iter, Std.Iterators.Iter.toIterM, Std.PRange.RangeSize.size]

theorem Std.PRange.getElem?_Rcx_eq [LE α] [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [SupportsUpperBound su α] [LawfulUpwardEnumerableUpperBound su α]
    [LawfulUpwardEnumerableLE α] [HasFiniteRanges su α]
    {r : PRange ⟨.closed, su⟩ α} {i} :
    r.toList[i]? = (UpwardEnumerable.succMany? i r.lower).filter (SupportsUpperBound.IsSatisfied r.upper) := by
  induction i generalizing r
  · rw [PRange.toList_eq_match, UpwardEnumerable.succMany?_zero]
    simp only [Option.filter_some, decide_eq_true_eq]
    split <;> simp
  · rename_i n ih
    rw [PRange.toList_eq_match]
    simp only
    split
    · simp [LawfulUpwardEnumerable.succMany?_succ_eq_succ?_bind_succMany?]
      cases hs : UpwardEnumerable.succ? r.lower
      · rw [PRange.toList_eq_match]
        simp [BoundedUpwardEnumerable.init?, hs]
      · rw [toList_open_eq_toList_closed_of_isSome_succ? (by grind)]
        rw [ih]
        simp [hs]
    · simp only [List.length_nil, Nat.not_lt_zero, not_false_eq_true, getElem?_neg]
      cases hs : UpwardEnumerable.succMany? (n + 1) r.lower
      · grind
      · rename_i hl a
        simp only [Option.filter_some, decide_eq_true_eq, right_eq_ite_iff]
        have : UpwardEnumerable.LE r.lower a := ⟨n + 1, hs⟩
        intro ha
        exact hl.elim <| LawfulUpwardEnumerableUpperBound.isSatisfied_of_le r.upper _ _ ha this (α := α)

theorem Std.PRange.isSome_succMany?_of_lt_length_toList [LE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [SupportsUpperBound su α] [LawfulUpwardEnumerableUpperBound su α]
    [LawfulUpwardEnumerableLE α] [HasFiniteRanges su α]
    {r : PRange ⟨.closed, su⟩ α} {i} (h : i < r.toList.length) :
    (UpwardEnumerable.succMany? i r.lower).isSome := by
  have : r.toList[i]?.isSome := by grind
  simp only [getElem?_Rcx_eq, Option.isSome_filter] at this
  exact Option.isSome_of_any this

theorem Std.PRange.getElem_Rcx_eq [LE α] [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [SupportsUpperBound su α] [LawfulUpwardEnumerableUpperBound su α]
    [LawfulUpwardEnumerableLE α] [HasFiniteRanges su α]
    {r : PRange ⟨.closed, su⟩ α} {i h} :
    r.toList[i]'h = (UpwardEnumerable.succMany? i r.lower).get
        (isSome_succMany?_of_lt_length_toList h) := by
  simp [List.getElem_eq_getElem?_get, getElem?_Rcx_eq]

theorem Std.PRange.eq_succMany?_of_toList_Rcx_eq_append_cons [LE α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [SupportsUpperBound su α] [HasFiniteRanges su α] [LawfulUpwardEnumerableUpperBound su α]
    {r : PRange ⟨.closed, su⟩ α} {pref suff : List α} {cur : α} (h : r.toList = pref ++ cur :: suff) :
    cur = (UpwardEnumerable.succMany? pref.length r.lower).get
        (isSome_succMany?_of_lt_length_toList (by grind)) := by
  have : cur = (pref ++ cur :: suff)[pref.length] := by grind
  simp only [← h] at this
  simp [this, getElem_Rcx_eq]

/-!
## Verification
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
  case inv1 =>
    exact ⇓⟨cur, xs⟩ => ⌜xs.length = cur.prefix.length⌝
  case inv2 =>
    -- factorial loop
    exact ⇓⟨cur, xs⟩ => ⌜True⌝
  case inv3 =>
    -- sum loop
    exact ⇓⟨cur, xs⟩ => ⌜True⌝
  all_goals simp_all -- relies on `Nat.size_Rcc`

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
  case vc10 => simp -- base case
  case vc11 => -- postcondition
    rename_i h
    obtain ⟨h, h'⟩ := h
    simp_all

  -- FACTORIAL LOOP
  case inv2 => exact ⇓⟨cur, x⟩ => ⌜x = factorial cur.prefix.length⌝
  case vc4 => simp [factorial] -- base case
  case vc5 => -- postcondition
    simp_all only [Std.PRange.eq_succMany?_of_toList_Rcx_eq_append_cons ‹_›,
      Std.PRange.UpwardEnumerable.succMany?, SPred.down_pure,
      Std.PRange.length_toList_eq_size, Nat.size_Rcc, List.length_cons,
      List.length_append, List.length_nil, true_and, List.getElem_cons]
    split
    · simp_all only [SPred.down_pure, Std.PRange.length_toList_eq_size, Nat.size_Rcc]
      grind
    · rename_i h' _ _
      refine fun _ =>
        Eq.trans ?_ (h'.2 ?_) <;> grind only -- `grind` without `only` fails, see #10233
  case vc3.step => -- step
    have := Std.PRange.eq_succMany?_of_toList_Rcx_eq_append_cons ‹_›
    simp_all only [factorial, SPred.down_pure, Std.PRange.UpwardEnumerable.succMany?,
      Option.get_some]
    grind [factorial]

  -- SUM LOOP
  case inv3 => exact ⇓⟨cur, x⟩ => ⌜x = triangle cur.prefix.length⌝
  case vc8 => simp [triangle] -- base case
  case vc9 => -- postcondition
    simp_all only [Std.PRange.eq_succMany?_of_toList_Rcx_eq_append_cons ‹_›,
      Std.PRange.UpwardEnumerable.succMany?, SPred.down_pure,
      Std.PRange.length_toList_eq_size, Nat.size_Rcc, List.length_cons,
      List.length_append, List.length_nil, true_and, List.getElem_cons]
    split
    · simp_all only [SPred.down_pure, Std.PRange.length_toList_eq_size, Nat.size_Rcc]
      grind
    · rename_i h' _ _
      refine fun _ =>
        Eq.trans ?_ (h'.2 ?_) <;> grind only -- `grind` without `only` fails, see #10233
  case vc7.step => -- step
    have := Std.PRange.eq_succMany?_of_toList_Rcx_eq_append_cons ‹_›
    simp_all only [factorial, SPred.down_pure, Std.PRange.UpwardEnumerable.succMany?,
      Option.get_some]
    grind [triangle]

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
