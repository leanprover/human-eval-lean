module

import Std.Tactic.Do
-- Sadly, it's apparently impossible to easily prove the size of a
-- `Nat` range without unfolding internal stuff.
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
## Verification
-/

def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => factorial n * (n + 1)

example : factorial 1 = 1 := by decide
example : factorial 3 = 6 := by decide

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
    [SupportsUpperBound su α]
    [LawfulUpwardEnumerableLE α] [HasFiniteRanges su α]
    {r : PRange ⟨.closed, su⟩ α} {i} :
    r.toList[i]? = (UpwardEnumerable.succMany? i r.lower).filter (SupportsUpperBound.IsSatisfied r.upper) := by
  sorry

theorem Std.PRange.succMany?_isSome_of_lt_length_toList [LE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [SupportsUpperBound su α]
    [LawfulUpwardEnumerableLE α] [HasFiniteRanges su α]
    {r : PRange ⟨.closed, su⟩ α} {i} (h : i < r.toList.length) :
    (UpwardEnumerable.succMany? i r.lower).isSome := by
  sorry

theorem Std.PRange.getElem_Rcx_eq [LE α] [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [SupportsUpperBound su α]
    [LawfulUpwardEnumerableLE α] [HasFiniteRanges su α]
    {r : PRange ⟨.closed, su⟩ α} {i h} :
    r.toList[i]'h = (UpwardEnumerable.succMany? i r.lower).get
        (succMany?_isSome_of_lt_length_toList h) := by
  simp [List.getElem_eq_getElem?_get, getElem?_Rcx_eq]

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

abbrev SVal' (σs : List (Type u)) (α : Type u) : Type u := match σs with
  | [] => α
  | σ :: σs => σ → SVal σs α

abbrev SPred' (σs : List (Type u)) : Type u := SVal σs (ULift Prop)

def pure {σs : List (Type u)} (P : Prop) : SPred' σs := match σs with
  | [] => ULift.up P
  | _ :: _ => fun _ => pure P

-- open Std PRange in
-- @[spec]
-- theorem Spec.forIn'_prange {α β : Type u}
--     [Monad m] [WPMonad m ps]
--     [UpwardEnumerable α]
--     [SupportsUpperBound su α] [SupportsLowerBound sl α] [HasFiniteRanges su α]
--     [BoundedUpwardEnumerable sl α] [LawfulUpwardEnumerable α]
--     [LawfulUpwardEnumerableLowerBound sl α] [LawfulUpwardEnumerableUpperBound su α]
--     {xs : PRange ⟨sl, su⟩ α} {init : β} {f : (a : α) → a ∈ xs → β → m (ForInStep β)}
--     (inv : Invariant xs.toList β ps)
--     (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
--       Triple
--         (f cur (by simp [←mem_toList_iff_mem, h]) b)
--         (inv.1 (⟨pref, cur::suff, h.symm⟩, b))
--         (fun r => match r with
--           | .yield b' => inv.1 (⟨pref ++ [cur], suff, by simp [h]⟩, b')
--           | .done b' => inv.1 (⟨xs.toList, [], by simp⟩, b'), inv.2)) :
--     Triple (forIn' xs init f) (inv.1 (⟨[], xs.toList, rfl⟩, init)) (fun b => inv.1 (⟨xs.toList, [], by simp⟩, b), inv.2) := by
--   simp only [forIn'_eq_forIn'_toList]
--   apply Spec.forIn'_list inv step

theorem f_eq_fac {n : Nat} {k : Nat} (hlt : k < n) (hmod : k % 2 = 1) :
    (f n)[k]'(by grind [length_f]) = factorial (k + 1) := by
  rw [List.getElem_eq_iff]
  generalize hwp : f n = w
  apply Std.Do.Id.of_wp_run_eq hwp
  mvcgen
  all_goals try infer_instance
  case inv1 =>
    exact ⇓⟨cur, xs⟩ => ⌜xs.length = cur.prefix.length ∧ ((_ : k < xs.length) → xs[xs.length - 1 - k] = factorial (k + 1))⌝
  case inv2 =>
    -- factorial loop
    exact ⇓⟨cur, x⟩ => ⌜x = factorial cur.prefix.length⌝
  case inv3 =>
    -- sum loop => irrelevant
    exact ⇓⟨cur, xs⟩ => ⌜True⌝
  case vc3 =>
    simp_all [factorial]
    rename_i cur _ _ _ _ pref' cur' suff' h' _ _ _
    have : cur' = (1...=cur).toList[pref'.length]'(by simp [h']) := by simp [h']
    rw [this, Std.PRange.getElem_Rcx_eq]
    simp only [Std.PRange.UpwardEnumerable.succMany?, Option.get_some]
    grind
  case vc4 => simp [factorial]
  case vc5 =>
    simp_all
    intro h
    rename_i pref cur suff _ _ _ _ _ _  h' _
    have : cur = pref.length + 1 := sorry
    obtain ⟨h', h''⟩ := h'
    simp_all
    rw [List.getElem_cons]
    split
    · simp_all
      grind
    · simp_all
      refine Eq.trans ?_ (h'' ?_)
      · grind
      · grind only -- `grind` fails, see #10233
  case vc7 => simp
  case vc8 => simp
  case vc9 =>
    simp_all
    intro h
    rename_i pref cur suff _ _ _ _ _ h''
    have : cur = pref.length + 1 := sorry
    refine Eq.trans ?_ (h''.2 ?_)
    simp_all
    rw [List.getElem_cons]
    · rw [dif_neg (by grind only)]
      grind
    · grind
  case vc10 => simp
  case vc11 =>
    rename_i h
    obtain ⟨h, h'⟩ := h
    simp_all

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
