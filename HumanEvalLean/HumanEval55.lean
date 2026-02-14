module

public import Std
open Std

-- public section -- #12482

/-!
## Implementation

Iterator-based Fibonacci implementation.

The Fibonacci sequence is computed using an iterator that maintains a state `(fₙ, fₙ₊₁)`.
Each step transforms the state to `(fₙ₊₁, fₙ + fₙ₊₁)`, starting from `(0, 1)`.
-/

@[inline]
def fibonacciIterator.step : Nat × Nat → Nat × Nat
  | (x₁, x₂) => (x₂, x₁ + x₂)

@[inline]
def fibonacciIterator.states := Iter.repeat (init := (0, 1)) fibonacciIterator.step

def fibonacciIterator := fibonacciIterator.states.map (fun (current, _) => current)

def fib (n : Nat) : Nat :=
  fibonacciIterator.atIdxSlow? n |>.get!

/-! ## Tests -/

example : fib 10 = 55 := by native_decide
example : fib 1 = 1 := by native_decide
example : fib 8 = 21 := by native_decide
example : fib 11 = 89 := by native_decide
example : fib 12 = 144 := by native_decide

/-! ## Missing API -/

theorem Nat.eq_add_of_toList_rcc_eq_append_cons {a b : Nat} {pref cur suff}
    (h : (a...=b).toList = pref ++ cur :: suff) :
    cur = a + pref.length := by
  have := Rcc.eq_succMany?_of_toList_eq_append_cons h
  grind [PRange.Nat.succMany?_eq]

@[grind =]
theorem Std.Iter.atIdxSlow?_map [Iterator α Id β] [Iterators.Productive α Id]
    {it : Iter (α := α) β} {f : β → γ} :
    (it.map f).atIdxSlow? n = (it.atIdxSlow? n).map f := by
  induction n, it using atIdxSlow?.induct_unfolding
  all_goals
    rw [atIdxSlow?_eq_match, step_map]
    simp [*]

attribute [grind =] Iter.atIdxSlow?_repeat

theorem Std.Iter.length_take_repeat {f : α → α} {init} :
    (Iter.repeat (init := init) f |>.take n).length = n := by
  induction n generalizing init <;>
    grind [=_ Iter.length_toList_eq_length, Iter.toList_take_zero, Iter.toList_take_repeat_succ]

theorem Std.Iter.toList_take_map [Iterator α Id β] [Iterators.Productive α Id]
    {it : Iter (α := α) β} {f : β → γ} :
    (it.map f |>.take n).toList = (it.take n).toList.map f := by
  apply List.ext_getElem?
  grind [Iter.getElem?_toList_eq_atIdxSlow?, Iter.atIdxSlow?_take]

attribute [grind =] Iter.atIdxSlow?_take Iter.toList_take_map Iter.length_map
  Iter.length_toList_eq_length Iter.length_take_repeat

/-! ## Verification of `tri` -/

def fibState (n : Nat) :=
  (fibonacciIterator.states.atIdxSlow? n).get (by grind [fibonacciIterator.states])

theorem fib_eq_fst_fibState :
    fib n = (fibState n).1 := by
  grind [fib, fibState, fibonacciIterator, fibonacciIterator.states]

theorem fibState_spec :
    fibState n =
      if n = 0 then
        (0, 1)
      else if n = 1 then
        (1, 1)
      else
        (fib (n - 2) + fib (n - 1), fib (n + 1)) := by
  simp only [fib, fibState, fibonacciIterator, fibonacciIterator.states]
  induction n using Nat.strongRecOn with | ind n ih
  match n with
  | 0 | 1 | n + 2 => grind [Nat.repeat, fibonacciIterator.step]

theorem fib_spec:
    fib n =
      if n = 0 then
        0
      else if n = 1 then
        1
      else
        fib (n - 2) + fib (n - 1) := by
  grind [fibState_spec, fib_eq_fst_fibState]

/-!
## Prompt

```python3


def fib(n: int):
    """Return n-th Fibonacci number.
    >>> fib(10)
    55
    >>> fib(1)
    1
    >>> fib(8)
    21
    """
```

## Canonical solution

```python3
    if n == 0:
        return 0
    if n == 1:
        return 1
    return fib(n - 1) + fib(n - 2)
```

## Tests

```python3


METADATA = {}


def check(candidate):
    assert candidate(10) == 55
    assert candidate(1) == 1
    assert candidate(8) == 21
    assert candidate(11) == 89
    assert candidate(12) == 144

```
-/
