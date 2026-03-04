module

public import Std
open Std Std.Do

set_option mvcgen.warning false

/-!
## Implementation

(See also problem 46.)
-/

def fibfib (n : Nat) : Nat := Id.run do
  let mut lastThree : Vector Nat 3 := #v[0, 0, 1]
  for i in *...(n - 2) do
    lastThree := lastThree.set (i % 3) (lastThree[0] + lastThree[1] + lastThree[2])
  return lastThree[n % 3]

/-! ## Tests -/

example : fibfib 2 = 1 := by native_decide
example : fibfib 1 = 0 := by native_decide
example : fibfib 5 = 4 := by native_decide
example : fibfib 8 = 24 := by native_decide
example : fibfib 10 = 81 := by native_decide
example : fibfib 12 = 274 := by native_decide
example : fibfib 14 = 927 := by native_decide

/-! ## Missing API -/

theorem eq_getElem_append_cons {pref suff : List α} {cur : α} :
    (pref ++ cur :: suff)[pref.length]? = cur := by
  simp

grind_pattern eq_getElem_append_cons => pref ++ cur :: suff
attribute [grind =] Nat.getElem?_toList_rio
attribute [grind =] Nat.length_toList_rio

/-! ## Verification -/

def fibfibReference : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | k + 3 =>
    fibfibReference (k + 2) + fibfibReference (k + 1) + fibfibReference k

theorem sum_mod_eq_sum {vec : Vector Nat 3} :
    ∀ i, vec[i % 3] + vec[(i + 1) % 3] + vec[(i + 2) % 3] =
        vec[0] + vec[1] + vec[2]
  | 0 | 1 | 2 => by grind
  | i + 3 => by
    have := sum_mod_eq_sum (vec := vec) (i := i)
    simp only [Nat.add_mod_right]
    grind

theorem fibfib_eq_fibfibReference :
    fibfib n = fibfibReference n := by
  generalize hwp : fibfib n = wp
  apply Id.of_wp_run_eq hwp
  mvcgen
  invariants
  · ⇓⟨cur, lastThree⟩ => ⌜∀ i, i < 3 → lastThree[(cur.pos + i) % 3] = fibfibReference (cur.pos + i)⌝
  case vc1 pref cur suff heq _ _ h =>
    simp_all only [List.Cursor.pos_mk, List.length_append, List.length_cons, List.length_nil]
    intro i hi
    by_cases i = 2
    · rename_i hi'
      rw [hi', fibfibReference]
      simp only [show (pref.length + 1 + 2) % 3 = cur % 3 by grind]
      grind [sum_mod_eq_sum, h 0 (by grind), h 1 (by grind), h 2 (by grind),
        Vector.getElem_set_self]
    · specialize h (i + 1) (by grind)
      grind
  case vc2 =>
    simp only [List.Cursor.pos_mk, Vector.getElem_eq_iff]
    decide
  case vc3 h =>
    by_cases hn : n < 3
    · grind
    · specialize h 2 (by grind)
      grind

/-!
## Prompt

```python3


def fibfib(n: int):
    """The FibFib number sequence is a sequence similar to the Fibbonacci sequnece that's defined as follows:
    fibfib(0) == 0
    fibfib(1) == 0
    fibfib(2) == 1
    fibfib(n) == fibfib(n-1) + fibfib(n-2) + fibfib(n-3).
    Please write a function to efficiently compute the n-th element of the fibfib number sequence.
    >>> fibfib(1)
    0
    >>> fibfib(5)
    4
    >>> fibfib(8)
    24
    """
```

## Canonical solution

```python3
    if n == 0:
        return 0
    if n == 1:
        return 0
    if n == 2:
        return 1
    return fibfib(n - 1) + fibfib(n - 2) + fibfib(n - 3)
```

## Tests

```python3


METADATA = {}


def check(candidate):
    assert candidate(2) == 1
    assert candidate(1) == 0
    assert candidate(5) == 4
    assert candidate(8) == 24
    assert candidate(10) == 81
    assert candidate(12) == 274
    assert candidate(14) == 927

```
-/
