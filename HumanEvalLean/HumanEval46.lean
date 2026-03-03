module

public import Std
open Std Std.Do

set_option mvcgen.warning false

/-! ## Implementation -/

def fib4 (n : Nat) : Nat := Id.run do
  let mut lastFour : Vector Nat 4 := #v[0, 0, 2, 0]
  for i in *...(n - 3) do
    lastFour := lastFour.set (i % 4) (lastFour[0] + lastFour[1] + lastFour[2] + lastFour[3])
  return lastFour[n % 4]

/-! ## Tests -/

example : fib4 5 = 4 := by native_decide
example : fib4 8 = 28 := by native_decide
example : fib4 10 = 104 := by native_decide
example : fib4 12 = 386 := by native_decide

/-! ## Missing API -/

theorem eq_getElem_append_cons {pref suff : List α} {cur : α} :
    (pref ++ cur :: suff)[pref.length]? = cur := by
  simp

grind_pattern eq_getElem_append_cons => pref ++ cur :: suff
attribute [grind =] Nat.getElem?_toList_rio
attribute [grind =] Nat.length_toList_rio

/-! ## Verification -/

def fib4Reference : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 2
  | 3 => 0
  | (k + 4) =>
    fib4Reference (k + 4 - 1) + fib4Reference (k + 4 - 2) + fib4Reference (k + 4 - 3) + fib4Reference (k + 4 - 4)

theorem sum_mod_eq_sum {vec : Vector Nat 4} :
    ∀ i, vec[i % 4] + vec[(i + 1) % 4] + vec[(i + 2) % 4] + vec[(i + 3) % 4] =
        vec[0] + vec[1] + vec[2] + vec[3]
  | 0 | 1 | 2 | 3 => by grind
  | i + 4 => by
    have := sum_mod_eq_sum (vec := vec) (i := i)
    have : ∀ j, j < 4 → (i + 4 + j) % 4 = (i + j) % 4 := by grind
    simp only [Nat.add_mod_right, Nat.reduceLT, this, Nat.lt_add_one]
    grind

theorem fib4_eq_fib4Reference :
    fib4 n = fib4Reference n := by
  generalize hwp : fib4 n = wp
  apply Id.of_wp_run_eq hwp
  mvcgen
  invariants
  · ⇓⟨cur, lastFour⟩ => ⌜∀ i, i < 4 → lastFour[(cur.pos + i) % 4] = fib4Reference (cur.pos + i)⌝
  case vc1 pref cur suff heq _ _ h =>
    simp_all only [List.Cursor.pos_mk, List.length_append, List.length_cons, List.length_nil]
    intro i hi
    by_cases i = 3
    · rename_i hi'
      rw [hi', fib4Reference]
      simp only [show (pref.length + 1 + 3) % 4 = cur % 4 by grind]
      grind [sum_mod_eq_sum, h 0 (by grind), h 1 (by grind), h 2 (by grind), h 3 (by grind),
        Vector.getElem_set_self]
    · specialize h (i + 1) (by grind)
      grind
  case vc2 =>
    simp only [List.Cursor.pos_mk, Vector.getElem_eq_iff]
    decide
  case vc3 h =>
    by_cases hn : n < 4
    · grind
    · specialize h 3
      grind

/-!
## Prompt

```python3


def fib4(n: int):
    """The Fib4 number sequence is a sequence similar to the Fibbonacci sequnece that's defined as follows:
    fib4(0) -> 0
    fib4(1) -> 0
    fib4(2) -> 2
    fib4(3) -> 0
    fib4(n) -> fib4(n-1) + fib4(n-2) + fib4(n-3) + fib4(n-4).
    Please write a function to efficiently compute the n-th element of the fib4 number sequence.  Do not use recursion.
    >>> fib4(5)
    4
    >>> fib4(6)
    8
    >>> fib4(7)
    14
    """
```

## Canonical solution

```python3
    results = [0, 0, 2, 0]
    if n < 4:
        return results[n]

    for _ in range(4, n + 1):
        results.append(results[-1] + results[-2] + results[-3] + results[-4])
        results.pop(0)

    return results[-1]
```

## Tests

```python3


METADATA = {}


def check(candidate):
    assert candidate(5) == 4
    assert candidate(8) == 28
    assert candidate(10) == 104
    assert candidate(12) == 386

```
-/
