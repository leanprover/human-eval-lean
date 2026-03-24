module
import Std

def fizzBuzz (n : Nat) : Nat :=
  (0...n).iter
    |>.filter (fun i => i % 11 == 0 || i % 13 == 0)
    |>.map (fun i => i.repr.chars.filter (· == '7') |>.length)
    |>.fold (init := 0) (· + ·)

example : fizzBuzz 50 = 0 := by native_decide
example : fizzBuzz 78 = 2 := by native_decide
example : fizzBuzz 79 = 3 := by native_decide
example : fizzBuzz 100 = 3 := by native_decide
example : fizzBuzz 200 = 6 := by native_decide
example : fizzBuzz 4000 = 192 := by native_decide
example : fizzBuzz 10000 = 639 := by native_decide
example : fizzBuzz 100000 = 8026 := by native_decide

def count7s (n : Nat) : Nat :=
  let last := if n % 10 = 7 then 1 else 0
  if n < 10 then last else count7s (n / 10) + last

theorem count7s_eq {n : Nat} : count7s n = ((Nat.toDigits 10 n).filter (· == '7')).length := by
  fun_induction count7s with
  | case1 n l h =>
    subst l
    simp only [Nat.mod_eq_of_lt h, dite_eq_ite, ↓Char.isValue, Nat.toDigits_of_lt_base h,
      List.filter_cons, beq_iff_eq, Nat.digitChar_eq_seven, List.filter_nil]
    split <;> simp
  | case2 n l h ih =>
    subst l
    simp only [ih, ↓Char.isValue, dite_eq_ite]
    conv => rhs; rw [← Nat.div_add_mod (m := n) (n := 10)]
    rw [← Nat.toDigits_append_toDigits (by decide) (by simp; omega) (Nat.mod_lt _ (by decide))]
    simp [Nat.toDigits_of_lt_base (Nat.mod_lt _ (y := 10) (by decide)), List.filter_cons,
      apply_ite List.length]

theorem fizzBuzz_eq {n : Nat} :
    fizzBuzz n = (((0...n).toList.filter (fun i => i % 11 == 0 || i % 13 == 0)).map count7s).sum := by
  simp only [fizzBuzz, ne_eq, ↓Char.isValue, ← Std.Iter.foldl_toList, Std.Iter.toList_map,
    Std.Iter.toList_filter, Std.Rco.toList_iter, List.sum_eq_foldl]
  congr
  ext n
  simp [count7s_eq, ← Std.Iter.length_toList_eq_length]


/-!
## Prompt

```python3


def fizz_buzz(n: int):
    """Return the number of times the digit 7 appears in integers less than n which are divisible by 11 or 13.
    >>> fizz_buzz(50)
    0
    >>> fizz_buzz(78)
    2
    >>> fizz_buzz(79)
    3
    """
```

## Canonical solution

```python3
    ns = []
    for i in range(n):
        if i % 11 == 0 or i % 13 == 0:
            ns.append(i)
    s = ''.join(list(map(str, ns)))
    ans = 0
    for c in s:
        ans += (c == '7')
    return ans
```

## Tests

```python3


METADATA = {}


def check(candidate):
    assert candidate(50) == 0
    assert candidate(78) == 2
    assert candidate(79) == 3
    assert candidate(100) == 3
    assert candidate(200) == 6
    assert candidate(4000) == 192
    assert candidate(10000) == 639
    assert candidate(100000) == 8026

```
-/
