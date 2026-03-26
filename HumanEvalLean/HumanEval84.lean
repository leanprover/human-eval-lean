module

def solve (n : Nat) : String :=
  String.ofList (Nat.toDigits 2 (n.repr.chars.map (fun c => c.toNat - '0'.toNat) |>.fold (init := 0) (· + ·)))

example : solve 1000 = "1" := by native_decide
example : solve 150 = "110" := by native_decide
example : solve 147 = "1100" := by native_decide
example : solve 333 = "1001" := by native_decide
example : solve 963 = "10010" := by native_decide

theorem ofDigitChars_solve {n : Nat} :
    Nat.ofDigitChars 2 (solve n).toList 0 = (n.repr.toList.map (fun c => c.toNat - '0'.toNat)).sum := by
  rw [solve, String.toList_ofList, Nat.ofDigitChars_toDigits (by simp) (by simp),
    ← Std.Iter.foldl_toList, Std.Iter.toList_map]
  simp [List.sum_eq_foldl]

/-!
## Prompt

```python3

def solve(N):
    """Given a positive integer N, return the total sum of its digits in binary.

    Example
        For N = 1000, the sum of digits will be 1 the output should be "1".
        For N = 150, the sum of digits will be 6 the output should be "110".
        For N = 147, the sum of digits will be 12 the output should be "1100".

    Variables:
        @N integer
             Constraints: 0 ≤ N ≤ 10000.
    Output:
         a string of binary number
    """
```

## Canonical solution

```python3
    return bin(sum(int(i) for i in str(N)))[2:]
```

## Tests

```python3
def check(candidate):

    # Check some simple cases
    assert True, "This prints if this assert fails 1 (good for debugging!)"
    assert candidate(1000) == "1", "Error"
    assert candidate(150) == "110", "Error"
    assert candidate(147) == "1100", "Error"

    # Check some edge cases that are easy to work out by hand.
    assert True, "This prints if this assert fails 2 (also good for debugging!)"
    assert candidate(333) == "1001", "Error"
    assert candidate(963) == "10010", "Error"

```
-/
