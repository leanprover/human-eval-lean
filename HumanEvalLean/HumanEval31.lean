module

public import HumanEvalLean.Common.IsPrime

public section

/-! ## Implementation -/

/-- info: isPrime (n : Nat) : Bool -/
#guard_msgs in
#check isPrime

/-! ## Tests -/

example : isPrime 6 = false := by native_decide
example : isPrime 101 = true := by native_decide
example : isPrime 11 = true := by native_decide
example : isPrime 13441 = true := by native_decide
example : isPrime 61 = true := by native_decide
example : isPrime 4 = false := by native_decide
example : isPrime 1 = false := by native_decide
example : isPrime 5 = true := by native_decide
example : isPrime 17 = true := by native_decide
example : isPrime (5 * 17) = false := by native_decide
example : isPrime (11 * 7) = false := by native_decide
example : isPrime (13441 * 19) = false := by native_decide

/-! ## Verification -/

theorem isPrime_spec :
    isPrime n ↔ 2 ≤ n ∧ ∀ d, d ∣ n → d = 1 ∨ d = n := by
  grind [isPrime_eq_true_iff_isPrime, isPrime_iff]

/-!
## Prompt

```python3


def is_prime(n):
    """Return true if a given number is prime, and false otherwise.
    >>> is_prime(6)
    False
    >>> is_prime(101)
    True
    >>> is_prime(11)
    True
    >>> is_prime(13441)
    True
    >>> is_prime(61)
    True
    >>> is_prime(4)
    False
    >>> is_prime(1)
    False
    """
```

## Canonical solution

```python3
    if n < 2:
        return False
    for k in range(2, n - 1):
        if n % k == 0:
            return False
    return True
```

## Tests

```python3


METADATA = {}


def check(candidate):
    assert candidate(6) == False
    assert candidate(101) == True
    assert candidate(11) == True
    assert candidate(13441) == True
    assert candidate(61) == True
    assert candidate(4) == False
    assert candidate(1) == False
    assert candidate(5) == True
    assert candidate(11) == True
    assert candidate(17) == True
    assert candidate(5 * 17) == False
    assert candidate(11 * 7) == False
    assert candidate(13441 * 19) == False

```
-/
