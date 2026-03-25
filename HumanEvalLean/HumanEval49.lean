module

public section

/-! ## Implementation -/

def modp (n p : Nat) : Nat :=
  Nat.repeat (fun x => (2 * x) % p) n 1

/-! ## Tests -/

example : modp 3 5 = 3 := by cbv
example : modp 1101 101 = 2 := by native_decide -- `cbv` reaches resource limits
example : modp 0 101 = 1 := by cbv
example : modp 3 11 = 8 := by cbv
example : modp 100 101 = 1 := by cbv
example : modp 30 5 = 4 := by cbv
example : modp 31 5 = 3 := by cbv

/-! ## Verification -/

theorem modp_eq (h : 1 < p) :
    modp n p = (2 ^ n) % p := by
  induction n
  · obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_lt h
    simp [modp, Nat.repeat, Nat.add_comm 1]
  · simp only [modp] at *
    simp only [Nat.repeat, Nat.pow_add_one, *]
    rw [Nat.mul_mod, Nat.mul_mod]
    simp [Nat.mul_comm]

/-!
## Prompt

```python3


def modp(n: int, p: int):
    """Return 2^n modulo p (be aware of numerics).
    >>> modp(3, 5)
    3
    >>> modp(1101, 101)
    2
    >>> modp(0, 101)
    1
    >>> modp(3, 11)
    8
    >>> modp(100, 101)
    1
    """
```

## Canonical solution

```python3
    ret = 1
    for i in range(n):
        ret = (2 * ret) % p
    return ret
```

## Tests

```python3


METADATA = {}


def check(candidate):
    assert candidate(3, 5) == 3
    assert candidate(1101, 101) == 2
    assert candidate(0, 101) == 1
    assert candidate(3, 11) == 8
    assert candidate(100, 101) == 1
    assert candidate(30, 5) == 4
    assert candidate(31, 5) == 3

```
-/
