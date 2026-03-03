module

set_option cbv.warning false

/-!
## Implementation

Lean supports addition out of the box, so we just reference to it and to the lemmas verifying its
behavior.
-/

/-- info: Nat.add : Nat → Nat → Nat -/
#guard_msgs in
#check Nat.add

/-! ## Tests -/

example : Nat.add 0 1 = 1 := by cbv
example : Nat.add 1 0 = 1 := by cbv
example : Nat.add 2 3 = 5 := by cbv
example : Nat.add 5 7 = 12 := by cbv
example : Nat.add 7 5 = 12 := by cbv

/-! ## Verification -/

/-- info: Nat.add_zero (n : Nat) : n + 0 = n -/
#guard_msgs in
#check Nat.add_zero

/-- info: Nat.zero_add (n : Nat) : 0 + n = n -/
#guard_msgs in
#check Nat.zero_add

/-- info: Nat.add_assoc (n m k : Nat) : n + m + k = n + (m + k) -/
#guard_msgs in
#check Nat.add_assoc

/-- info: Nat.add_comm (n m : Nat) : n + m = m + n -/
#guard_msgs in
#check Nat.add_comm

/-!
## Prompt

```python3


def add(x: int, y: int):
    """Add two numbers x and y
    >>> add(2, 3)
    5
    >>> add(5, 7)
    12
    """
```

## Canonical solution

```python3
    return x + y
```

## Tests

```python3


METADATA = {}


def check(candidate):
    import random

    assert candidate(0, 1) == 1
    assert candidate(1, 0) == 1
    assert candidate(2, 3) == 5
    assert candidate(5, 7) == 12
    assert candidate(7, 5) == 12

    for i in range(100):
        x, y = random.randint(0, 1000), random.randint(0, 1000)
        assert candidate(x, y) == x + y

```
-/
