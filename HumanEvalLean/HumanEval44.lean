module

def changeBase (x : Nat) (base : Nat) : String :=
  String.ofList (Nat.toDigits base x)

example : changeBase 8 3 = "22" := by native_decide
example : changeBase 9 3 = "100" := by native_decide
example : changeBase 234 2 = "11101010" := by native_decide
example : changeBase 16 2 = "10000" := by native_decide
example : changeBase 8 2 = "1000" := by native_decide
example : changeBase 7 2 = "111" := by native_decide

theorem ofDigitChars_changeBase {x : Nat} {base : Nat} (hb' : 1 < base) (hb : base ≤ 10) :
    Nat.ofDigitChars base (changeBase x base).toList 0 = x := by
  simp [changeBase, Nat.ofDigitChars_toDigits hb' hb]

/-!
## Prompt

```python3


def change_base(x: int, base: int):
    """Change numerical base of input number x to base.
    return string representation after the conversion.
    base numbers are less than 10.
    >>> change_base(8, 3)
    '22'
    >>> change_base(8, 2)
    '1000'
    >>> change_base(7, 2)
    '111'
    """
```

## Canonical solution

```python3
    ret = ""
    while x > 0:
        ret = str(x % base) + ret
        x //= base
    return ret
```

## Tests

```python3


METADATA = {}


def check(candidate):
    assert candidate(8, 3) == "22"
    assert candidate(9, 3) == "100"
    assert candidate(234, 2) == "11101010"
    assert candidate(16, 2) == "10000"
    assert candidate(8, 2) == "1000"
    assert candidate(7, 2) == "111"
    for x in range(2, 8):
        assert candidate(x, x + 1) == str(x)

```
-/
