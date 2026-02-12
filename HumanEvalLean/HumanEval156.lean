module

/-- Table lookup version per Wikipedia. This essentially defines what Roman numerals are. -/
def intToMiniRoman (n : Nat) (hn' : n ≤ 1000 := by decide) : String :=
  ["", "m"][n / 1000]'(by grind) ++
  ["", "c", "cc", "ccc", "cd", "d", "dc", "dcc", "dccc", "cm"][(n / 100) % 10]'(by simp; grind) ++
  ["", "x", "xx", "xxx", "xl", "l", "lx", "lxx", "lxxx", "xc"][(n / 10) % 10]'(by simp; grind) ++
  ["", "i", "ii", "iii", "iv", "v", "vi", "vii", "viii", "ix"][n % 10]'(by simp; grind)

/-- Greedy algorithm as given by model solution. -/
def intToMiniRoman2 (n : Nat) : String := Id.run do
  let pairs := [("m", 1000), ("cm", 900), ("d", 500), ("cd", 400), ("c", 100), ("xc", 90),
    ("l", 50), ("xl", 40), ("x", 10), ("ix", 9), ("v", 5), ("iv", 4), ("i", 1)]
  let mut num := n
  let mut s := ""
  for ⟨t, v⟩ in pairs do
    s := (num / v).repeat (· ++ t) s
    num := num % v
  return s

example : intToMiniRoman2 19 = "xix" := rfl
example : intToMiniRoman2 152 = "clii" := rfl
example : intToMiniRoman2 251 = "ccli" := rfl
example : intToMiniRoman2 426 = "cdxxvi" := rfl
example : intToMiniRoman2 500 = "d" := rfl
example : intToMiniRoman2 1 = "i" := rfl
example : intToMiniRoman2 4 = "iv" := rfl
example : intToMiniRoman2 43 = "xliii" := rfl
example : intToMiniRoman2 90 = "xc" := rfl
example : intToMiniRoman2 94 = "xciv" := rfl
example : intToMiniRoman2 532 = "dxxxii" := rfl
example : intToMiniRoman2 900 = "cm" := rfl
example : intToMiniRoman2 994 = "cmxciv" := rfl
example : intToMiniRoman2 1000 = "m" := rfl

/-- Show that the two implementations coincide by brute force. -/
theorem eq : ∀ n, (h : n ≤ 1000) → intToMiniRoman n h = intToMiniRoman2 n := by
  decide +kernel

/-!
## Prompt

```python3

def int_to_mini_roman(number):
    """
    Given a positive integer, obtain its roman numeral equivalent as a string,
    and return it in lowercase.
    Restrictions: 1 <= num <= 1000

    Examples:
    >>> int_to_mini_roman(19) == 'xix'
    >>> int_to_mini_roman(152) == 'clii'
    >>> int_to_mini_roman(426) == 'cdxxvi'
    """
```

## Canonical solution

```python3
    num = [1, 4, 5, 9, 10, 40, 50, 90,
           100, 400, 500, 900, 1000]
    sym = ["I", "IV", "V", "IX", "X", "XL",
           "L", "XC", "C", "CD", "D", "CM", "M"]
    i = 12
    res = ''
    while number:
        div = number // num[i]
        number %= num[i]
        while div:
            res += sym[i]
            div -= 1
        i -= 1
    return res.lower()
```

## Tests

```python3
def check(candidate):

    # Check some simple cases
    assert candidate(19) == 'xix'
    assert candidate(152) == 'clii'
    assert candidate(251) == 'ccli'
    assert candidate(426) == 'cdxxvi'
    assert candidate(500) == 'd'
    assert candidate(1) == 'i'
    assert candidate(4) == 'iv'
    assert candidate(43) == 'xliii'
    assert candidate(90) == 'xc'
    assert candidate(94) == 'xciv'
    assert candidate(532) == 'dxxxii'
    assert candidate(900) == 'cm'
    assert candidate(994) == 'cmxciv'
    assert candidate(1000) == 'm'

    # Check some edge cases that are easy to work out by hand.
    assert True

```
-/
