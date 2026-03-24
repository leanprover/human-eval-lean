module

def Char.flipCase (c : Char) : Char :=
  if c.isLower then
    c.toUpper
  else if c.isUpper then
    c.toLower
  else
    c

def flipCase (string : String) : String :=
  string.map Char.flipCase

example : flipCase "" = "" := by cbv
example : flipCase "Hello!" = "hELLO!" := by cbv
example : flipCase "These violent delights have violent ends" = "tHESE VIOLENT DELIGHTS HAVE VIOLENT ENDS" := by cbv

theorem toList_flipCase {string : String} : (flipCase string).toList = string.toList.map Char.flipCase := by
  simp [flipCase]

namespace Char

@[simp]
theorem toNat_mk {val : UInt32} {h} : (Char.mk val h).toNat = val.toNat := by
  simp [← toNat_val]

theorem isUpper_flipCase {c : Char} : c.flipCase.isUpper ↔ c.isLower := by
  grind [flipCase, isUpper, isLower, toUpper, toLower]

theorem isLower_flipCase {c : Char} : c.flipCase.isLower ↔ c.isUpper := by
  grind [flipCase, isUpper, isLower, toUpper, toLower]

theorem toLower_flipCase {c : Char} : c.flipCase.toLower = c.toLower := by
  -- https://github.com/leanprover/lean4/issues/13089
  simp [flipCase, isUpper, isLower, toUpper, toLower, ← toNat_inj, apply_dite Char.toNat,
    apply_ite Char.toNat, UInt32.le_iff_toNat_le]
  grind

end Char


/-!
## Prompt

```python3


def flip_case(string: str) -> str:
    """ For a given string, flip lowercase characters to uppercase and uppercase to lowercase.
    >>> flip_case('Hello')
    'hELLO'
    """
```

## Canonical solution

```python3
    return string.swapcase()
```

## Tests

```python3


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    assert candidate('') == ''
    assert candidate('Hello!') == 'hELLO!'
    assert candidate('These violent delights have violent ends') == 'tHESE VIOLENT DELIGHTS HAVE VIOLENT ENDS'
```
-/
