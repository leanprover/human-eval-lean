module
import Std

open Std

def isPalindrome (s : String) : Bool :=
  s.chars.zip s.revChars |>.all (fun p => p.1 == p.2)

example : isPalindrome "" = true := by cbv
example : isPalindrome "aba" = true := by cbv
example : isPalindrome "aaaaa" = true := by cbv
example : isPalindrome "zbcd" = false := by cbv
example : isPalindrome "xywyx" = true := by cbv
example : isPalindrome "xywyz" = false := by cbv
example : isPalindrome "xywxz" = false := by cbv

theorem isPalindome_iff {s : String} : isPalindrome s ↔ s.toList = s.toList.reverse := by
  simp [isPalindrome, ← Iter.all_toList, List.mem_iff_getElem, List.ext_getElem_iff]
  grind

/-!
## Prompt

```python3


def is_palindrome(text: str):
    """
    Checks if given string is a palindrome
    >>> is_palindrome('')
    True
    >>> is_palindrome('aba')
    True
    >>> is_palindrome('aaaaa')
    True
    >>> is_palindrome('zbcd')
    False
    """
```

## Canonical solution

```python3
    for i in range(len(text)):
        if text[i] != text[len(text) - 1 - i]:
            return False
    return True
```

## Tests

```python3


METADATA = {}


def check(candidate):
    assert candidate('') == True
    assert candidate('aba') == True
    assert candidate('aaaaa') == True
    assert candidate('zbcd') == False
    assert candidate('xywyx') == True
    assert candidate('xywyz') == False
    assert candidate('xywzx') == False

```
-/
