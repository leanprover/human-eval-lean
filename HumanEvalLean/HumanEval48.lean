module

def is_palindrome : Unit :=
  ()

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