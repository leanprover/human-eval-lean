module

def filterBySubstring (strings : Array String) (substring : String) : Array String :=
  strings.filter (·.contains substring)

example : filterBySubstring #[] "john" = #[] := by native_decide
example : filterBySubstring #["xxx", "asd", "xxy", "john doe", "xxxAAA", "xxx"] "xxx" = #["xxx", "xxxAAA", "xxx"] := by native_decide
example : filterBySubstring #["xxx", "asd", "aaaxxy", "john doe", "xxxAAA", "xxx"] "xx" = #["xxx", "aaaxxy", "xxxAAA", "xxx"] := by native_decide
example : filterBySubstring #["grunt", "trumpet", "prune", "gruesome"] "run" = #["grunt", "prune"] := by native_decide

@[simp]
theorem String.contains_string_iff_infix {s t : String} : s.contains t ↔ t.toList <:+: s.toList := sorry

open Classical in
theorem filterBySubstring_eq {strings : Array String} {substring : String} :
    filterBySubstring strings substring = strings.filter (decide <| substring.toList <:+: ·.toList) := by
  rw [filterBySubstring]
  congr
  ext
  exact Bool.eq_iff_iff.2 (by simp)

/-!
## Prompt

```python3
from typing import List


def filter_by_substring(strings: List[str], substring: str) -> List[str]:
    """ Filter an input list of strings only for ones that contain given substring
    >>> filter_by_substring([], 'a')
    []
    >>> filter_by_substring(['abc', 'bacd', 'cde', 'array'], 'a')
    ['abc', 'bacd', 'array']
    """
```

## Canonical solution

```python3
    return [x for x in strings if substring in x]
```

## Tests

```python3


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    assert candidate([], 'john') == []
    assert candidate(['xxx', 'asd', 'xxy', 'john doe', 'xxxAAA', 'xxx'], 'xxx') == ['xxx', 'xxxAAA', 'xxx']
    assert candidate(['xxx', 'asd', 'aaaxxy', 'john doe', 'xxxAAA', 'xxx'], 'xx') == ['xxx', 'aaaxxy', 'xxxAAA', 'xxx']
    assert candidate(['grunt', 'trumpet', 'prune', 'gruesome'], 'run') == ['grunt', 'prune']
```
-/
