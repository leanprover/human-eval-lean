module

def filterByPrefix (l : List String) (pref : String) : List String :=
  l.filter (·.startsWith pref)

open Classical in
theorem filterByPrefix_eq {l : List String} {pref : String} :
    filterByPrefix l pref = l.filter (fun s => pref.toList <+: s.toList) := by
  simp [filterByPrefix, ← String.startsWith_string_iff]

/-!
## Prompt

```python3
from typing import List


def filter_by_prefix(strings: List[str], prefix: str) -> List[str]:
    """ Filter an input list of strings only for ones that start with a given prefix.
    >>> filter_by_prefix([], 'a')
    []
    >>> filter_by_prefix(['abc', 'bcd', 'cde', 'array'], 'a')
    ['abc', 'array']
    """
```

## Canonical solution

```python3
    return [x for x in strings if x.startswith(prefix)]
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
```
-/
