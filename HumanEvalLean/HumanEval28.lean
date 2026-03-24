module

def concatenate (strings : List String) : String :=
  String.join strings

theorem toList_concatenate {strings : List String} :
    (concatenate strings).toList = strings.flatMap String.toList := by
  -- https://github.com/leanprover/lean4/pull/13091
  simp [concatenate]

/-!
## Prompt

```python3
from typing import List


def concatenate(strings: List[str]) -> str:
    """ Concatenate list of strings into a single string
    >>> concatenate([])
    ''
    >>> concatenate(['a', 'b', 'c'])
    'abc'
    """
```

## Canonical solution

```python3
    return ''.join(strings)
```

## Tests

```python3


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    assert candidate([]) == ''
    assert candidate(['x', 'y', 'z']) == 'xyz'
    assert candidate(['x', 'y', 'z', 'w', 'k']) == 'xyzwk'
```
-/
