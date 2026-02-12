module

def unique : Unit :=
  ()

/-!
## Prompt

```python3


def unique(l: list):
    """Return sorted unique elements in a list
    >>> unique([5, 3, 5, 2, 3, 3, 9, 0, 123])
    [0, 2, 3, 5, 9, 123]
    """
```

## Canonical solution

```python3
    return sorted(list(set(l)))
```

## Tests

```python3


METADATA = {}


def check(candidate):
    assert candidate([5, 3, 5, 2, 3, 3, 9, 0, 123]) == [0, 2, 3, 5, 9, 123]

```
-/