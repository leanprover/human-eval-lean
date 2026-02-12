module

def triangle_area : Unit :=
  ()

/-!
## Prompt

```python3


def triangle_area(a, h):
    """Given length of a side and high return area for a triangle.
    >>> triangle_area(5, 3)
    7.5
    """
```

## Canonical solution

```python3
    return a * h / 2.0
```

## Tests

```python3


METADATA = {}


def check(candidate):
    assert candidate(5, 3) == 7.5
    assert candidate(2, 2) == 2.0
    assert candidate(10, 8) == 40.0

```
-/