module

def triangle_area (a h : Rat) : Rat :=
  a * h / 2.0

/-!
We don't provide a formal verification here since it is not clear what to even verify.
-/

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
