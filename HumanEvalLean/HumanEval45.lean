module

/-! ## Implementation -/

def triangleArea (a h : Rat) : Rat :=
  a * h / 2.0

/-! ## Tests -/

example : triangleArea 5 3 = 7.5 := by native_decide
example : triangleArea 2 2 = 2.0 := by native_decide
example : triangleArea 10 8 = 40.0 := by native_decide

/-!
## Verification

We won't formalize geometry and therefore cannot close the verification gap.
What follows are lemmas about `triangleArea` proving useful properties.
-/

theorem triangleArea_mul_left :
    triangleArea (c * a) h = c * triangleArea a h := by
  grind [triangleArea]

theorem triangleArea_mul_right :
    triangleArea a (c * h) = c * triangleArea a h := by
  grind [triangleArea]

theorem triangleArea_add_left :
    triangleArea (a + b) h = triangleArea a h + triangleArea b h := by
  grind [triangleArea]

theorem triangleArea_add_right :
    triangleArea a (h₁ + h₂) = triangleArea a h₁ + triangleArea a h₂ := by
  grind [triangleArea]

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
