module

public import Std
open Std

public section

/-!
## Implementation

This Problem assumes a language with dynamic typing. We approximate this by defining an inductive
`Any` type.
-/

inductive Any where
  | int : Int → Any
  | float : Float → Any
  | string : String → Any

@[grind =]
def Any.int? (x : Any) : Option Int :=
  if let .int a := x then
    some a
  else
    none

@[grind =]
def filterIntegers (xs : Array Any): Array Int :=
  xs.filterMap Any.int?

/-! ## Tests -/

example : filterIntegers #[] = #[] := by native_decide
example : filterIntegers #[.int 4, .float 23.2, .int 9, .string "adasd"] = #[4, 9] := by native_decide
example : filterIntegers #[.int 3, .string "c", .int 3, .int 3, .string "a", .string "b"] = #[3, 3, 3] := by native_decide

/-! ## Verification -/

section Verification

variable {xs ys : Array Any}

theorem filterIntegers_empty : filterIntegers #[] = #[] := by grind
theorem filterIntegers_singleton_int : filterIntegers #[.int x] = #[x] := by grind
theorem filterIntegers_singleton_float : filterIntegers #[.float x] = #[] := by grind
theorem filterIntegers_singleton_string : filterIntegers #[.string x] = #[] := by grind
theorem filterIntegers_push_int : filterIntegers (xs.push (.int x)) = (filterIntegers xs).push x := by grind
theorem filterIntegers_push_float : filterIntegers (xs.push (.float x)) = filterIntegers xs := by grind
theorem filterIntegers_push_string : filterIntegers (xs.push (.string x)) = filterIntegers xs := by grind
theorem filterIntegers_append : filterIntegers (x ++ y) = filterIntegers x ++ filterIntegers y := by grind

end Verification

/-!
## Prompt

```python3
from typing import List, Any


def filter_integers(values: List[Any]) -> List[int]:
    """ Filter given list of any python values only for integers
    >>> filter_integers(['a', 3.14, 5])
    [5]
    >>> filter_integers([1, 2, 3, 'abc', {}, []])
    [1, 2, 3]
    """
```

## Canonical solution

```python3
    return [x for x in values if isinstance(x, int)]
```

## Tests

```python3


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    assert candidate([]) == []
    assert candidate([4, {}, [], 23.2, 9, 'adasd']) == [4, 9]
    assert candidate([3, 'c', 3, 3, 'a', 'b']) == [3, 3, 3]
```
-/
