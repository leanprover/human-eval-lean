module

example : [].intersperse 7 = []                              := rfl
example : [5, 6, 3, 2].intersperse 8 = [5, 8, 6, 8, 3, 8, 2] := rfl
example : [2, 2, 2].intersperse 2 = [2, 2, 2, 2, 2]          := rfl

open List

/--
info: List.length_intersperse.{u_1} {α : Type u_1} {l : List α} {sep : α} : (intersperse sep l).length = 2 * l.length - 1
-/
#guard_msgs in
#check length_intersperse

/--
info: List.getElem?_intersperse_two_mul.{u_1} {α : Type u_1} {l : List α} {sep : α} {i : Nat} :
  (intersperse sep l)[2 * i]? = l[i]?
-/
#guard_msgs in
#check getElem?_intersperse_two_mul

/--
info: List.getElem?_intersperse_two_mul_add_one.{u_1} {α : Type u_1} {l : List α} {sep : α} {i : Nat} (h : i + 1 < l.length) :
  (intersperse sep l)[2 * i + 1]? = some sep
-/
#guard_msgs in
#check getElem?_intersperse_two_mul_add_one

/--
info: List.getElem_intersperse_two_mul.{u_1} {α : Type u_1} {l : List α} {sep : α} {i : Nat}
  (h : 2 * i < (intersperse sep l).length) : (intersperse sep l)[2 * i] = l[i]
-/
#guard_msgs in
#check getElem_intersperse_two_mul

/--
info: List.getElem_intersperse_two_mul_add_one.{u_1} {α : Type u_1} {l : List α} {sep : α} {i : Nat}
  (h : 2 * i + 1 < (intersperse sep l).length) : (intersperse sep l)[2 * i + 1] = sep
-/
#guard_msgs in
#check getElem_intersperse_two_mul_add_one

/--
info: List.getElem_eq_getElem_intersperse_two_mul.{u_1} {α : Type u_1} {l : List α} {sep : α} {i : Nat} (h : i < l.length) :
  l[i] = (intersperse sep l)[2 * i]
-/
#guard_msgs in
#check getElem_eq_getElem_intersperse_two_mul

/-!
## Prompt

```python3
from typing import List


def intersperse(numbers: List[int], delimeter: int) -> List[int]:
    """ Insert a number 'delimeter' between every two consecutive elements of input list `numbers'
    >>> intersperse([], 4)
    []
    >>> intersperse([1, 2, 3], 4)
    [1, 4, 2, 4, 3]
    """
```

## Canonical solution

```python3
    if not numbers:
        return []

    result = []

    for n in numbers[:-1]:
        result.append(n)
        result.append(delimeter)

    result.append(numbers[-1])

    return result
```

## Tests

```python3


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    assert candidate([], 7) == []
    assert candidate([5, 6, 3, 2], 8) == [5, 8, 6, 8, 3, 8, 2]
    assert candidate([2, 2, 2], 2) == [2, 2, 2, 2, 2]
```
-/
