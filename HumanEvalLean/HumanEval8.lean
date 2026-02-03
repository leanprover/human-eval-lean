import Std.Tactic.Do
open Std.Do
set_option mvcgen.warning false

@[grind]
def List.product (xs : List Int) : Int :=
  match xs with
  | [] => 1
  | x :: xs' => x * (product xs')

@[grind]
def sumProduct (xs : List Int) : Int × Int := (List.sum xs, List.product xs)

def sumProductDo (xs : List Int) : Int × Int := Id.run do
  let mut sum := 0
  let mut product := 1
  for x in xs do
    sum := sum + x
    product := product * x

  return (sum, product)

@[grind =]
theorem List.product_append (xs : List Int) (ys : List Int) :
    product (xs ++ ys) = product xs * product ys := by
  induction xs with
  | nil =>
    change product ys = 1 * product ys
    omega
  | cons x xs hi =>
    change x * product (xs ++ ys) = x * product xs * product ys
    rw [hi]
    simp only [Int.mul_assoc]

theorem sumProductDo_correct (xs : List Int) : sumProductDo xs = sumProduct xs := by
  generalize h : sumProductDo xs = ys
  apply Id.of_wp_run_eq h
  mvcgen
  invariants
  · ⇓ ⟨ cur, result ⟩ =>
    ⌜ result.snd = List.sum cur.prefix ∧ result.fst = List.product cur.prefix ⌝
  with grind

example : sumProductDo [] = (0, 1) := by rfl
example : sumProductDo [1, 1, 1] = (3, 1) := by rfl
example : sumProductDo [100, 0] = (100, 0) := by rfl
example : sumProductDo [3, 5, 7] = (3 + 5 + 7, 3 * 5 * 7) := by rfl
example : sumProductDo [10] = (10, 10) := by rfl

/-!
## Prompt

```python3
from typing import List, Tuple


def sum_product(numbers: List[int]) -> Tuple[int, int]:
    """ For a given list of integers, return a tuple consisting of a sum and a product of all the integers in a list.
    Empty sum should be equal to 0 and empty product should be equal to 1.
    >>> sum_product([])
    (0, 1)
    >>> sum_product([1, 2, 3, 4])
    (10, 24)
    """
```

## Canonical solution

```python3
    sum_value = 0
    prod_value = 1

    for n in numbers:
        sum_value += n
        prod_value *= n
    return sum_value, prod_value
```

## Tests

```python3


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    assert candidate([]) == (0, 1)
    assert candidate([1, 1, 1]) == (3, 1)
    assert candidate([100, 0]) == (100, 0)
    assert candidate([3, 5, 7]) == (3 + 5 + 7, 3 * 5 * 7)
    assert candidate([10]) == (10, 10)
```
-/
