module

import Std
open Std

/-! ## Missing API -/

def Std.Iter.sum [Add β] [Zero β] [Iterator α Id β] [IteratorLoop α Id Id]
    (it : Iter (α := α) β) : β :=
  it.fold (init := 0) (· + ·)

theorem Std.Iter.sum_toList [Add β] [Zero β]
    [Associative (α := β) (· + ·)] [Commutative (α := β) (· + ·)]
    [LawfulIdentity (· + ·) (0 : β)]
    [Iterator α Id β] [IteratorLoop α Id Id]
    [LawfulIteratorLoop α Id Id] [Iterators.Finite α Id] {it : Iter (α := α) β} :
    it.toList.sum = it.sum := by
  simp only [Iter.sum, ← Iter.foldl_toList, List.sum_eq_foldl]

/-! ## Implementation -/

def mean (xs : Array Rat) : Rat :=
  xs.sum / xs.size

def meanAbsoluteDeviation (xs : Array Rat) : Rat :=
  let mean := mean xs
  (xs.iter
    |>.map (fun x => (x - mean).abs)
    |>.sum) / xs.size

/-! ## Tests -/

example : meanAbsoluteDeviation #[(1 : Rat), 2, 3] = (2 : Rat) / 3 := by native_decide
example : meanAbsoluteDeviation #[(1 : Rat), 2, 3, 4] = 1 := by native_decide
example : meanAbsoluteDeviation #[(1 : Rat), 2, 3, 4, 5] = (6 : Rat) / 5 := by native_decide

/-!
## Verification

In order to verify the implementation, we point to library lemmas verifying `Array.sum`, `Rat.abs`,
`Array.size` and `Array.map`. Then we show that `mean` is actually the quotient of `sum` and `size`
and that `meanAbsoluteDeviation` computes the mean of absolute deviations from the mean,
expressed using said four library functions.
-/

section API

variable {x : Rat} {xs ys : Array Rat} {f : Rat → β}

example : (#[] : Array Rat).sum = 0 := Array.sum_empty
example : (#[x]).sum = x := Array.sum_singleton
example : (xs.push x).sum = xs.sum + x := Array.sum_push
example : (xs ++ ys).sum = xs.sum + ys.sum := Array.sum_append

example (h : 0 ≤ x) : x.abs = x := Rat.abs_of_nonneg h
example (h : x ≤ 0) : x.abs = -x := Rat.abs_of_nonpos h
example : 0 ≤ x.abs := Rat.abs_nonneg

example : (#[] : Array Rat).size = 0 := Array.size_empty
example : (#[x]).size = 1 := Array.size_singleton
example : (xs.push x).size = xs.size + 1 := Array.size_push _
example : (xs ++ ys).size = xs.size + ys.size := Array.size_append

example : (#[] : Array Rat).map f = #[] := Array.map_empty
example : #[x].map f = #[f x] := Array.map_singleton
example : (xs.push x).map f = (xs.map f).push (f x) := Array.map_push
example : (xs ++ ys).map f = xs.map f ++ ys.map f := Array.map_append

end API

theorem mean_spec {xs : Array Rat} :
    mean xs = xs.sum / xs.size := by
  simp [mean]

theorem meanAbsoluteDeviation_spec {xs : Array Rat} :
    meanAbsoluteDeviation xs =
      mean (xs.map (fun x => (x - mean xs).abs)) := by
  -- TODO: get rid of `+instances`, which is not endorsed.
  simp +instances [meanAbsoluteDeviation, mean, ← Iter.sum_toList, ← Array.sum_toList]

/-!
## Prompt

```python3
from typing import List


def mean_absolute_deviation(numbers: List[float]) -> float:
    """ For a given list of input numbers, calculate Mean Absolute Deviation
    around the mean of this dataset.
    Mean Absolute Deviation is the average absolute difference between each
    element and a centerpoint (mean in this case):
    MAD = average | x - x_mean |
    >>> mean_absolute_deviation([1.0, 2.0, 3.0, 4.0])
    1.0
    """
```

## Canonical solution

```python3
    mean = sum(numbers) / len(numbers)
    return sum(abs(x - mean) for x in numbers) / len(numbers)
```

## Tests

```python3


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    assert abs(candidate([1.0, 2.0, 3.0]) - 2.0/3.0) < 1e-6
    assert abs(candidate([1.0, 2.0, 3.0, 4.0]) - 1.0) < 1e-6
    assert abs(candidate([1.0, 2.0, 3.0, 4.0, 5.0]) - 6.0/5.0) < 1e-6

```
-/
