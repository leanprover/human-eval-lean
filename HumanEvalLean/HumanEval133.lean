module

def sumSquares (xs : List Rat) : Int :=
  xs.map (·.ceil ^ (2 : Nat)) |>.sum

/-! ## Tests -/

example : sumSquares [1, 2, 3] = 14 := by native_decide
example : sumSquares [1.0, 2, 3] = 14 := by native_decide
example : sumSquares [1, 3, 5, 7] = 84 := by native_decide
example : sumSquares [1.4, 4.2, 0] = 29 := by native_decide
example : sumSquares [-2.4, 1, 1] = 6 := by native_decide
example : sumSquares [100, 1, 15, 2] = 10230 := by native_decide
example : sumSquares [10000, 10000] = 200000000 := by native_decide
example : sumSquares [-1.4, 4.6, 6.3] = 75 := by native_decide
example : sumSquares [-1.4, 17.9, 18.9, 19.9] = 1086 := by native_decide
example : sumSquares [0] = 0 := by native_decide
example : sumSquares [-1] = 1 := by native_decide
example : sumSquares [-1, 1, 0] = 2 := by native_decide

/-!
## Verification

We start pointing to lemmas that verify `Rat.ceil` and then express the correctness lemmas in
terms of `Rat.ceil`.
-/

/-- info: Rat.ceil_lt {x : Rat} : ↑x.ceil < x + 1 -/
#guard_msgs in
#check Rat.ceil_lt

/-- info: Rat.le_ceil {x : Rat} : x ≤ ↑x.ceil -/
#guard_msgs in
#check Rat.le_ceil

@[grind =]
theorem sumSquares_nil :
    sumSquares [] = 0 := by
  grind [sumSquares]

theorem sumSquares_singleton :
    sumSquares [x] = x.ceil * x.ceil := by
  grind [sumSquares]

theorem sumSquares_append {xs ys : List Rat} :
    sumSquares (xs ++ ys) = sumSquares xs + sumSquares ys := by
  grind [sumSquares]

/-!
## Prompt

```python3


def sum_squares(lst):
    """You are given a list of numbers.
    You need to return the sum of squared numbers in the given list,
    round each element in the list to the upper int(Ceiling) first.
    Examples:
    For lst = [1,2,3] the output should be 14
    For lst = [1,4,9] the output should be 98
    For lst = [1,3,5,7] the output should be 84
    For lst = [1.4,4.2,0] the output should be 29
    For lst = [-2.4,1,1] the output should be 6


    """
```

## Canonical solution

```python3
    import math
    squared = 0
    for i in lst:
        squared += math.ceil(i)**2
    return squared
```

## Tests

```python3
def check(candidate):

    # Check some simple cases
    assert candidate([1,2,3])==14, "This prints if this assert fails 1 (good for debugging!)"
    assert candidate([1.0,2,3])==14, "This prints if this assert fails 1 (good for debugging!)"
    assert candidate([1,3,5,7])==84, "This prints if this assert fails 1 (good for debugging!)"
    assert candidate([1.4,4.2,0])==29, "This prints if this assert fails 1 (good for debugging!)"
    assert candidate([-2.4,1,1])==6, "This prints if this assert fails 1 (good for debugging!)"

    assert candidate([100,1,15,2])==10230, "This prints if this assert fails 1 (good for debugging!)"
    assert candidate([10000,10000])==200000000, "This prints if this assert fails 1 (good for debugging!)"
    assert candidate([-1.4,4.6,6.3])==75, "This prints if this assert fails 1 (good for debugging!)"
    assert candidate([-1.4,17.9,18.9,19.9])==1086, "This prints if this assert fails 1 (good for debugging!)"


    # Check some edge cases that are easy to work out by hand.
    assert candidate([0])==0, "This prints if this assert fails 2 (also good for debugging!)"
    assert candidate([-1])==1, "This prints if this assert fails 2 (also good for debugging!)"
    assert candidate([-1,1,0])==2, "This prints if this assert fails 2 (also good for debugging!)"

```
-/
