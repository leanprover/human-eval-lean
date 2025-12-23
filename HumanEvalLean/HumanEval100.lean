module

import Std.Data.Iterators

/-!
## Implementation
-/

@[grind =]
def makeAPile₁ (n : Nat) : List Nat :=
  (*...n).iter.map (n + 2 * ·) |>.toList

/-- An implementation that does not build up an intermediate array. -/
@[grind =]
def makeAPile₂ (n : Nat) : List Nat :=
  (*...n).iter.map (fun i => n + 2 * (n - 1 - i)) |>.toListRev

/-!
## Tests
-/

example : makeAPile₁ 0 = [] := by native_decide
example : makeAPile₁ 1 = [1] := by native_decide
example : makeAPile₁ 2 = [2, 4] := by native_decide
example : makeAPile₁ 3 = [3, 5, 7] := by native_decide
example : makeAPile₁ 4 = [4, 6, 8, 10] := by native_decide
example : makeAPile₁ 5 = [5, 7, 9, 11, 13] := by native_decide
example : makeAPile₁ 6 = [6, 8, 10, 12, 14, 16] := by native_decide
example : makeAPile₁ 8 = [8, 10, 12, 14, 16, 18, 20, 22] := by native_decide

example : makeAPile₂ 0 = [] := by native_decide
example : makeAPile₂ 1 = [1] := by native_decide
example : makeAPile₂ 2 = [2, 4] := by native_decide
example : makeAPile₂ 3 = [3, 5, 7] := by native_decide
example : makeAPile₂ 4 = [4, 6, 8, 10] := by native_decide
example : makeAPile₂ 5 = [5, 7, 9, 11, 13] := by native_decide
example : makeAPile₂ 6 = [6, 8, 10, 12, 14, 16] := by native_decide
example : makeAPile₂ 8 = [8, 10, 12, 14, 16, 18, 20, 22] := by native_decide

/-!
## Verification
-/

@[simp, grind =]
theorem length_makeAPile₁ {n : Nat} :
    (makeAPile₁ n).length = n := by
  simp [makeAPile₁]

@[grind =]
theorem geetElem_makeAPile₁ {n i : Nat} (h : i < n) :
    (makeAPile₁ n)[i]'(by grind) = n + 2 * i := by
  simp [makeAPile₁]

theorem getElem_zero_makeAPile₁ {n : Nat} (h : 0 < n) :
    (makeAPile₁ n)[0]'(by grind) = n := by
  grind

theorem getElem_makeAPile₁_mod_two {n i : Nat} (h : i < n) :
    (makeAPile₁ n)[i]'(by grind) % 2 = n % 2 := by
  grind

theorem getElem_succ_makeAPile₁ {n i : Nat} (h : i + 1 < n) :
    (makeAPile₁ n)[i + 1]'(by grind) = (makeAPile₁ n)[i]'(by grind) + 2 := by
  grind

@[simp, grind =]
theorem length_makeAPile₂ {n : Nat} :
    (makeAPile₂ n).length = n := by
  simp [makeAPile₂]

@[grind =]
theorem geetElem_makeAPile₂ {n i : Nat} (h : i < n) :
    (makeAPile₂ n)[i]'(by grind) = n + 2 * i := by
  grind [makeAPile₂, Std.Iter.toListRev_eq, Std.Iter.toList_map, Std.Rio.toList_iter,
    Nat.getElem_toList_rio, Nat.length_toList_rio]

theorem getElem_zero_makeAPile₂ {n : Nat} (h : 0 < n) :
    (makeAPile₂ n)[0]'(by grind) = n := by
  grind

theorem getElem_makeAPile₂_mod_two {n i : Nat} (h : i < n) :
    (makeAPile₂ n)[i]'(by grind) % 2 = n % 2 := by
  grind

theorem getElem_succ_makeAPile₂ {n i : Nat} (h : i + 1 < n) :
    (makeAPile₂ n)[i + 1]'(by grind) = (makeAPile₂ n)[i]'(by grind) + 2 := by
  grind

/-!
## Prompt

```python3

def make_a_pile(n):
    """
    Given a positive integer n, you have to make a pile of n levels of stones.
    The first level has n stones.
    The number of stones in the next level is:
        - the next odd number if n is odd.
        - the next even number if n is even.
    Return the number of stones in each level in a list, where element at index
    i represents the number of stones in the level (i+1).

    Examples:
    >>> make_a_pile(3)
    [3, 5, 7]
    """
```

## Canonical solution

```python3
    return [n + 2*i for i in range(n)]
```

## Tests

```python3
def check(candidate):

    # Check some simple cases
    assert candidate(3) == [3, 5, 7], "Test 3"
    assert candidate(4) == [4,6,8,10], "Test 4"
    assert candidate(5) == [5, 7, 9, 11, 13]
    assert candidate(6) == [6, 8, 10, 12, 14, 16]
    assert candidate(8) == [8, 10, 12, 14, 16, 18, 20, 22]

    # Check some edge cases that are easy to work out by hand.
    assert True, "This prints if this assert fails 2 (also good for debugging!)"

```
-/
