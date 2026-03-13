module

public import Std
open Std

public section

/-! ## Missing API -/

def Std.Iter.sum [Iterator α Id Nat] [IteratorLoop α Id Id] (it : Iter (α := α) Nat) :
    Nat :=
  it.fold (init := 0) (· + ·)

theorem Std.Iter.sum_toList [Iterator α Id Nat] [IteratorLoop α Id Id]
    [LawfulIteratorLoop α Id Id] [Iterators.Finite α Id] {it : Iter (α := α) Nat} :
    it.toList.sum = it.sum := by
  simp [sum, List.sum_eq_foldl, foldl_toList]

theorem Std.Iter.sum_toArray [Iterator α Id Nat] [IteratorLoop α Id Id]
    [LawfulIteratorLoop α Id Id] [Iterators.Finite α Id] {it : Iter (α := α) Nat} :
    it.toArray.sum = it.sum := by
  simp [← toArray_toList, sum_toList]

/-! ## Implementation -/

def totalMatch (xs ys : Array String) : Array String :=
  minOn (fun zs => (zs.iter.map (·.length)).sum) xs ys

/-! ## Tests -/

example : totalMatch #[] #[] = #[] := by native_decide
example : totalMatch #["hi", "admin"] #["hi", "hi"] = #["hi", "hi"] := by native_decide
example : totalMatch #["hi", "admin"] #["hi", "hi", "admin", "project"] = #["hi", "admin"] := by
  native_decide
example : totalMatch #["4"] #["1", "2", "3", "4", "5"] = #["4"] := by native_decide
example : totalMatch #["hi", "admin"] #["hI", "Hi"] = #["hI", "Hi"] := by native_decide
example : totalMatch #["hi", "admin"] #["hI", "hi", "hi"] = #["hI", "hi", "hi"] := by
  native_decide
example : totalMatch #["hi", "admin"] #["hI", "hi", "hii"] = #["hi", "admin"] := by native_decide
example : totalMatch #[] #["this"] = #[] := by native_decide
example : totalMatch #["this"] #[] = #[] := by native_decide

/-! ## Verification -/

theorem totalMatch_spec :
    totalMatch xs ys = if (xs.map (·.length)).sum ≤ (ys.map (·.length)).sum then xs else ys := by
  simp [totalMatch, ← Iter.sum_toArray, minOn_eq_if]

/-!
## Prompt

```python3

def total_match(lst1, lst2):
    '''
    Write a function that accepts two lists of strings and returns the list that has
    total number of chars in the all strings of the list less than the other list.

    if the two lists have the same number of chars, return the first list.

    Examples
    total_match([], []) ➞ []
    total_match(['hi', 'admin'], ['hI', 'Hi']) ➞ ['hI', 'Hi']
    total_match(['hi', 'admin'], ['hi', 'hi', 'admin', 'project']) ➞ ['hi', 'admin']
    total_match(['hi', 'admin'], ['hI', 'hi', 'hi']) ➞ ['hI', 'hi', 'hi']
    total_match(['4'], ['1', '2', '3', '4', '5']) ➞ ['4']
    '''
```

## Canonical solution

```python3
    l1 = 0
    for st in lst1:
        l1 += len(st)

    l2 = 0
    for st in lst2:
        l2 += len(st)

    if l1 <= l2:
        return lst1
    else:
        return lst2
```

## Tests

```python3
def check(candidate):

    # Check some simple cases
    assert True, "This prints if this assert fails 1 (good for debugging!)"
    assert candidate([], []) == []
    assert candidate(['hi', 'admin'], ['hi', 'hi']) == ['hi', 'hi']
    assert candidate(['hi', 'admin'], ['hi', 'hi', 'admin', 'project']) == ['hi', 'admin']
    assert candidate(['4'], ['1', '2', '3', '4', '5']) == ['4']
    assert candidate(['hi', 'admin'], ['hI', 'Hi']) == ['hI', 'Hi']
    assert candidate(['hi', 'admin'], ['hI', 'hi', 'hi']) == ['hI', 'hi', 'hi']
    assert candidate(['hi', 'admin'], ['hI', 'hi', 'hii']) == ['hi', 'admin']


    # Check some edge cases that are easy to work out by hand.
    assert True, "This prints if this assert fails 2 (also good for debugging!)"
    assert candidate([], ['this']) == []
    assert candidate(['this'], []) == []

```
-/
