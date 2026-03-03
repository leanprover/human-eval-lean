module

/-! ## Implementation -/

public section

def incrList (xs : List Nat) : List Nat :=
  xs.map (· + 1)

end

/-! ## Tests -/

example : incrList [] = [] := by decide
example : incrList [1, 2, 3] = [2, 3, 4] := by decide
example : incrList [3, 2, 1] = [4, 3, 2] := by decide
example : incrList [5, 3, 5, 2, 3, 3, 9, 0, 123] = [6, 4, 6, 3, 4, 4, 10, 1, 124] := by decide
example : incrList [5, 2, 5, 2, 3, 3, 9, 0, 123] = [6, 3, 6, 3, 4, 4, 10, 1, 124] := by decide

/-! ## Verification -/

section

variable {x : Nat} {xs : List Nat}

@[simp, grind =]
theorem length_incrList :
    (incrList xs).length = xs.length := by
  grind [incrList]

@[simp, grind =]
theorem getElem_incrList {i : Nat} {h : i < (incrList xs).length} :
    (incrList xs)[i] = xs[i]'(by grind) + 1 := by
  grind [incrList]

/-!
The previous lemmas fully characterize the solution. Some additional useful lemmas:
-/

@[simp, grind =]
theorem incrList_nil :
    incrList [] = [] := by
  grind [incrList]

@[simp, grind =]
theorem incrList_cons :
    incrList (x :: xs) = (x + 1) :: incrList xs := by
  grind [incrList]

end

/-!
## Prompt

```python3


def incr_list(l: list):
    """Return list with elements incremented by 1.
    >>> incr_list([1, 2, 3])
    [2, 3, 4]
    >>> incr_list([5, 3, 5, 2, 3, 3, 9, 0, 123])
    [6, 4, 6, 3, 4, 4, 10, 1, 124]
    """
```

## Canonical solution

```python3
    return [(e + 1) for e in l]
```

## Tests

```python3


METADATA = {}


def check(candidate):
    assert candidate([]) == []
    assert candidate([3, 2, 1]) == [4, 3, 2]
    assert candidate([5, 2, 5, 2, 3, 3, 9, 0, 123]) == [6, 3, 6, 3, 4, 4, 10, 1, 124]

```
-/
