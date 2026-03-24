module
import Std

def reverse (s : String) : String :=
  s.revChars.fold (init := "") String.push

def shiftString (s : String) (i : Nat) : String :=
  let p := s.startPos.nextn (s.length - i)
  (s.sliceFrom p).copy ++ s.sliceTo p

def circularShift (x shift : Nat) : String :=
  let str := x.repr
  if shift > str.length then
    reverse str
  else
    shiftString str shift

example : circularShift 12 1 = "21" := by native_decide
example : circularShift 12 2 = "12" := by native_decide
example : circularShift 100 2 = "001" := by native_decide
example : circularShift 97 8 = "79" := by native_decide

@[simp]
theorem toList_reverse {s : String} : (reverse s).toList = s.toList.reverse := by
  simp only [reverse, ne_eq, ← Std.Iter.foldl_toList, String.toList_revChars, List.foldl_reverse]
  suffices ∀ (t : String), (s.toList.foldr (fun c s => s.push c) t).toList = t.toList ++ s.toList.reverse by
    simpa using this ""
  intro t
  induction s.toList generalizing t with simp_all

theorem String.splits_nextn_startPos (s : String) (n : Nat) :
    (s.startPos.nextn n).Splits (String.ofList (s.toList.take n)) (String.ofList (s.toList.drop n)) :=
  sorry -- https://github.com/leanprover/lean4/pull/13106

@[simp]
theorem toList_shiftString {s : String} {i : Nat} :
    (shiftString s i).toList = s.toList.drop (s.length - i) ++ s.toList.take (s.length - i) := by
  have := s.splits_nextn_startPos (s.length - i)
  simp [shiftString, this.copy_sliceFrom_eq, this.copy_sliceTo_eq]

theorem toList_circularShift {x shift : Nat} : (circularShift x shift).toList =
    if shift > x.repr.length then
      x.repr.toList.reverse
    else
      x.repr.toList.drop (x.repr.length - shift) ++ x.repr.toList.take (x.repr.length - shift) := by
  simp [circularShift, apply_ite String.toList]


/-!
## Prompt

```python3

def circular_shift(x, shift):
    """Circular shift the digits of the integer x, shift the digits right by shift
    and return the result as a string.
    If shift > number of digits, return digits reversed.
    >>> circular_shift(12, 1)
    "21"
    >>> circular_shift(12, 2)
    "12"
    """
```

## Canonical solution

```python3
    s = str(x)
    if shift > len(s):
        return s[::-1]
    else:
        return s[len(s) - shift:] + s[:len(s) - shift]
```

## Tests

```python3
def check(candidate):

    # Check some simple cases
    assert candidate(100, 2) == "001"
    assert candidate(12, 2) == "12"
    assert candidate(97, 8) == "79"
    assert candidate(12, 1) == "21", "This prints if this assert fails 1 (good for debugging!)"

    # Check some edge cases that are easy to work out by hand.
    assert candidate(11, 101) == "11", "This prints if this assert fails 2 (also good for debugging!)"

```
-/
