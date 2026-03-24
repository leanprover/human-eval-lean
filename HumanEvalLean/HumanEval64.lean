module
import Std

open Std

def vowelsList : List Char :=
  ['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U']

def vowels : HashSet Char :=
  .ofList vowelsList

def vowelsCount (s : String) : Nat :=
  let nVowels := s.chars.filter (· ∈ vowels) |>.length
  let atEnd := if s.back?.any (fun c => c == 'y' || c == 'Y') then 1 else 0
  nVowels + atEnd

example : vowelsCount "abcde" = 2 := by native_decide
example : vowelsCount "Alone" = 3 := by native_decide
example : vowelsCount "key" = 2 := by native_decide
example : vowelsCount "bye" = 1 := by native_decide
example : vowelsCount "keY" = 2 := by native_decide
example : vowelsCount "bYe" = 1 := by native_decide
example : vowelsCount "ACEDY" = 3 := by native_decide

theorem String.back?_eq {s : String} : s.back? = s.toList.getLast? :=
  sorry -- https://github.com/leanprover/lean4/pull/13105

theorem vowelsCount_eq {s : String} :
    vowelsCount s = (s.toList.filter (· ∈ vowelsList)).length +
      (if s.toList.getLast? = some 'y' ∨ s.toList.getLast? = some 'Y' then 1 else 0) := by
  simp only [vowelsCount, ne_eq, ← Iter.length_toList_eq_length,
    Iter.toList_filter, String.toList_chars, ↓Char.isValue]
  simp only [vowels, HashSet.mem_ofList, List.contains_eq_mem, decide_eq_true_eq, ↓Char.isValue,
    Option.any_eq_true, Bool.or_eq_true, beq_iff_eq, Nat.add_left_cancel_iff]
  simp [and_comm, String.back?_eq]

/-!
## Prompt

```python3

FIX = """
Add more test cases.
"""

def vowels_count(s):
    """Write a function vowels_count which takes a string representing
    a word as input and returns the number of vowels in the string.
    Vowels in this case are 'a', 'e', 'i', 'o', 'u'. Here, 'y' is also a
    vowel, but only when it is at the end of the given word.

    Example:
    >>> vowels_count("abcde")
    2
    >>> vowels_count("ACEDY")
    3
    """
```

## Canonical solution

```python3
    vowels = "aeiouAEIOU"
    n_vowels = sum(c in vowels for c in s)
    if s[-1] == 'y' or s[-1] == 'Y':
        n_vowels += 1
    return n_vowels
```

## Tests

```python3
def check(candidate):

    # Check some simple cases
    assert candidate("abcde") == 2, "Test 1"
    assert candidate("Alone") == 3, "Test 2"
    assert candidate("key") == 2, "Test 3"
    assert candidate("bye") == 1, "Test 4"
    assert candidate("keY") == 2, "Test 5"
    assert candidate("bYe") == 1, "Test 6"
    assert candidate("ACEDY") == 3, "Test 7"

    # Check some edge cases that are easy to work out by hand.
    assert True, "This prints if this assert fails 2 (also good for debugging!)"

```
-/
