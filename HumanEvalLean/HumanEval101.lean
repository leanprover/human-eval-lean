module

import Std
open Std Std.Do

set_option mvcgen.warning false

def delimiters : TreeSet Char := .ofList [' ', ',', '\t', '\n', '\r']

def wordsString (str : String) : Array String :=
  str.split (· ∈ delimiters)
    |>.filter (! ·.isEmpty)
    |>.map String.Slice.toString
    |>.toArray

def wordsString₂ (str : String) : Array String := Id.run do
  let mut words : Array String := #[]
  let mut currentWord : String := ""
  for c in str.chars do
    if c ∈ delimiters then
      if ! currentWord.isEmpty then
        words := words.push currentWord
        currentWord := ""
    else
      currentWord := currentWord.push c
  if ! currentWord.isEmpty then
    words := words.push currentWord
  return words

/-!
## Tests
-/

example : wordsString "Hi, my name is John" = #["Hi", "my", "name", "is", "John"] := by
  native_decide

example : wordsString "One, two, three, four, five, six" =
      #["One", "two", "three", "four", "five", "six"] := by
  native_decide

example : wordsString "Hi, my name" = #["Hi", "my", "name"] := by
  native_decide

example : wordsString "One,, two, three, four, five, six," =
      #["One", "two", "three", "four", "five", "six"] := by
  native_decide

example : wordsString "ahmed     , gamal" = #["ahmed", "gamal"] := by
  native_decide

example : wordsString "" = #[] := by
  native_decide

/-!
# Verification
-/

@[grind =]
theorem not_contains_empty {c : Char} :
    "".contains c = false := by
  sorry

@[grind =]
theorem contains_push {s : String} {c d : Char} :
    (s.push c).contains d = (s.contains d || c = d) := by
  sorry

theorem not_contains_of_mem_delimiters {s : String} {c : Char} (h : c ∈ delimiters) :
    (wordsString₂ s).all (! ·.contains c) := by
  generalize hret : wordsString₂ s = ret
  apply Id.of_wp_run_eq hret
  mvcgen
  case inv1 => exact ⇓⟨_, currentWord, words⟩ => ⌜¬ currentWord.contains c ∧ words.all (! ·.contains c)⌝
  all_goals grind

@[simp, grind =]
theorem toList_chars_empty : "".chars.toList = [] := by
  sorry

@[simp, grind =]
theorem isEmpty_empty : "".isEmpty := by
  sorry

@[simp, grind =]
theorem wordsString₂_empty :
    wordsString₂ "" = #[] := by
  simp [wordsString₂, ← Iter.forIn_toList]

theorem wordsString₂_push_of_mem {s : String} {c : Char} (h : c ∈ delimiters) :
    wordsString₂ (str.push c) = wordsString₂ str := by
  sorry

theorem wordsString₂_push {s : String} {c : Char} :
    wordsString₂ (str.push c) =
      if c ∈ delimiters then
        wordsString₂ str
      else if str.startPos.get?.all (· ∈ delimiters) then
        (wordsString₂ str).push (Char.toString c)
      else
        (wordsString₂ str).modify ((wordsString₂ str).size - 1) (·.push c) := by
  sorry

theorem wordsString_eq_append {s t : String} {c : Char} (h : c ∈ delimiters) :
    wordsString₂ (s ++ Char.toString c ++ t) = wordsString₂ s ++ wordsString₂ t := by
  sorry

/-!
## Prompt

```python3

def words_string(s):
    """
    You will be given a string of words separated by commas or spaces. Your task is
    to split the string into words and return an array of the words.

    For example:
    words_string("Hi, my name is John") == ["Hi", "my", "name", "is", "John"]
    words_string("One, two, three, four, five, six") == ["One", "two", "three", "four", "five", "six"]
    """
```

## Canonical solution

```python3
    if not s:
        return []

    s_list = []

    for letter in s:
        if letter == ',':
            s_list.append(' ')
        else:
            s_list.append(letter)

    s_list = "".join(s_list)
    return s_list.split()
```

## Tests

```python3
def check(candidate):

    # Check some simple cases
    assert True, "This prints if this assert fails 1 (good for debugging!)"
    assert candidate("Hi, my name is John") == ["Hi", "my", "name", "is", "John"]
    assert candidate("One, two, three, four, five, six") == ["One", "two", "three", "four", "five", "six"]
    assert candidate("Hi, my name") == ["Hi", "my", "name"]
    assert candidate("One,, two, three, four, five, six,") == ["One", "two", "three", "four", "five", "six"]

    # Check some edge cases that are easy to work out by hand.
    assert True, "This prints if this assert fails 2 (also good for debugging!)"
    assert candidate("") == []
    assert candidate("ahmed     , gamal") == ["ahmed", "gamal"]

```
-/
