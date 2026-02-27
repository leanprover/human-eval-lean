module

def wordsString (s : String) : Array String :=
  s.split (fun c => c = ',' ∨ c = ' ')
    |>.filter (!·.isEmpty)
    |>.toStringArray

example : wordsString "Hi, my name is John" = #["Hi", "my", "name", "is", "John"] := by native_decide
example : wordsString "One, two, three, four, five, six" = #["One", "two", "three", "four", "five", "six"] := by native_decide
example : wordsString "Hi, my name" = #["Hi", "my", "name"] := by native_decide
example : wordsString "One,, two, three, four, five, six," = #["One", "two", "three", "four", "five", "six"] := by native_decide
example : wordsString "" = #[] := by native_decide
example : wordsString "ahmed     , gamal" = #["ahmed", "gamal"] := by native_decide

theorem wordsString_eq (s : String) : wordsString s =
    (s.split (fun c => c = ',' ∨ c = ' ')
      |>.toList
      |>.map String.Slice.copy
      |>.filter (!·.isEmpty)
      |>.toArray) := by
  simp [← Array.toList_inj, wordsString, List.filter_map]
  congr
  · sorry -- will be easy in next nightly
  · ext; simp [String.Slice.isEmpty_copy]


theorem wordsString_empty : wordsString "" = #[] := by
  rw [wordsString_eq]
  sorry

theorem wordsString_singleton_append_of_or (s : String) (c : Char) (hc : c = ',' ∨ c = ' ') :
    wordsString (String.singleton c ++ s) = wordsString s := by
  sorry

theorem wordsString_append_append (s t : String) (hs : ',' ∉ s.toList) (hs' : ' ' ∉ s.toList)
    (c : Char) (hc : c = ',' ∨ c = ' ') :
    wordsString (s ++ String.singleton c ++ t) = #[s] ++ wordsString t :=
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
