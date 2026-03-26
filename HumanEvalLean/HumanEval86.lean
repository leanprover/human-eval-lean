module

def antiShuffle (s : String) : String :=
  s.split ' '
    |>.map (fun sl => String.ofList (Array.mergeSort sl.chars.toArray).toList)
    |>.intercalateString " "

example : antiShuffle "Hi" = "Hi" := by native_decide
example : antiShuffle "hello" = "ehllo" := by native_decide
example : antiShuffle "Hello World!!!" = "Hello !!!Wdlor" := by native_decide
example : antiShuffle "number" = "bemnru" := by native_decide
example : antiShuffle "abcd" = "abcd" := by native_decide
example : antiShuffle "" = "" := by native_decide
example : antiShuffle "Hi. My name is Mister Robot. How are you?" = ".Hi My aemn is Meirst .Rboot How aer ?ouy" := by native_decide

@[simp]
theorem String.toString_eq : (ToString.toString (α := String)) = id := rfl

/-- Taking a list of words, joining them together separated by spaces and calling `antiShuffle` on that
is the same as first sorting the characters in every word and then joining that together. -/
theorem antiShuffle_intercalate {l : List (List Char)} (hl : ∀ s ∈ l, ' ' ∉ s) :
    antiShuffle (" ".intercalate (l.map String.ofList)) =
      " ".intercalate (l.map (fun s => String.ofList s.mergeSort)) := by
  rw [antiShuffle]
  simp +instances only [String.reduceToSingleton]
  rw [Std.Iter.intercalateString_eq, String.copy_toSlice, Std.Iter.toList_map]
  simp only [← Std.Iter.toArray_toList, String.Slice.toList_chars]
  have : (fun (sl : String.Slice) => String.ofList (sl.copy.toList.toArray.mergeSort).toList) =
    (fun (s : String) => String.ofList (s.toList.toArray.mergeSort).toList) ∘ String.Slice.copy := rfl
  simp only [this, ← List.map_map]
  rw [String.toList_split_intercalate (by simpa)]
  simp only [↓Char.isValue, String.reduceSingleton, List.map_eq_nil_iff, List.map_map]
  split
  · simp_all
  · simp only [String.toString_eq, Function.id_comp, List.map_map]
    congr
    ext1 s
    simp [Array.toList_mergeSort]

/-!
## Prompt

```python3

def anti_shuffle(s):
    """
    Write a function that takes a string and returns an ordered version of it.
    Ordered version of string, is a string where all words (separated by space)
    are replaced by a new word where all the characters arranged in
    ascending order based on ascii value.
    Note: You should keep the order of words and blank spaces in the sentence.

    For example:
    anti_shuffle('Hi') returns 'Hi'
    anti_shuffle('hello') returns 'ehllo'
    anti_shuffle('Hello World!!!') returns 'Hello !!!Wdlor'
    """
```

## Canonical solution

```python3
    return ' '.join([''.join(sorted(list(i))) for i in s.split(' ')])
```

## Tests

```python3
def check(candidate):

    # Check some simple cases
    assert candidate('Hi') == 'Hi'
    assert candidate('hello') == 'ehllo'
    assert candidate('number') == 'bemnru'
    assert candidate('abcd') == 'abcd'
    assert candidate('Hello World!!!') == 'Hello !!!Wdlor'
    assert candidate('') == ''
    assert candidate('Hi. My name is Mister Robot. How are you?') == '.Hi My aemn is Meirst .Rboot How aer ?ouy'
    # Check some edge cases that are easy to work out by hand.
    assert True

```
-/
