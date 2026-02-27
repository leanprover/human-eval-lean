module

import Std.Data.TreeMap.Lemmas
import Std.Data.Iterators.Producers.Array
import Std.Data.Iterators.Producers.Range
import Std.Data.Iterators.Lemmas.Producers.Range

def numbers : Array String :=
  #["zero", "one", "two", "three", "four", "five", "six", "seven", "eight", "nine"]

def numberToNumber : Std.TreeMap String Nat :=
  (0...=9).iter.fold (init := ∅) (fun sofar num => sofar.insert numbers[num]! num)

def sortNumbers (str : String) : String :=
  str.split ' '
    |>.filter (!·.isEmpty)
    |>.map (numberToNumber[·.copy]!)
    |>.toList
    |>.mergeSort
    |>.map (numbers[·]!)
    |> String.intercalate " "

example : sortNumbers "" = "" := by native_decide
example : sortNumbers "three" = "three" := by native_decide
example : sortNumbers "three five nine" = "three five nine" := by native_decide
example : sortNumbers "five zero four seven nine eight" = "zero four five seven eight nine" := by native_decide
example : sortNumbers "six five four three two one zero" = "zero one two three four five six" := by native_decide

attribute [-simp] Nat.toList_rcc_eq_append

@[simp]
theorem toList_rcc_eq : (0...=9).toList = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] := by
  rw [Nat.toList_rcc_eq_append (by simp), ← List.range_eq_toList_rco]
  simp [List.range, List.range.loop]

theorem numberToNumber_numbers (i : Nat) (hi : i ≤ 9) :
    numberToNumber[numbers[i]!]! = i := by
  simp [numbers, numberToNumber, ← Std.Iter.foldl_toList, Std.TreeMap.getElem!_insert]
  rcases i with (_|_|_|_|_|_|_|_|_|_|_) <;> simp at ⊢ hi

theorem String.toList_split_intercalate {c : Char} {l : List String} (hl : ∀ s ∈ l, c ∉ s.toList) :
    ((String.intercalate (String.singleton c) l).split c).toList.map (·.copy) =
      if l = [] then [""] else l := by
  -- Proved in https://github.com/leanprover/lean4/pull/12723
  sorry

-- OK
@[simp]
theorem String.isEmpty_eq_false_iff {s : String} : s.isEmpty = false ↔ s ≠ "" := by
  simp [← String.isEmpty_iff]

theorem correct (l : List Nat) (hl : ∀ a ∈ l, a ≤ 9) :
    sortNumbers (String.intercalate " " (l.map (numbers[·]!))) =
      String.intercalate " " (l.mergeSort.map (numbers[·]!)) := by
  simp [sortNumbers]
  have : (numberToNumber[·.copy]!) = (fun (s : String) => numberToNumber[s]!) ∘ String.Slice.copy := rfl
  simp only [this]
  rw [← List.map_map]
  simp only [← String.Slice.isEmpty_copy]
  have : (!·.copy.isEmpty) = (fun (s : String) => !s.isEmpty) ∘ String.Slice.copy := rfl
  simp only [this]
  rw [← List.filter_map]
  erw [String.toList_split_intercalate]
  · simp only [List.map_eq_nil_iff]
    split <;> rename_i hl'
    · subst hl'
      simp
    · congr
      clear hl'
      induction l with
      | nil => simp
      | cons hd tl ih =>
        simp
        rw [List.filter_cons_of_pos]
        simp at ⊢ hl
        rw [ih]
        · simp
          rw [numberToNumber_numbers _ hl.1]
        · grind
        · simp at hl
          simp [numbers]
          rw [getElem?_pos]
          · rcases hd with (_|_|_|_|_|_|_|_|_|_|_) <;> simp at ⊢ hl
          · simp; grind
  · simp [numbers]
    intro a ha
    have := hl a ha
    rcases a with (_|_|_|_|_|_|_|_|_|_|_) <;> simp at ⊢ hl


/-!
## Prompt

```python3
from typing import List


def sort_numbers(numbers: str) -> str:
    """ Input is a space-delimited string of numberals from 'zero' to 'nine'.
    Valid choices are 'zero', 'one', 'two', 'three', 'four', 'five', 'six', 'seven', 'eight' and 'nine'.
    Return the string with numbers sorted from smallest to largest
    >>> sort_numbers('three one five')
    'one three five'
    """
```

## Canonical solution

```python3
    value_map = {
        'zero': 0,
        'one': 1,
        'two': 2,
        'three': 3,
        'four': 4,
        'five': 5,
        'six': 6,
        'seven': 7,
        'eight': 8,
        'nine': 9
    }
    return ' '.join(sorted([x for x in numbers.split(' ') if x], key=lambda x: value_map[x]))
```

## Tests

```python3


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    assert candidate('') == ''
    assert candidate('three') == 'three'
    assert candidate('three five nine') == 'three five nine'
    assert candidate('five zero four seven nine eight') == 'zero four five seven eight nine'
    assert candidate('six five four three two one zero') == 'zero one two three four five six'
```
-/
