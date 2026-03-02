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
  simp only [numberToNumber, numbers, List.getElem!_toArray, List.getElem!_eq_getElem?_getD,
    String.default_eq, ← Std.Iter.foldl_toList, Std.Rcc.toList_iter, toList_rcc_eq, List.foldl_cons,
    List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.zero_lt_succ, getElem?_pos,
    List.getElem_cons_zero, Option.getD_some, Nat.reduceLT, List.getElem_cons_succ, Nat.lt_add_one,
    List.foldl_nil, Std.TreeMap.getElem!_insert, Std.LawfulEqCmp.compare_eq_iff_eq,
    Std.TreeMap.not_mem_emptyc, not_false_eq_true, getElem!_neg, Nat.default_eq_zero, ite_self]
  rcases i with (_|_|_|_|_|_|_|_|_|_|_) <;> simp at ⊢ hi

theorem sortNumbers_intercalate (l : List Nat) (hl : ∀ a ∈ l, a ≤ 9) :
    sortNumbers (String.intercalate " " (l.map (numbers[·]!))) =
      String.intercalate " " (l.mergeSort.map (numbers[·]!)) := by
  simp only [sortNumbers, ↓Char.isValue, Std.Iter.toList_map, Std.Iter.toList_filter]
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
        rw [List.map_cons, List.filter_cons_of_pos]
        · simp only [List.mem_cons, forall_eq_or_imp, List.map_cons, List.cons.injEq] at ⊢ hl
          simpa [ih (by grind)] using numberToNumber_numbers _ hl.1
        · simp only [List.mem_cons, forall_eq_or_imp, numbers, List.getElem!_toArray,
            List.getElem!_eq_getElem?_getD, String.default_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
            String.isEmpty_eq_false_iff, ne_eq] at hl ⊢
          rw [getElem?_pos]
          · rcases hd with (_|_|_|_|_|_|_|_|_|_|_) <;> simp at ⊢ hl
          · simp; grind
  · simp only [numbers, List.getElem!_toArray, List.getElem!_eq_getElem?_getD, String.default_eq,
      List.mem_map, ↓Char.isValue, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
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
