module
import Std.Data.Iterators.Producers.Range
import Std

def stringSequence (n : Nat) : String :=
  Std.Iter.intercalateString " " ((0...=n).iter.map (String.toSlice ∘ Nat.repr))

example : stringSequence 0 = "0" := by native_decide
example : stringSequence 3 = "0 1 2 3" := by native_decide
example : stringSequence 10 = "0 1 2 3 4 5 6 7 8 9 10" := by native_decide

/-- Calling `stringSequence` and then splitting the result at space characters and attempting to
parse the components into natural numbers yields the sequence `[some 0, some 1, ..., some n]`. -/
theorem map_ofNat?_stringSequence {n : Nat} :
    ((stringSequence n).split ' ').toList.map String.Slice.toNat? =
      (0...=n).toList.map Option.some := by
  rw [stringSequence, ← String.Slice.toNat?_comp_copy, ← List.map_map,
    Std.Iter.intercalateString_eq, String.Slice.toStringToString_eq, String.copy_toSlice]
  simp +instances only [String.reduceToSingleton]
  rw [String.toList_split_intercalate]
  · rw [Std.Iter.toList_map]
    simp
  · rw [Std.Iter.toList_map]
    simp only [Std.Rcc.toList_iter, List.mem_map, Function.comp_apply, ↓Char.isValue,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, String.copy_toSlice, Nat.toList_repr]
    intro a ha h
    simpa using Nat.isDigit_of_mem_toDigits (by decide) (by decide) h

/-!
## Prompt

```python3


def string_sequence(n: int) -> str:
    """ Return a string containing space-delimited numbers starting from 0 upto n inclusive.
    >>> string_sequence(0)
    '0'
    >>> string_sequence(5)
    '0 1 2 3 4 5'
    """
```

## Canonical solution

```python3
    return ' '.join([str(x) for x in range(n + 1)])
```

## Tests

```python3


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    assert candidate(0) == '0'
    assert candidate(3) == '0 1 2 3'
    assert candidate(10) == '0 1 2 3 4 5 6 7 8 9 10'
```
-/
