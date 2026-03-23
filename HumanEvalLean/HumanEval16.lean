module
import Std.Data.Iterators.Consumers.Set
import Std.Data.Iterators.Lemmas.Consumers.Set
import Std.Data.HashSet.Lemmas

open Std

def countDistinctCharacters (s : String) : Nat :=
  (s.chars.map Char.toLower).toHashSet.size

theorem countDistinctCharacters_eq {s : String} :
    countDistinctCharacters s = (HashSet.ofList (s.toList.map Char.toLower)).size := by
  simp [countDistinctCharacters, Iter.toHashSet_equiv_ofList.size_eq]

theorem countDistinctCharacters_empty : countDistinctCharacters "" = 0 := by
  simp [countDistinctCharacters_eq]

theorem countDistinctCharacters_push {s : String} {c : Char} :
    countDistinctCharacters (s.push c) =
      if c.toLower ∈ s.toList.map Char.toLower then
        countDistinctCharacters s
      else
        countDistinctCharacters s + 1 := by
  simp only [countDistinctCharacters_eq, String.toList_push, List.map_append, List.map_cons,
    List.map_nil, List.mem_map]
  rw [HashSet.ofList_equiv_foldl.size_eq, List.foldl_append, List.foldl_cons, List.foldl_nil,
    HashSet.size_insert]
  simp [← HashSet.ofList_equiv_foldl.mem_iff, ← HashSet.ofList_equiv_foldl.size_eq]

/-!
## Prompt

```python3


def count_distinct_characters(string: str) -> int:
    """ Given a string, find out how many distinct characters (regardless of case) does it consist of
    >>> count_distinct_characters('xyzXYZ')
    3
    >>> count_distinct_characters('Jerry')
    4
    """
```

## Canonical solution

```python3
    return len(set(string.lower()))
```

## Tests

```python3


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    assert candidate('') == 0
    assert candidate('abcde') == 5
    assert candidate('abcde' + 'cade' + 'CADE') == 5
    assert candidate('aaaaAAAAaaaa') == 1
    assert candidate('Jerry jERRY JeRRRY') == 5
```
-/
