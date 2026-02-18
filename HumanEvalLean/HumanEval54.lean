module
import Std.Data.Iterators.Consumers.Set
import Std.Data.HashSet.Lemmas
import Std.Data.Iterators.Lemmas.Consumers.Set

open Std

def sameChars (s₁ s₂ : String) : Bool :=
  s₁.chars.toHashSet == s₂.chars.toHashSet

theorem sameChars_iff {s₁ s₂ : String} :
    sameChars s₁ s₂ ↔ (∀ c, c ∈ s₁.toList ↔ c ∈ s₂.toList) := by
  simp [sameChars, HashSet.beq_iff_equiv, HashSet.Equiv.congr_left Iter.toHashSet_equiv_ofList,
    HashSet.Equiv.congr_right Iter.toHashSet_equiv_ofList, HashSet.equiv_iff_forall_mem_iff]

macro "sameChars_decide" : tactic => `(tactic| (simp [← Bool.not_eq_true, sameChars_iff, iff_def, forall_and]; decide))

example : sameChars "eabcdzzzz" "dddzzzzzzzddeddabc" = true := by sameChars_decide
example : sameChars "abcd" "dddddddabc" = true := by sameChars_decide
example : sameChars "dddddddabc" "abcd" = true := by sameChars_decide
example : sameChars "eabcd" "dddddddabc" = false := by sameChars_decide
example : sameChars "abcd" "dddddddabcf" = false := by sameChars_decide
example : sameChars "eabcdzzzz" "dddzzzzzzzddddabc" = false := by sameChars_decide
example : sameChars "aabb" "aaccc" = false := by sameChars_decide

/-!
## Prompt

```python3


def same_chars(s0: str, s1: str):
    """
    Check if two words have the same characters.
    >>> same_chars('eabcdzzzz', 'dddzzzzzzzddeddabc')
    True
    >>> same_chars('abcd', 'dddddddabc')
    True
    >>> same_chars('dddddddabc', 'abcd')
    True
    >>> same_chars('eabcd', 'dddddddabc')
    False
    >>> same_chars('abcd', 'dddddddabce')
    False
    >>> same_chars('eabcdzzzz', 'dddzzzzzzzddddabc')
    False
    """
```

## Canonical solution

```python3
    return set(s0) == set(s1)
```

## Tests

```python3


METADATA = {}


def check(candidate):
    assert candidate('eabcdzzzz', 'dddzzzzzzzddeddabc') == True
    assert candidate('abcd', 'dddddddabc') == True
    assert candidate('dddddddabc', 'abcd') == True
    assert candidate('eabcd', 'dddddddabc') == False
    assert candidate('abcd', 'dddddddabcf') == False
    assert candidate('eabcdzzzz', 'dddzzzzzzzddddabc') == False
    assert candidate('aabb', 'aaccc') == False

```
-/
