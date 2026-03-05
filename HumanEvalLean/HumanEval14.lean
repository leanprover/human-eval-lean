module
import Std.Data.Iterators.Combinators.Drop
import Std.Data.Iterators.Lemmas.Combinators.Drop

def allPrefixes (string : String) : Array String.Slice :=
  if string = "" then
    #[]
  else
    ((string.positions.drop 1).map (string.sliceTo ·.1) |>.toArray).push string

example : allPrefixes "" = #[] := by native_decide
example : allPrefixes "asdfgh" == #["a".toSlice, "as", "asd", "asdf", "asdfg", "asdfgh"] := by native_decide
example : allPrefixes "WWW" == #["W".toSlice, "WW", "WWW"] := by native_decide

@[simp]
theorem String.length_pos_iff {s : String} : 0 < s.length ↔ s ≠ "" := by
  simp [Nat.pos_iff_ne_zero, String.length_eq_zero_iff]

theorem List.take_append_eq_left {l₁ l₂ : List α} {n : Nat} (h : n = l₁.length) :
    (l₁ ++ l₂).take n = l₁ := by
  subst h; simp

theorem map_allPrefixes {s : String} :
    (allPrefixes s).toList.map (String.toList ∘ String.Slice.copy) =
      (1...=s.toList.length).toList.map s.toList.take := by
  rw [allPrefixes]
  split
  · simp_all
  · rw [Array.toList_push, Std.Iter.toList_toArray,
      Nat.toList_rcc_eq_append (by simpa [Nat.succ_le_iff])]
    simp only [ne_eq, Std.Iter.toList_map, Std.Iter.toList_drop, String.toList_positions,
      List.drop_one, List.map_tail, List.map_subtype, List.map_append, List.map_map, List.map_cons,
      Function.comp_apply, String.copy_toSlice, List.map_nil, List.take_length,
      List.append_cancel_right_eq]
    suffices ∀ (p : s.Pos) (t₁ t₂ : String), p.Splits t₁ t₂ →
        ((String.Model.positionsFrom p).unattach.map
          ((String.toList ∘ String.Slice.copy) ∘ s.sliceTo)).tail =
          ((t₁.length + 1)...s.length).toList.map s.toList.take by
      simpa using this s.startPos
    intro p t₁ t₂ hp
    induction p using String.Pos.next_induction generalizing t₁ t₂ with
    | next p h ih =>
      obtain ⟨t₂, rfl⟩ := hp.exists_eq_singleton_append h
      have := ih _ _ hp.next
      simp only [ne_eq, String.append_singleton, String.length_push,
        String.Model.positionsFrom_eq_cons h, List.unattach_cons, List.map_cons,
        Function.comp_apply, List.tail_cons] at this ⊢
      by_cases h' : p.next h = s.endPos
      · obtain ⟨hs, rfl⟩ := by simpa [h'] using hp.next
        simp [← hs, h']
      · simp [String.Model.positionsFrom_eq_cons h'] at this ⊢
        have hlen : t₁.length + 1 < s.length := by
          obtain ⟨t₂, rfl⟩ := hp.next.exists_eq_singleton_append h'
          have := congrArg String.length hp.next.eq_append
          simp only [String.append_singleton, String.length_append, String.length_push,
            String.length_singleton] at this
          omega
        conv => rhs; rw [Nat.toList_rco_eq_cons (by omega)]
        simp only [this, List.map_cons, List.cons.injEq, and_true]
        conv => rhs; rw [hp.next.eq_append]
        simp only [String.append_singleton, String.toList_append, String.toList_push,
          List.append_assoc, List.cons_append, List.nil_append]
        rw [List.append_cons, List.take_append_eq_left (by simp)]
        simp [← hp.next.eq_left (p.next h).splits]
    | endPos => simp_all


/-!
## Prompt

```python3
from typing import List


def all_prefixes(string: str) -> List[str]:
    """ Return list of all prefixes from shortest to longest of the input string
    >>> all_prefixes('abc')
    ['a', 'ab', 'abc']
    """
```

## Canonical solution

```python3
    result = []

    for i in range(len(string)):
        result.append(string[:i+1])
    return result
```

## Tests

```python3


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    assert candidate('') == []
    assert candidate('asdfgh') == ['a', 'as', 'asd', 'asdf', 'asdfg', 'asdfgh']
    assert candidate('WWW') == ['W', 'WW', 'WWW']
```
-/
