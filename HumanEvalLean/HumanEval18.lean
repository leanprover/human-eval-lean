module

-- This compiles to a tight loop calling `memcpy` a bunch of times
def howManyTimes (string substring : String) : Nat :=
  string.positions.filter (fun p => (string.sliceFrom p.1).startsWith substring) |>.length

example : howManyTimes "" "a" = 0 := by native_decide
example : howManyTimes "aaa" "a" = 3 := by native_decide
example : howManyTimes "aaaa" "aa" = 3 := by native_decide
example : howManyTimes "xyxyxyx" "x" = 4 := by native_decide
example : howManyTimes "cacacacac" "cac" = 4 := by native_decide
example : howManyTimes "john doe" "john" = 1 := by native_decide

def howManyTimesSpec [DecidableEq α] (string substring : List α) : Nat :=
  ((0...=string.length).toList.filter (fun i => (string.drop i).take substring.length = substring)).length

theorem howManyTimes_eq {string substring : String} (h : substring ≠ "") :
    howManyTimes string substring = howManyTimesSpec string.toList substring.toList := by
  simp only [howManyTimes, ne_eq,
    ← Std.Iter.length_toList_eq_length, Std.Iter.toList_filter, String.toList_positions,
    howManyTimesSpec, String.length_toList, Nat.zero_le, Nat.toList_rcc_eq_append,
    List.filter_append, List.filter_cons, decide_eq_true_eq, List.filter_nil, List.length_append]
  rw [if_neg (by simpa [← String.length_toList])]
  simp only [List.length_nil, Nat.add_zero]
  suffices ∀ (p : string.Pos) (t₁ t₂ : String), p.Splits t₁ t₂ →
      (List.filter (fun p => (string.sliceFrom p.val).startsWith substring)
        (String.Model.positionsFrom p)).length =
      (List.filter (fun i => decide (List.take substring.length (List.drop i string.toList) = substring.toList))
        (t₁.length...string.length).toList).length by
    simpa using this string.startPos "" string
  intro p t₁ t₂ ht
  induction p using String.Pos.next_induction generalizing t₁ t₂ with
  | next p hp ih =>
    obtain ⟨t₂, rfl⟩ := ht.exists_eq_singleton_append hp
    rw [String.Model.positionsFrom_eq_cons hp, List.filter_cons, Nat.toList_rco_eq_cons]
    · rw [List.filter_cons, apply_ite List.length, apply_ite List.length]
      simp only [String.Slice.startsWith_string_iff, ne_eq, List.length_cons, ih _ _ ht.next,
        String.append_singleton, String.length_push, decide_eq_true_eq]
      congr
      simp [ht.eq_append, ht.copy_sliceFrom_eq, List.prefix_iff_eq_take, eq_comm]
    · have := congrArg String.length ht.eq_append
      simp at this
      omega
  | endPos => simp_all

/-!
## Prompt

```python3


def how_many_times(string: str, substring: str) -> int:
    """ Find how many times a given substring can be found in the original string. Count overlaping cases.
    >>> how_many_times('', 'a')
    0
    >>> how_many_times('aaa', 'a')
    3
    >>> how_many_times('aaaa', 'aa')
    3
    """
```

## Canonical solution

```python3
    times = 0

    for i in range(len(string) - len(substring) + 1):
        if string[i:i+len(substring)] == substring:
            times += 1

    return times
```

## Tests

```python3


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    assert candidate('', 'x') == 0
    assert candidate('xyxyxyx', 'x') == 4
    assert candidate('cacacacac', 'cac') == 4
    assert candidate('john doe', 'john') == 1
```
-/
