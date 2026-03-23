module
import Std.Data.Iterators.Producers.Range

@[inline]
def intercalateIter {α : Type} [Std.Iterator α Id String.Slice] [Std.IteratorLoop α Id Id]
    (s : String.Slice) (it : Std.Iter (α := α) String.Slice) : String :=
  (it.fold (init := none) (fun | none, sl => some sl.copy | some str, sl => str ++ s ++ sl)).getD ""

def stringSequence (n : Nat) : String :=
  intercalateIter " " ((0...=n).iter.map (String.toSlice ∘ Nat.repr))

example : stringSequence 0 = "0" := by native_decide
example : stringSequence 3 = "0 1 2 3" := by native_decide
example : stringSequence 10 = "0 1 2 3 4 5 6 7 8 9 10" := by native_decide

theorem String.intercalate_append_of_ne_nil {l m : List String} {s : String} (hl : l ≠ []) (hm : m ≠ []) :
    s.intercalate (l ++ m) = s.intercalate l ++ s ++ s.intercalate m := by
  induction l with
  | nil => simp_all
  | cons hd tl ih =>
    simp
    rw [String.intercalate_cons_of_ne_nil (by simp_all)]
    by_cases ht : tl = []
    · simp_all
    · simp [ih ht, String.intercalate_cons_of_ne_nil ht, String.append_assoc]

@[simp]
theorem intercalateIter_eq {α : Type} [Std.Iterator α Id String.Slice] [Std.Iterators.Finite α Id]
    [Std.IteratorLoop α Id Id] [Std.LawfulIteratorLoop α Id Id] {s : String.Slice} {it : Std.Iter (α := α) String.Slice} :
    intercalateIter s it = s.intercalate it.toList := by
  simp only [intercalateIter, String.appendSlice_eq, ← Std.Iter.foldl_toList,
    String.Slice.intercalate_eq]
  generalize s.copy = s
  have := congrArg (·.getD "") (List.foldl_map (init := none) (l := it.toList) (f := String.Slice.copy)
    (g := (fun | none, t => some t | some str, t => str ++ s ++ t)))
  refine Eq.trans ?_ (Eq.trans this.symm ?_)
  · congr
    grind
  · suffices ∀ (l m : List String),
        (l.foldl (init := if m = [] then none else some (s.intercalate m)) (fun | none, sl => some sl | some str, sl => str ++ s ++ sl)).getD ""
          = s.intercalate (m ++ l) by
      simpa using this (it.toList.map String.Slice.copy) []
    clear this
    intro l m
    induction l generalizing m with
    | nil => cases m <;> simp
    | cons hd tl ih =>
      rw [List.append_cons, ← ih, List.foldl_cons]
      congr
      simp only [List.append_eq_nil_iff, List.cons_ne_self, and_false, ↓reduceIte]
      match m with
      | [] => simp
      | x::xs =>
        simp only [reduceCtorEq, ↓reduceIte, List.cons_append, Option.some.injEq]
        rw [← List.cons_append, String.intercalate_append_of_ne_nil (by simp) (by simp),
          String.intercalate_singleton]

theorem map_ofNat?_stringSequence {n : Nat} :
    ((stringSequence n).split ' ').toList.map (String.toNat? ∘ String.Slice.copy) =
      (0...=n).toList.map Option.some := by
  simp [stringSequence]
  rw [intercalateIter_eq]q


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
