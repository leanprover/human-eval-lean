module

open Std

/-!
## Implementation
-/

def argmax [LE β] [DecidableLE β] (f : α → β) (x y : α) : α :=
  if f y ≤ f x then x else y

def List.argmax [LE β] [DecidableLE β] (xs : List α) (f : α → β) (h : xs ≠ []) : α :=
  match xs with
  | x :: xs => xs.foldl (init := x) (_root_.argmax f)

def List.argmax? [LE β] [DecidableLE β] (xs : List α) (f : α → β) : Option α :=
  if h : xs ≠ [] then
    some (xs.argmax f h)
  else
    none

def longest? (xs : List String) : Option String :=
  xs.argmax? String.length

/-!
## Tests
-/

example : longest? [] = none := by native_decide
example : longest? ["x", "y", "z"] = some "x" := by native_decide
example : longest? ["x", "yyy", "zzzz", "www", "kkkk", "abc"] = some "zzzz" := by native_decide

/-!
## Verification
-/

@[grind =]
theorem List.argmax_singleton [LE β] [DecidableLE β] {x : α} {f : α → β} :
    [x].argmax f (by grind) = x := by
  grind [argmax]

@[grind =]
theorem argmax_assoc [LE β] [DecidableLE β] [IsLinearPreorder β] {f : α → β} {x y z : α} :
    argmax f (argmax f x y) z = argmax f x (argmax f y z) := by
  grind [argmax]

instance [LE β] [DecidableLE β] [IsLinearPreorder β] {f : α → β} :
    Associative (argmax f) where
  assoc := by apply argmax_assoc

theorem List.argmax_cons
    [LE β] [DecidableLE β] [IsLinearPreorder β] {x : α} {xs : List α} {f : α → β} :
    (x :: xs).argmax f (by grind) =
      if h : xs = [] then x else _root_.argmax f x (xs.argmax f h) := by
  simp only [argmax]
  match xs with
  | [] => simp
  | y :: xs => simp [foldl_assoc]

theorem List.foldl_etaExpand {α : Type u} {β : Type v} {f : α → β → α} {init : α} {xs : List β} :
    xs.foldl (init := init) f = xs.foldl (init := init) fun a b => f a b := by
  rfl

theorem argmax_eq_or [LE β] [DecidableLE β] {f : α → β} {x y : α} :
    argmax f x y = x ∨ argmax f x y = y := by
  grind [argmax]

@[grind =]
theorem argmax_self [LE β] [DecidableLE β] [IsLinearPreorder β] {f : α → β} {x : α} :
    argmax f x x = x := by
  grind [argmax]

@[grind =]
theorem argmax_eq_left [LE β] [DecidableLE β] {f : α → β} {x y : α} (h : f y ≤ f x) :
    argmax f x y = x := by
  grind [argmax]

@[grind =]
theorem argmax_eq_right [LE β] [DecidableLE β] {f : α → β} {x y : α} (h : ¬ f y ≤ f x) :
    argmax f x y = y := by
  grind [argmax]

@[grind =>]
theorem apply_left_le_apply_argmax [LE β] [DecidableLE β] [IsLinearPreorder β] {f : α → β}
    {x y : α} : f x ≤ f (argmax f x y) := by
  grind [argmax]

@[grind =>]
theorem apply_right_le_apply_argmax [LE β] [DecidableLE β] [IsLinearPreorder β]
    {f : α → β} {x y : α} : f y ≤ f (argmax f x y) := by
  grind [argmax]

@[grind .]
theorem List.argmax_mem [LE β] [DecidableLE β] [IsLinearPreorder β] {xs : List α}
    {f : α → β} {h : xs ≠ []} : xs.argmax f h ∈ xs := by
  simp only [List.argmax]
  match xs with
  | x :: xs =>
    fun_induction xs.foldl (init := x) (_root_.argmax f) <;> grind [argmax_eq_or]

@[grind =>]
theorem List.le_apply_argmax_of_mem [LE β] [DecidableLE β] [IsLinearPreorder β]
    {xs : List α} {f : α → β} {y : α} (hx : y ∈ xs) :
    f y ≤ f (xs.argmax f (List.ne_nil_of_mem hx)) := by
  have h : xs ≠ [] := List.ne_nil_of_mem hx
  simp only [List.argmax]
  match xs with
  | x :: xs =>
    fun_induction xs.foldl (init := x) (_root_.argmax f) generalizing y <;> grind

@[grind =]
theorem List.argmax_append [LE β] [DecidableLE β] [IsLinearPreorder β] {xs ys : List α}
    {f : α → β} (hxs : xs ≠ []) (hys : ys ≠ []) :
    (xs ++ ys).argmax f (by simp [hxs]) = _root_.argmax f (xs.argmax f hxs) (ys.argmax f hys) := by
  match xs, ys with
  | x :: xs, y :: ys => simp [argmax, foldl_assoc]

/--
`List.argmax xs f h` comes before any other element in `xs` where `f` attains its maximum.
-/
theorem List.argmax_left_leaning
    [LE β] [DecidableLE β] [IsLinearPreorder β] (xs : List α) (f : α → β) (h : xs ≠ []) :
    ∃ j : Fin xs.length, xs[j] = xs.argmax f h ∧
      ∀ i : Fin j, ¬ f (xs.argmax f h) ≤ f xs[i] := by
  -- open scoped Classical in
  -- let j := xs.findIdx (· == xs.argmax f h)
  -- have hj : xs[j]'(by grind) == xs.argmax f h := by grind
  -- refine ⟨⟨j, by grind⟩, by grind, ?_⟩
  -- intro i
  -- let lhs := xs.take j
  -- let rhs := xs.drop j
  -- have h₁ : xs = lhs ++ rhs := by simp [lhs, rhs]
  -- let ml := lhs.argmax? f
  -- let mr := rhs.argmax? f
  -- by_cases lhs = []; grind
  -- by_cases rhs = []; grind
  -- have h₂ := argmax_append (xs := lhs) (ys := rhs) (f := f) ‹_› ‹_›
  -- simp only [h₁, h₂, Fin.getElem_fin] at hj ⊢
  -- rw [getElem_append_left (by grind)]
  -- rw [getElem_append_right (by grind)] at hj
  -- simp only [show j - lhs.length = 0 by grind] at hj
  -- have : rhs.argmax f (by grind) = rhs[0]'(by grind) := by grind
  -- have : lhs.argmax f (by grind) = lhs[0]'(by grind) := by

  -- have : ¬ f (rhs.argmax f (by grind)) ≤ f (lhs.argmax f (by grind)) := by
  --   intro h
  --   rw [_root_.argmax_eq_left ‹_›] at h₂
  simp only [List.argmax]
  match xs with
  | x :: xs =>
    simp only
    clear h
    fun_induction xs.foldl (init := x) (_root_.argmax f)
    · exact ⟨⟨0, by grind⟩, by grind⟩
    · rename_i x y xs ih
      obtain ⟨j, ih⟩ := ih
      by_cases hj : j.val = 0
      · by_cases hm : f y ≤ f x
        · exact ⟨⟨0, by grind⟩, by grind⟩
        · exact ⟨⟨1, by grind⟩, by grind⟩
      · refine ⟨⟨j + 1, by grind⟩, ?_⟩
        obtain ⟨j, _⟩ := Nat.exists_eq_succ_of_ne_zero hj
        apply And.intro
        · grind
        · intro i hi
          have : i.val ≥ 2 := by have := ih.2 ⟨0, by grind⟩; grind
          obtain ⟨i, _⟩ := Nat.exists_eq_add_of_le this
          have := ih.2 ⟨i + 1, by grind⟩
          grind

/-- `List.argmax?` returns `none` when applied to an empty list. -/
@[grind =]
theorem List.argmax?_nil [LE β] [DecidableLE β] {f : α → β} :
    ([] : List α).argmax? f = none := by
  simp [argmax?]

@[grind =]
theorem List.argmax?_cons
    [LE β] [DecidableLE β] [IsLinearPreorder β] {f : α → β} {x : α} {xs : List α} :
    (x :: xs).argmax? f = (xs.argmax? f).elim x (_root_.argmax f x) := by
  grind [argmax?, argmax_cons]

@[grind =>]
theorem List.isSome_argmax?_of_mem
    [LE β] [DecidableLE β] {f : α → β} {xs : List α} {x : α} (h : x ∈ xs) :
    (xs.argmax? f).isSome := by
  grind [argmax?]

theorem List.le_apply_argmax?_get_of_mem
    [LE β] [DecidableLE β] [IsLinearPreorder β] {f : α → β} {xs : List α} {x : α} (h : x ∈ xs) :
    f x ≤ f ((xs.argmax? f).get (isSome_argmax?_of_mem h)) := by
  grind [argmax?]

-- The suggested patterns are not useful because all involve `IsLinearPreorder`.
grind_pattern List.le_apply_argmax?_get_of_mem => x ∈ xs, (xs.argmax? f).get _

theorem List.argmax?_left_leaning [LE β] [DecidableLE β] [IsLinearPreorder β] {xs : List α} {f : α → β} {x : α}
    (hx : xs.argmax? f = some x) :
    ∃ j : Fin xs.length, xs[j] = x ∧ ∀ i : Fin j, ¬ f x ≤ f xs[i] := by
  simp only [argmax?] at hx
  split at hx
  · simp only [Option.some.injEq] at hx
    rw [← hx]
    apply argmax_left_leaning
  · grind

@[grind =]
theorem List.argmax?_append [LE β] [DecidableLE β] [IsLinearPreorder β] (xs ys : List α) (f : α → β) :
    (xs ++ ys).argmax? f =
      (xs.argmax? f).merge (_root_.argmax f) (ys.argmax? f) := by
  grind [argmax?, append_eq_nil_iff]

/-!
### Main theorems

The following theorems verify important properties of `longest?`.
The requirements from the prompt are verified by `le_length_longest?_get_of_mem` and
`longest?_left_leaning`.

Some other useful properties are proved by the remaining lemmas.
-/

theorem longest?_nil : longest? [] = none := by
  grind [longest?]

theorem longest?_singleton : longest? [x] = some x := by
  grind [longest?]

theorem longest?_append {xs ys : List String} :
    longest? (xs ++ ys) = (longest? xs).merge (_root_.argmax String.length) (longest? ys) := by
  grind [longest?]

theorem isSome_longest?_of_mem {xs : List String} {x : String} (h : x ∈ xs) :
    (longest? xs).isSome := by
  grind [longest?]

theorem le_length_longest?_get_of_mem {xs : List String} {x : String} (h : x ∈ xs) :
    x.length ≤ ((longest? xs).get (isSome_longest?_of_mem h)).length := by
  grind [longest?]

/--
`longest?` returns the first string with maximum length: any other string with maximum length
appears at an index greater than the returned string's index.
-/
theorem longest?_left_leaning {xs : List String} {x : String} (h : longest? xs = some x) :
    ∃ j : Fin xs.length, xs[j] = x ∧ ∀ i : Fin j, xs[i].length < x.length := by
  rw [longest?] at h
  have := List.argmax?_left_leaning h
  grind

/-!
## Prompt

```python3
from typing import List, Optional


def longest(strings: List[str]) -> Optional[str]:
    """ Out of list of strings, return the longest one. Return the first one in case of multiple
    strings of the same length. Return None in case the input list is empty.
    >>> longest([])

    >>> longest(['a', 'b', 'c'])
    'a'
    >>> longest(['a', 'bb', 'ccc'])
    'ccc'
    """
```

## Canonical solution

```python3
    if not strings:
        return None

    maxlen = max(len(x) for x in strings)
    for s in strings:
        if len(s) == maxlen:
            return s
```

## Tests

```python3


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    assert candidate([]) == None
    assert candidate(['x', 'y', 'z']) == 'x'
    assert candidate(['x', 'yyy', 'zzzz', 'www', 'kkkk', 'abc']) == 'zzzz'
```
-/
