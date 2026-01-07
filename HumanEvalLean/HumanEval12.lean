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

def longest (xs : List String) : Option String :=
  xs.argmax? String.length

/-!
## Verification
-/

/--
A list attains its maximum (with respect to function `f`) at element `x` if `x` appears in
the list and the function applied to all elements is at most the function applied to `x`.
-/
def AttainsMaximumAt [LE β] (xs : List α) (f : α → β) (x : α) : Prop :=
  x ∈ xs ∧ ∀ y ∈ xs, f y ≤ f x

/--
A string has maximum length in a list if it appears in the list and all strings in the
list are at most as long.
-/
def HasMaxLength (s : String) (xs : List String) : Prop :=
  s ∈ xs ∧ ∀ t ∈ xs, t.length ≤ s.length

@[grind =]
theorem List.argmax_singleton [LE β] [DecidableLE β] {x : α} {f : α → β} :
    [x].argmax f (by grind) = x := by
  grind [argmax]

@[grind =]
theorem argmax_assoc [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {f : α → β} {x y z : α} :
    argmax f (argmax f x y) z = argmax f x (argmax f y z) := by
  grind [argmax]

instance [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {f : α → β} :
    Std.Associative (argmax f) where
  assoc := by apply argmax_assoc

theorem List.argmax_cons [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {x : α} {xs : List α} {f : α → β} :
    (x :: xs).argmax f (by grind) = if h : xs = [] then x else _root_.argmax f x (xs.argmax f h) := by
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
theorem argmax_self [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {f : α → β} {x : α} :
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
theorem apply_left_le_apply_argmax [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {f : α → β} {x y : α} :
    f x ≤ f (argmax f x y) := by
  grind [argmax]

@[grind =>]
theorem apply_right_le_apply_argmax [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {f : α → β} {x y : α} :
    f y ≤ f (argmax f x y) := by
  grind [argmax]

@[grind .]
theorem List.argmax_mem [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {xs : List α} {f : α → β} {h : xs ≠ []} :
    xs.argmax f h ∈ xs := by
  simp only [List.argmax]
  match xs with
  | x :: xs =>
    fun_induction xs.foldl (init := x) (_root_.argmax f) <;> grind [argmax_eq_or]

theorem List.apply_le_apply_argmax [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {xs : List α} {f : α → β} {h : xs ≠ []} {y : α} (hx : y ∈ xs) :
    f y ≤ f (xs.argmax f h) := by
  simp only [List.argmax]
  match xs with
  | x :: xs =>
    fun_induction xs.foldl (init := x) (_root_.argmax f) generalizing y <;> grind

/-- `List.argmax xs f h` returns an element that attains the maximum of `f` over `xs`. -/
theorem List.argmax_attainsMaximum [LE β] [DecidableLE β] [Std.IsLinearPreorder β] (xs : List α) (f : α → β) (h : xs ≠ []) :
    AttainsMaximumAt xs f (xs.argmax f h) := by
  sorry

/--
`List.argmax xs f h` returns the first element that attains the maximum any other element
that attains the maximum appears at an index greater than or equal to the returned element's index.
-/
theorem List.argmax_left_leaning [LE β] [DecidableLE β] [Std.IsLinearPreorder β] (xs : List α) (f : α → β) (h : xs ≠ []) :
    ∃ j : Nat, xs[j]? = some (xs.argmax f h) ∧
      ∀ (i : Nat) (hi : i < xs.length), f (xs.argmax f h) ≤ f xs[i] → j ≤ i := by
  simp only [List.argmax]
  match xs with
  | x :: xs =>
    simp only
    clear h
    fun_induction xs.foldl (init := x) (_root_.argmax f)
    · exact ⟨0, by grind⟩
    · rename_i x y xs ih
      obtain ⟨j, ih⟩ := ih
      by_cases hj : j = 0
      · cases hj
        by_cases hm : f y ≤ f x
        · exact ⟨0, by grind⟩
        · exact ⟨1, by grind⟩
      · refine ⟨j + 1, ?_⟩
        obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
        apply And.intro
        · grind
        · intro i hi hle
          have : i ≥ 2 := by have := ih.2 0; grind
          obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le this
          have := ih.2 (i + 1)
          grind

@[grind =]
theorem List.argmax_append [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {xs ys : List α}
    {f : α → β} (hxs : xs ≠ []) (hys : ys ≠ []) :
    (xs ++ ys).argmax f (by simp [hxs]) = _root_.argmax f (xs.argmax f hxs) (ys.argmax f hys) := by
  match xs, ys with
  | x :: xs, y :: ys => simp [argmax, foldl_assoc]

/-- `List.argmax?` returns `none` when applied to an empty list. -/
@[grind =]
theorem List.argmax?_nil [LE β] [DecidableLE β] {f : α → β} :
    ([] : List α).argmax? f = none := by
  simp [argmax?]

/-- `List.argmax?` returns `some` when applied to a non-empty list. -/
@[grind =]
theorem List.isSome_argmax? [LE β] [DecidableLE β] {f : α → β} {xs : List α} (hxs : xs ≠ []) :
    (xs.argmax? f).isSome := by
  grind [argmax?]

@[grind =]
theorem List.argmax?_cons [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {f : α → β} {x : α} {xs : List α} :
    (x :: xs).argmax? f = (xs.argmax? f).elim x (_root_.argmax f x) := by
  grind [argmax?, argmax_cons]

/--
When `List.argmax? xs f` returns `some x`, the element `x` is the first that attains the maximum.
-/
theorem List.argmax?_left_leaning [LE β] [DecidableLE β] [Std.IsLinearPreorder β] (xs : List α) (f : α → β) (x : α)
    (hx : xs.argmax? f = some x) :
    ∃ j : Nat, xs[j]? = some x ∧ ∀ (i : Nat) (hi : i < xs.length), f x ≤ f xs[i] → j ≤ i := by
  simp only [argmax?] at hx
  split at hx
  · simp only [Option.some.injEq] at hx
    rw [← hx]
    apply argmax_left_leaning
  · grind

@[grind =]
theorem List.argmax?_append [LE β] [DecidableLE β] [Std.IsLinearPreorder β] (xs ys : List α) (f : α → β) :
    (xs ++ ys).argmax? f =
      (xs.argmax? f).merge (_root_.argmax f) (ys.argmax? f) := by
  grind [argmax?, append_eq_nil_iff]

theorem List.attainsMaximum_argmax? [LE β] [DecidableLE β] {xs : List α} {f : α → β} {x : α}
    (hx : xs.argmax? f = some x) :
    AttainsMaximumAt xs f x := by
  sorry

/-- `longest` returns `none` when applied to an empty list. -/
theorem longest_nil : longest [] = none := by
  grind [longest]

theorem longest_append {xs ys : List String} :
    longest (xs ++ ys) = (longest xs).merge (_root_.argmax String.length) (longest ys) := by
  grind [longest]

/--
`longest` returns a string with maximum length when applied to a non-empty list.
-/
theorem longest_hasMaxLength (xs : List String) (h : xs ≠ []) :
    ∃ s, longest xs = some s ∧ HasMaxLength s xs := by
  sorry

/--
`longest` returns the first string with maximum length: any other string with maximum length
appears at an index greater than the returned string's index.
-/
theorem longest_left_leaning {xs : List String} {x : String} (h : longest xs = some x) :
    ∃ j : Fin xs.length, xs[j] = x ∧ ∀ i : Fin j, xs[i].length < x.length := by
  sorry


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
