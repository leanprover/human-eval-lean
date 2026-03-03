module

public import Std
import all Init.Data.Range.Polymorphic.UpwardEnumerable
open Std Std.Do

set_option mvcgen.warning false

/-! ## Implementation 1: imperative -/

public def triplesSumToZero (xs : Array Int) : Bool := Id.run do
  let mut index : Std.TreeSet Int := ∅
  for h : i in 1...xs.size do
    index := index.insert xs[i - 1]
    for h' : j in i<...xs.size do
      if -(xs[i] + xs[j]) ∈ index then
        return true
  return false

/-! ## Tests 1 -/

example : triplesSumToZero #[1, 3, 5, 0] = false := by native_decide
example : triplesSumToZero #[1, 3, 5, -1] = false := by native_decide
example : triplesSumToZero #[1, 3, -2, 1] = true := by native_decide
example : triplesSumToZero #[1, 2, 3, 7] = false := by native_decide
example : triplesSumToZero #[1, 2, 5, 7] = false := by native_decide
example : triplesSumToZero #[2, 4, -5, 3, 9, 7] = true := by native_decide
example : triplesSumToZero #[1] = false := by native_decide
example : triplesSumToZero #[1, 3, 5, -100] = false := by native_decide
example : triplesSumToZero #[100, 3, 5, -100] = false := by native_decide

/-! ## Missing API -/

theorem Array.take_add_one {xs : Array α} {i : Nat} : xs.take (i + 1) = xs.take i ++ xs[i]?.toArray := by
  grind

theorem eq_getElem_append_cons {pref suff : List α} {cur : α} :
    (pref ++ cur :: suff)[pref.length]? = cur := by
  simp

grind_pattern eq_getElem_append_cons => pref ++ cur :: suff
attribute [grind =] Nat.getElem_toList_rco Nat.getElem_toList_roo
attribute [grind =] Nat.length_toList_rco Nat.length_toList_roo

/-! ## Verification 1 -/

def HasTriple (xs : List Int) : Prop :=
  ∃ (i j k : Nat) (hi : i < j) (hj : j < k) (hk : k < xs.length), xs[i] + xs[j] + xs[k] = 0

def HasTriple₁ (xs : List Int) (m : Nat) : Prop :=
  ∃ (i j k : Nat) (hi : i < j) (hj : j < k) (hk : k < xs.length)
    (h : j < m), xs[i] + xs[j] + xs[k] = 0

def HasTriple₂ (xs : List Int) (m n : Nat) : Prop :=
  ∃ (i j k : Nat) (hi : i < j) (hj : j < k) (hk : k < xs.length)
    (h : j < m ∨ j = m ∧ k < n), xs[i] + xs[j] + xs[k] = 0

theorem hasTriple₁_add_one_iff :
    HasTriple₁ xs (i + 1) ↔ HasTriple₂ xs i xs.length := by
  grind [HasTriple₁, HasTriple₂]

theorem hasTriple₂_add_one_iff {xs : Array Int} (h : m < xs.size) (h' : m < n ∧ n < xs.size) :
    HasTriple₂ xs.toList m (n + 1) ↔ HasTriple₂ xs.toList m n ∨ -(xs[m] + xs[n]) ∈ xs.take m := by
  grind [Array.mem_extract_iff_getElem, HasTriple₂]

theorem triplesSumToZero_iff {xs : Array Int} :
    triplesSumToZero xs ↔ HasTriple xs.toList := by
  generalize hwp : triplesSumToZero xs = wp
  apply Id.of_wp_run_eq hwp
  mvcgen
  invariants
  · .withEarlyReturn
      (fun cur index => ⌜(∀ x, x ∈ index ↔ x ∈ xs.take cur.pos) ∧ ¬ HasTriple₁ xs.toList (1 + cur.pos)⌝)
      (fun ret index => ⌜ret = HasTriple xs.toList⌝)
  · by
      rename_i a i c d e f g
      exact .withEarlyReturn
        (fun cur index => ⌜¬ HasTriple₂ xs.toList (i) (i + 1 + cur.pos)⌝)
        (fun ret _ => ⌜ret = HasTriple xs.toList⌝)
  case vc1 pref cur suff heq _ _ h_mem_iff pref' cur' suff' heq' _ h_mem _ =>
    have h₁ : -(xs[cur]'(by grind) + xs[cur']'(by grind)) ∈ xs.take cur := by grind [Array.take_add_one]
    have h₂ : cur < cur' := by grind
    -- can't really simplify this right now, see #12772
    grind [HasTriple, Array.mem_extract_iff_getElem]
  case vc2 =>
    simp only [List.Cursor.pos_mk, List.length_append, List.length_cons, List.length_nil]
    grind [Array.take_add_one, hasTriple₂_add_one_iff]
  case vc3 => grind [HasTriple, HasTriple₁, HasTriple₂]
  case vc4 => grind [Array.take_add_one, hasTriple₁_add_one_iff, Rco.mem_iff]
  case vc5 => grind [HasTriple, HasTriple₁, HasTriple₂]
  case vc6 => grind [HasTriple, HasTriple₁, HasTriple₂]
  case vc7 => grind [HasTriple, HasTriple₁, HasTriple₂]
  case vc8 => grind

/-! ## Implementation 2: purely functional -/

public def triplesSumToZero' (xs : Array Int) : Bool :=
  if h : 3 ≤ xs.size then
    loop₁ 1 ((∅ : TreeSet Int).insert xs[0])
  else
    false
where
  loop₁ (j : Nat) (index : TreeSet Int compare) : Bool :=
    if h : j < xs.size then
      loop₂ j (j + 1) index || loop₁ (j + 1) (index.insert xs[j])
    else
      false
  loop₂ (j : Nat) (k : Nat) (index : TreeSet Int compare) : Bool :=
    if h : j < k ∧ k < xs.size then
      -(xs[j] + xs[k]) ∈ index || loop₂ j (k + 1) index
    else
      false
  termination_by xs.size - k

/-! ## Tests 2 -/

example : triplesSumToZero' #[1, 3, 5, 0] = false := by native_decide
example : triplesSumToZero' #[1, 3, 5, -1] = false := by native_decide
example : triplesSumToZero' #[1, 3, -2, 1] = true := by native_decide
example : triplesSumToZero' #[1, 2, 3, 7] = false := by native_decide
example : triplesSumToZero' #[1, 2, 5, 7] = false := by native_decide
example : triplesSumToZero' #[2, 4, -5, 3, 9, 7] = true := by native_decide
example : triplesSumToZero' #[1] = false := by native_decide
example : triplesSumToZero' #[1, 3, 5, -100] = false := by native_decide
example : triplesSumToZero' #[100, 3, 5, -100] = false := by native_decide

/-! ## Verification 2 -/

private theorem triplesSumToZero'.loop₂_iff
    (h : ∀ x, x ∈ index ↔ x ∈ xs.take j)
    (h' : j < k₀) :
    triplesSumToZero'.loop₂ xs j k₀ index ↔
      ∃ (i k : Nat) (hi : i < j) (hk : k₀ ≤ k ∧ k < xs.size), xs[i] + xs[j] + xs[k] = 0 := by
  fun_induction triplesSumToZero'.loop₂ xs j k₀ index
  · rename_i k₀ hk₀ ih
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    rw [ih, h, Array.mem_extract_iff_getElem]
    · constructor
      · grind
      · rintro ⟨i, k, hi, hk, h⟩
        by_cases k₀ < k <;> grind
    · grind
  · grind

private theorem triplesSumToZero'.loop₁_iff
    (h : ∀ x, x ∈ index ↔ x ∈ xs.take j₀) :
    triplesSumToZero'.loop₁ xs j₀ index ↔
      ∃ (i j k : Nat) (hi : i < j) (hj : j₀ ≤ j ∧ j < k) (hk : k < xs.size), xs[i] + xs[j] + xs[k] = 0 := by
  fun_induction triplesSumToZero'.loop₁ xs j₀ index
  · grind [loop₂_iff h, Array.take_add_one]
  · grind

theorem triplesSumToZero'_iff :
    triplesSumToZero' xs ↔
      ∃ (i j k : Nat) (hi : i < j) (hj : j < k) (hk : k < xs.size), xs[i] + xs[j] + xs[k] = 0 := by
  fun_cases triplesSumToZero' xs
  · grind [triplesSumToZero'.loop₁_iff, Array.take_add_one]
  · grind

/-!
## Prompt

```python3


def triples_sum_to_zero(l: list):
    """
    triples_sum_to_zero takes a list of integers as an input.
    it returns True if there are three distinct elements in the list that
    sum to zero, and False otherwise.

    >>> triples_sum_to_zero([1, 3, 5, 0])
    False
    >>> triples_sum_to_zero([1, 3, -2, 1])
    True
    >>> triples_sum_to_zero([1, 2, 3, 7])
    False
    >>> triples_sum_to_zero([2, 4, -5, 3, 9, 7])
    True
    >>> triples_sum_to_zero([1])
    False
    """
```

## Canonical solution

```python3
    for i in range(len(l)):
        for j in range(i + 1, len(l)):
            for k in range(j + 1, len(l)):
                if l[i] + l[j] + l[k] == 0:
                    return True
    return False
```

## Tests

```python3


METADATA = {}


def check(candidate):
    assert candidate([1, 3, 5, 0]) == False
    assert candidate([1, 3, 5, -1]) == False
    assert candidate([1, 3, -2, 1]) == True
    assert candidate([1, 2, 3, 7]) == False
    assert candidate([1, 2, 5, 7]) == False
    assert candidate([2, 4, -5, 3, 9, 7]) == True
    assert candidate([1]) == False
    assert candidate([1, 3, 5, -100]) == False
    assert candidate([100, 3, 5, -100]) == False

```
-/
