module

public import Std
import all Init.Data.Range.Polymorphic.UpwardEnumerable
open Std Std.Do

public def triplesSumToZero (xs : Array Int) : Bool := Id.run do
  let mut index : Std.TreeSet Int := ∅
  for h : i in 1...xs.size do
    -- ensures index ~ xs.take (i - 1)
    -- ensures: no triple with i₂ < i
    index := index.insert xs[i - 1]
    -- ensures index ~ xs.take i
    for h' : j in i<...xs.size do
      -- ensures index ~ xs.take i
      -- ensures: no triple with i₂ < i ∨ i₂ = i ∧ i₃ < j
      if -(xs[i] + xs[j]) ∈ index then
        return true
      -- ensures: no triple with i₂ < i ∨ i₂ = i ∧ i₃ ≤ j
    -- ensures index ~ xs.take i
    -- ensures: no triple with i₂ ≤ i
  return false

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
    if h : k < xs.size then
      -(xs[j]! + xs[k]) ∈ index || loop₂ j (k + 1) index
    else
      false

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
  · rename_i j₀ index hj₀ ih
    simp only [Bool.or_eq_true]
    rw [loop₂_iff h (by grind), ih]
    · grind
    · simp only [TreeSet.mem_insert, LawfulEqCmp.compare_eq_iff_eq, h, Array.take_eq_extract,
      Array.mem_extract_iff_getElem, Nat.zero_add]
      grind
  · grind

theorem triplesSumToZero'_iff :
    triplesSumToZero' xs ↔
      ∃ (i j k : Nat) (hi : i < j) (hj : j < k) (hk : k < xs.size), xs[i] + xs[j] + xs[k] = 0 := by
  rw [triplesSumToZero']
  split
  · rw [triplesSumToZero'.loop₁_iff]
    · grind
    · simp only [TreeSet.mem_insert, LawfulEqCmp.compare_eq_iff_eq, TreeSet.not_mem_emptyc,
      or_false, Array.take_eq_extract, Array.mem_extract_iff_getElem, Nat.zero_add]
      grind
  · grind

def HasTriple (xs : List Int) : Prop :=
  ∃ (i j k : Nat) (hi : i < j) (hj : j < k) (hk : k < xs.length), xs[i] + xs[j] + xs[k] = 0

def HasTriple₁ (xs : List Int) (m : Nat) : Prop :=
  ∃ (i j k : Nat) (hi : i < j) (hj : j < k) (hk : k < xs.length)
    (h : j < m), xs[i] + xs[j] + xs[k] = 0

def HasTriple₂ (xs : List Int) (m n : Nat) : Prop :=
  ∃ (i j k : Nat) (hi : i < j) (hj : j < k) (hk : k < xs.length)
    (h : j < m ∨ j = m ∧ k < n), xs[i] + xs[j] + xs[k] = 0

theorem Nat.eq_add_of_toList_rco_eq_append_cons {a b : Nat} {pref cur suff}
    (h : (a...b).toList = pref ++ cur :: suff) :
    cur = a + pref.length := by
  have := Rco.eq_succMany?_of_toList_eq_append_cons h
  simpa [Std.PRange.UpwardEnumerable.least, PRange.least?] using this

theorem Nat.eq_add_of_toList_roo_eq_append_cons {a b : Nat} {pref cur suff}
    (h : (a<...b).toList = pref ++ cur :: suff) :
    cur = a + 1 + pref.length := by
  apply eq_add_of_toList_rco_eq_append_cons h

theorem Nat.eq_add_of_toList_rio_eq_append_cons {a : Nat} {pref cur suff}
    (h : (*...a).toList = pref ++ cur :: suff) :
    cur = pref.length := by
  have := Rio.eq_succMany?_of_toList_eq_append_cons h
  simpa [PRange.UpwardEnumerable.least, PRange.least?] using this

attribute [grind =] Nat.length_toList_rco Nat.length_toList_roo

theorem bla :
    HasTriple₁ xs (i + 1) ↔ HasTriple₂ xs i xs.length := by
  grind [HasTriple₁, HasTriple₂]

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
    have := Nat.eq_add_of_toList_rco_eq_append_cons heq
    have := Nat.eq_add_of_toList_roo_eq_append_cons heq'
    simp_all
    simp +zetaDelta only [h_mem_iff, Array.mem_extract_iff_getElem,
      TreeSet.mem_insert] at h_mem
    rcases h_mem with h_mem | h_mem
    · exact ⟨cur - 1, 1 + pref.length, 1 + pref.length + 1 + pref'.length, by grind⟩
    · obtain ⟨k, hk, hk'⟩ := h_mem
      exact ⟨k, 1 + pref.length, 1 + pref.length + 1 + pref'.length, by grind⟩
  case vc2 pref cur suff heq _ _ h_mem_iff pref' cur' suff' heq' _ h_mem _ =>
    have := Nat.eq_add_of_toList_rco_eq_append_cons heq
    have := Nat.eq_add_of_toList_roo_eq_append_cons heq'
    simp_all
    simp +zetaDelta [h_mem_iff] at h_mem
    grind [Array.mem_extract_iff_getElem, HasTriple₂]
  case vc3 pref cur suff heq _ _ _ =>
    have := Nat.eq_add_of_toList_rco_eq_append_cons heq
    grind [HasTriple, HasTriple₁, HasTriple₂]
  case vc4 pref cur suff heq _ _ h_mem_iff _ _ _ =>
    have := Nat.eq_add_of_toList_rco_eq_append_cons heq
    simp only [reduceCtorEq, eq_iff_iff, false_and, and_false, exists_const, or_false] at h_mem_iff
    simp +zetaDelta only [h_mem_iff, TreeSet.mem_insert, reduceCtorEq, eq_iff_iff, false_and,
      exists_const, or_false, true_and, Array.mem_extract_iff_getElem, Nat.zero_add]
    have : cur ∈ 1...xs.size := by grind [=_ Rco.mem_toList_iff_mem]
    grind [bla, Rco.mem_iff]
  case vc5 =>
    grind [HasTriple, HasTriple₁, HasTriple₂]
  case vc6 =>
    grind [HasTriple, HasTriple₁, HasTriple₂]
  case vc7 =>
    grind [HasTriple, HasTriple₁, HasTriple₂]
  case vc8 => grind

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
