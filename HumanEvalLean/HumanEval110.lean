module

public import Std

public def isExchangePossible (xs ys : Array Int) : String :=
  let need := xs.iter.filter (· % 2 == 1) |>.length
  let available := ys.iter.filter (· % 2 == 0) |>.length
  if need ≤ available then "YES" else "NO"

/-!
## Prerequisites
-/

theorem Vector.exists_mem_iff_exists_getElem (P : α → Prop) (xs : Vector α n) :
    (∃ x ∈ xs, P x) ↔ ∃ (i : Nat), ∃ hi, P (xs[i]'hi) := by
  grind [mem_iff_getElem]

theorem Vector.forall_mem_iff_forall_getElem (P : α → Prop) (xs : Vector α n) :
    (∀ x ∈ xs, P x) ↔ ∀ (i : Nat) hi, P (xs[i]'hi) := by
  grind [mem_iff_getElem]

/-!
## Verification
-/

attribute [grind =] Vector.countP_set
attribute [grind ←] Vector.countP_eq_zero

public structure VectorPair (m n : Nat) where
  fst : Vector Int m
  snd : Vector Int n

public structure Exchange (m n : Nat) where
  fst : Fin m
  snd : Fin n

public def VectorPair.concat (p : VectorPair m n) : Vector Int (m + n) :=
  p.1 ++ p.2

public def VectorPair.exchange {m n} (p : VectorPair m n) (e : Exchange m n) :
    VectorPair m n :=
  ⟨p.1.set e.1 p.2[e.2], p.2.set e.2 p.1[e.1]⟩

@[grind =]
public theorem VectorPair.fst_exchange {m n} {p : VectorPair m n} {e : Exchange m n} :
    (p.exchange e).fst = p.1.set e.1 p.2[e.2] := by
  grind [exchange]

@[grind =]
public theorem VectorPair.snd_exchange {m n} {p : VectorPair m n} {e : Exchange m n} :
    (p.exchange e).snd = p.2.set e.2 p.1[e.1] := by
  grind [exchange]

public theorem VectorPair.concat_exchange_eq_swap {p : VectorPair m n} {e : Exchange m n} :
    (p.exchange e).concat = p.concat.swap e.1 (m + e.2) := by
  grind [exchange, concat]

@[grind ←]
public theorem VectorPair.concat_exchange_perm {p : VectorPair m n} {e : Exchange m n} :
    Vector.Perm (p.exchange e).concat p.concat := by
  grind [VectorPair.concat_exchange_eq_swap, Vector.swap_perm]

public def VectorPair.exchanges {m n} (p : VectorPair m n) (es : List (Exchange m n)) :
    VectorPair m n :=
  es.foldl (init := p) (fun acc e => acc.exchange e)

@[grind =]
public theorem VectorPair.exchanges_cons {m n} {p : VectorPair m n} {e es} :
    p.exchanges (e :: es) = (p.exchange e).exchanges es := by
  grind [exchanges]

@[grind =]
public theorem VectorPair.exchanges_nil {m n} {p : VectorPair m n} :
    p.exchanges [] = p := by
  grind [exchanges]

@[grind ←]
public theorem VectorPair.concat_exchanges_perm {p : VectorPair m n} {es : List (Exchange m n)} :
    Vector.Perm (p.exchanges es).concat p.concat := by
  induction es generalizing p <;> grind [Vector.Perm.rfl, Vector.Perm.trans]

public theorem isExchangePossible_eq_yes_or_no {xs ys : Array Int} :
    isExchangePossible xs ys = "YES" ∨ isExchangePossible xs ys = "NO" := by
  grind [isExchangePossible]

public theorem VectorPair.countP_le_countP_iff_size_le_countP {p : VectorPair m n} :
    p.1.countP (· % 2 == 1) ≤ p.2.countP (· % 2 == 0) ↔
      m ≤ p.concat.countP (· %  2 == 0) := by
  simp only [Vector.size_eq_countP_add_countP (xs := p.1) (p := (· % 2 == 0))]
  grind [VectorPair.concat]

public theorem VectorPair.countP_le_countP_iff_exists {p : VectorPair m n} :
    p.1.countP (· % 2 == 1) ≤ p.2.countP (· % 2 == 0) ↔
      ∃ es, (VectorPair.exchanges p es).1.all (· % 2 == 0) := by
  constructor
  · induction hn : p.1.countP (· % 2 == 1) generalizing p
    · simp only [Nat.zero_le, true_imp_iff]
      refine ⟨[], ?_⟩
      have : ∀ (i : Nat) hi, p.1[i]'hi ∈ p.1 := by grind
      grind
    · rename_i n ih
      · intro h
        have hx : p.1.countP (· % 2 == 1) > 0 := by grind
        have hy : p.2.countP (· % 2 == 0) > 0 := by grind
        simp only [Vector.countP_pos_iff, Vector.exists_mem_iff_exists_getElem] at hx hy
        -- There are indices `ix`, `iy` such that `p.fst[ix] % 2 = 1` and `p.snd[iy] % 2 = 0`.
        -- By exchanging these, we can decrease the number of odd numbers in the first vector,
        -- enabling the application of the inductive hypothesis.
        obtain ⟨ix, hix, hx⟩ := hx
        obtain ⟨iy, hiy, hy⟩ := hy
        let p' := p.exchange ⟨⟨ix, hix⟩, ⟨iy, hiy⟩⟩
        specialize ih (p := p') (by grind)
        have : n ≤ p'.2.countP (· % 2 == 0) := by grind
        simp only [this, true_imp_iff] at ih
        obtain ⟨es', hes'⟩ := ih
        exact ⟨⟨⟨ix, hix⟩, ⟨iy, hiy⟩⟩ :: es', (by grind)⟩
  · rw [VectorPair.countP_le_countP_iff_size_le_countP]
    rintro ⟨es, hes⟩
    have : m ≤ (p.exchanges es).concat.countP (· % 2 == 0) := by
      simp only [VectorPair.concat, Vector.countP_append]
      rw [Vector.countP_eq_size.mpr]
      · grind
      · simp only [Vector.all_eq_true, beq_iff_eq] at hes
        rw [Vector.forall_mem_iff_forall_getElem]
        grind
    -- Alternatively to the following, we could add `Vector.Perm.countP_eq` and use
    -- `grind [Vector.Perm.countP_eq]`.
    grind [List.Perm.countP_eq, Vector.Perm.toList, =_ Vector.countP_toList]

public theorem isExchangePossible_correct {xs ys : Array Int} :
    isExchangePossible xs ys = "YES" ↔
      ∃ es, (VectorPair.exchanges ⟨xs.toVector, ys.toVector⟩ es).1.all (· % 2 == 0) := by
  -- package `xs`, `ys` into a `VectorPair`
  generalize h : VectorPair.mk xs.toVector ys.toVector = p
  simp only [show xs = p.1.toArray by grind, show ys = p.2.toArray by grind]
  -- prove the actual statement
  simp [isExchangePossible, ← Std.Iter.length_toList_eq_length,
    ← List.countP_eq_length_filter, VectorPair.countP_le_countP_iff_exists]

/-!
## Prompt

```python3

def exchange(lst1, lst2):
    """In this problem, you will implement a function that takes two lists of numbers,
    and determines whether it is possible to perform an exchange of elements
    between them to make lst1 a list of only even numbers.
    There is no limit on the number of exchanged elements between lst1 and lst2.
    If it is possible to exchange elements between the lst1 and lst2 to make
    all the elements of lst1 to be even, return "YES".
    Otherwise, return "NO".
    For example:
    exchange([1, 2, 3, 4], [1, 2, 3, 4]) => "YES"
    exchange([1, 2, 3, 4], [1, 5, 3, 4]) => "NO"
    It is assumed that the input lists will be non-empty.
    """
```

## Canonical solution

```python3
    odd = 0
    even = 0
    for i in lst1:
        if i%2 == 1:
            odd += 1
    for i in lst2:
        if i%2 == 0:
            even += 1
    if even >= odd:
        return "YES"
    return "NO"

```

## Tests

```python3
def check(candidate):

    # Check some simple cases
    assert candidate([1, 2, 3, 4], [1, 2, 3, 4]) == "YES"
    assert candidate([1, 2, 3, 4], [1, 5, 3, 4]) == "NO"
    assert candidate([1, 2, 3, 4], [2, 1, 4, 3]) == "YES"
    assert candidate([5, 7, 3], [2, 6, 4]) == "YES"
    assert candidate([5, 7, 3], [2, 6, 3]) == "NO"
    assert candidate([3, 2, 6, 1, 8, 9], [3, 5, 5, 1, 1, 1]) == "NO"

    # Check some edge cases that are easy to work out by hand.
    assert candidate([100, 200], [200, 200]) == "YES"

```
-/
