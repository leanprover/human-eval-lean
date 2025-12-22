module

public import Std

public def isExchangePossible (xs ys : Array Int) : String :=
    let need := xs.iter.filter (· % 2 == 1) |>.count
    let available := ys.iter.filter (· % 2 == 0) |>.count
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
## Specification

The specification is a very direct formalization of the problem statement.
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

@[grind =]
public theorem List.countP_add_countP_not {xs : List Int} P :
    xs.countP P + xs.countP (! P ·) = xs.length := by
  induction xs <;> grind

@[grind =]
public theorem Vector.countP_add_countP_not {xs : Vector Int m} {P} :
    xs.countP P + xs.countP (! P ·) = m := by
  simp only [← Vector.countP_toList]
  grind

public theorem b {xs : Vector Int m} {ys : Vector Int n} :
    xs.countP (· % 2 == 1) ≤ ys.countP (· % 2 == 0) ↔
      m ≤ (VectorPair.mk xs ys).concat.countP (· %  2 == 0) := by
  conv => rhs; lhs; rw [← Vector.countP_add_countP_not (xs := xs) (P := (· % 2 == 1))]
  have : ∀ x : Int, (x % 2 == 0) = (! x % 2 == 1) := by grind
  simp only [this, VectorPair.concat, Vector.countP_append]
  grind

@[grind .]
public theorem Vector.Perm.countP_eq {xs ys : Vector α n} {P}
    (h : Vector.Perm xs ys) : xs.countP P = ys.countP P := by
  simp only [Vector.countP, ← Array.countP_toList, Vector.toList_toArray]
  grind [List.Perm.countP_eq, Array.Perm.toList, Vector.Perm.toArray]

public theorem core {xs : Vector Int m} {ys : Vector Int n} :
    xs.countP (· % 2 == 1) ≤ ys.countP (· % 2 == 0) ↔
      ∃ es, (VectorPair.exchanges ⟨xs, ys⟩ es).1.all (· % 2 == 0) := by
  constructor
  · induction hn : xs.countP (· % 2 == 1) generalizing xs ys
    · simp only [Nat.zero_le, true_imp_iff]
      refine ⟨[], ?_⟩
      simp [VectorPair.exchanges]
      simp at hn
      intro i hi
      have : xs[i] ∈ xs := by grind
      grind
    · rename_i n ih
      · intro h
        have hx : xs.countP (· % 2 == 1) > 0 := by grind
        have hy : ys.countP (· % 2 == 0) > 0 := by grind
        simp only [Vector.countP_pos_iff, Vector.exists_mem_iff_exists_getElem] at hx hy
        obtain ⟨ix, hix, hx⟩ := hx
        obtain ⟨iy, hiy, hy⟩ := hy
        -- let p := exchange (xs, ys) ⟨ix, hix⟩ ⟨iy, hiy⟩
        let xs' := xs.set ix ys[iy]
        let ys' := ys.set iy xs[ix]
        specialize ih (xs := xs') (ys := ys') (by grind)
        have : n ≤ ys'.countP (· % 2 == 0) := by grind
        simp only [this, true_imp_iff] at ih
        obtain ⟨es', hes'⟩ := ih
        refine ⟨⟨⟨ix, hix⟩, ⟨iy, hiy⟩⟩ :: es', ?_⟩
        simp only [VectorPair.exchanges_cons]
        exact hes' -- TODO: this is defeq abuse
  · rw [b]
    rintro ⟨es, hes⟩
    generalize VectorPair.mk xs ys = p at *
    have : m ≤ (p.exchanges es).concat.countP (· % 2 == 0) := by
      simp only [VectorPair.concat, Vector.countP_append]
      rw [Vector.countP_eq_size.mpr]
      · grind
      · simp only [Vector.all_eq_true, beq_iff_eq] at hes
        rw [Vector.forall_mem_iff_forall_getElem]
        grind
    grind

public theorem isExchangePossible_correct {xs ys : Array Int} :
    isExchangePossible xs ys = "YES" ↔
      ∃ es, (VectorPair.exchanges ⟨xs.toVector, ys.toVector⟩ es).1.all (· % 2 == 0) := by
  simp only [isExchangePossible, ite_eq_left_iff, Nat.not_le, String.reduceEq,
    imp_false, Nat.not_lt]
  simp only [← Std.Iter.length_toList_eq_count, Std.Iter.toList_filter, Array.toList_iter,
    ← List.countP_eq_length_filter, Array.countP_toList]
  conv => lhs; rw [← Vector.toArray_mk (xs := xs), ← Vector.toArray_mk (xs := ys)]
  rw [← Array.toVector, ← Array.toVector, Vector.countP_toArray, Vector.countP_toArray]
  rw [core]

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
