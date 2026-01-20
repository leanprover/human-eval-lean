import Std

open Std

def collatzStep (n : Nat) : Nat :=
    if n % 2 = 0 then n / 2 else n * 3 + 1

def CollatzRel : Nat → Nat → Prop := fun m n =>
    n > 1 ∧ collatzStep n = m

instance : WellFoundedRelation { m : Nat // Acc CollatzRel m } := Acc.wfRel

def oddCollatz (n : Nat) (h : Acc CollatzRel n) : List Nat :=
  (collectOddCollatz ⟨n, h⟩ ∅).toList
where
  -- We attach a proof that `1` is reachable from `n` in finitely many steps to ensure termination.
  collectOddCollatz (n : { n : Nat // Acc CollatzRel n }) (acc : TreeSet Nat compare) :
      TreeSet Nat compare :=
    if h : n.val > 1 then
      collectOddCollatz ⟨collatzStep n, n.property.inv (by grind [CollatzRel])⟩
        (if n.val % 2 = 0 then acc else acc.insert n.val)
    else if n.val = 1 then
      acc.insert 1
    else
      acc
  termination_by n
  decreasing_by
    grind [CollatzRel]

theorem Std.compare_ne_eq [Ord α] [LawfulEqOrd α] {x y : α} :
    compare x y ≠ .eq ↔ x ≠ y := by
  simp

instance : LawfulOrderOrd Nat where
  isLE_compare := by grind [Nat.isLE_compare]
  isGE_compare := by grind [Nat.isGE_compare]

theorem oddCollatz_pairwise_distinct {n : Nat} {h : Acc CollatzRel n} :
    (oddCollatz n h).Pairwise (· ≠ ·) := by
  simpa [oddCollatz] using TreeSet.distinct_toList (α := Nat) (cmp := compare)

theorem oddCollatz_pairwise_lt {n : Nat} {h : Acc CollatzRel n} :
    (oddCollatz n h).Pairwise (· < ·) := by
  simpa [oddCollatz, compare_eq_lt] using TreeSet.ordered_toList (α := Nat) (cmp := compare)

theorem mod_two_eq_one_of_mem_oddCollatz {m n : Nat} {h : Acc CollatzRel n} (hm : m ∈ oddCollatz n h) :
    m % 2 = 1 := by
  simp only [oddCollatz, TreeSet.mem_toList] at hm
  generalize (⟨n, h⟩ : Subtype _) = n at hm
  generalize hg : (∅ : TreeSet Nat) = acc at hm
  have hm' (k : Nat) : k ∈ acc → k % 2 = 1 := by simp [← hg]
  clear hg
  fun_induction oddCollatz.collectOddCollatz n acc <;> grind

theorem collatzRel_collatzStep {n : Nat} (h : n > 1) :
    CollatzRel (collatzStep n) n := by
  grind [CollatzRel]

theorem transGen_collatzRel_of_mem_oddCollatz {m n : Nat} {h : Acc CollatzRel n} (hm : m ∈ oddCollatz n h)
    (hne : m ≠ n) :
    Relation.TransGen CollatzRel m n := by
  simp only [oddCollatz, TreeSet.mem_toList] at hm
  generalize htmp : (⟨n, h⟩ : Subtype _) = s at hm
  rw [show n = s.val by grind] at hne ⊢
  clear htmp
  generalize hg : (∅ : TreeSet Nat) = acc at hm
  have hm' (k : Nat) : k ∈ acc → k ≠ s → Relation.TransGen CollatzRel k s := by simp [← hg]
  clear hg
  generalize htmp : s = n₀ at hm' hne ⊢
  have hs : s = n₀ ∨ Relation.TransGen CollatzRel s n₀ := Or.inl htmp
  clear htmp
  fun_induction oddCollatz.collectOddCollatz s acc
  · rename_i n' acc' h' ih
    apply ih hm
    · grind
    · apply Or.inr
      rcases hs with rfl | hs
      · exact .single (collatzRel_collatzStep (by grind))
      · refine .trans ?_ hs
        exact .single (collatzRel_collatzStep (by grind))
  · grind
  · grind

theorem mem_collectOddCollatz_of_mem {n : { n : Nat // Acc CollatzRel n }} {acc : TreeSet Nat}
    {m : Nat} (h : m ∈ acc) :
    m ∈ oddCollatz.collectOddCollatz n acc := by
  fun_induction oddCollatz.collectOddCollatz n acc <;> grind

theorem mem_self_collectOddCollatz {n : { n : Nat // Acc CollatzRel n }} {acc : TreeSet Nat}
    (h : n.val % 2 = 1) :
    n.val ∈ oddCollatz.collectOddCollatz n acc := by
  fun_cases oddCollatz.collectOddCollatz n acc <;> grind [mem_collectOddCollatz_of_mem]

attribute [grind =] TreeSet.mem_toList

theorem mem_self_oddCollatz {n : Nat} {h : Acc CollatzRel n} (h' : n % 2 = 1) :
    n ∈ oddCollatz n h := by
  grind [oddCollatz, mem_self_collectOddCollatz]

theorem collectOddCollatz_mono {n : { n : Nat // Acc CollatzRel n }} {acc' acc : TreeSet Nat}
    (h : ∀ x, x ∈ acc' → x ∈ acc) {x : Nat} (hx : x ∈ oddCollatz.collectOddCollatz n acc') :
    x ∈ oddCollatz.collectOddCollatz n acc := by
  fun_induction oddCollatz.collectOddCollatz n acc generalizing acc' <;>
    grind [oddCollatz.collectOddCollatz]

theorem mem_oddCollatz_of_mem_oddCollatz_of_collatzRel {k m n : Nat} {hm hn}
    (hmem : k ∈ oddCollatz m hm) (hrel : CollatzRel m n) :
    k ∈ oddCollatz n hn := by
  grind [oddCollatz, CollatzRel, oddCollatz.collectOddCollatz, collectOddCollatz_mono]

theorem Acc.invTransGen {x y : α} (h₁ : Acc r x) (h₂ : Relation.TransGen r y x) : Acc r y := by
  simpa [acc_transGen_iff] using h₁.transGen.inv h₂

theorem mem_oddCollatz_of_mem_oddCollatz_of_transGen {k m n : Nat} {hn}
    (hrel : Relation.TransGen CollatzRel m n) (hmem : k ∈ oddCollatz m (hn.invTransGen hrel)) :
    k ∈ oddCollatz n hn := by
  induction hrel
  · grind [mem_oddCollatz_of_mem_oddCollatz_of_collatzRel]
  · grind [Acc.inv, mem_oddCollatz_of_mem_oddCollatz_of_collatzRel]

theorem mem_oddCollatz_of_transGen {m n : Nat} {hn : Acc CollatzRel n}
    (h : Relation.TransGen CollatzRel m n) (h' : m % 2 = 1) :
    m ∈ oddCollatz n hn := by
  grind [mem_oddCollatz_of_mem_oddCollatz_of_transGen, mem_self_oddCollatz]

theorem mem_oddCollatz_iff {m n : Nat} {h : Acc CollatzRel n} :
    m ∈ oddCollatz n h ↔ m % 2 = 1 ∧ (m = n ∨ Relation.TransGen CollatzRel m n) := by
  grind [mod_two_eq_one_of_mem_oddCollatz, transGen_collatzRel_of_mem_oddCollatz,
    mem_self_oddCollatz, mem_oddCollatz_of_transGen]

/-!
## Prompt

```python3

def get_odd_collatz(n):
    """
    Given a positive integer n, return a sorted list that has the odd numbers in collatz sequence.

    The Collatz conjecture is a conjecture in mathematics that concerns a sequence defined
    as follows: start with any positive integer n. Then each term is obtained from the
    previous term as follows: if the previous term is even, the next term is one half of
    the previous term. If the previous term is odd, the next term is 3 times the previous
    term plus 1. The conjecture is that no matter what value of n, the sequence will always reach 1.

    Note:
        1. Collatz(1) is [1].
        2. returned list sorted in increasing order.

    For example:
    get_odd_collatz(5) returns [1, 5] # The collatz sequence for 5 is [5, 16, 8, 4, 2, 1], so the odd numbers are only 1, and 5.
    """
```

## Canonical solution

```python3
    if n%2==0:
        odd_collatz = []
    else:
        odd_collatz = [n]
    while n > 1:
        if n % 2 == 0:
            n = n/2
        else:
            n = n*3 + 1

        if n%2 == 1:
            odd_collatz.append(int(n))

    return sorted(odd_collatz)
```

## Tests

```python3
def check(candidate):

    # Check some simple cases
    assert candidate(14) == [1, 5, 7, 11, 13, 17]
    assert candidate(5) == [1, 5]
    assert candidate(12) == [1, 3, 5], "This prints if this assert fails 1 (good for debugging!)"

    # Check some edge cases that are easy to work out by hand.
    assert candidate(1) == [1], "This prints if this assert fails 2 (also good for debugging!)"

```
-/
