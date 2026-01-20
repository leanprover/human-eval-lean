import Std

open Std

def collatzStep (n : Nat) : Nat :=
  if n > 0 then
    if n % 2 = 0 then n / 2 else n * 3 + 1
  else
    1

def CollatzRel : Nat → Nat → Prop := fun m n =>
    n ≠ 1 ∧ collatzStep n = m

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

instance : LawfulOrderOrd Nat := sorry

theorem oddCollatz_pairwise_distinct {n : Nat} {h : Acc CollatzRel n} :
    (oddCollatz n h).Pairwise (· ≠ ·) := by
  simpa [oddCollatz] using TreeSet.distinct_toList (α := Nat) (cmp := compare)

theorem oddCollatz_pairwise_lt {n : Nat} {h : Acc CollatzRel n} :
    (oddCollatz n h).Pairwise (· < ·) := by
  simpa [oddCollatz, compare_eq_lt] using TreeSet.ordered_toList (α := Nat) (cmp := compare)

theorem mem_oddCollatz_iff {m n : Nat} {h : Acc CollatzRel n} :
    m ∈ oddCollatz n h ↔ m = n ∨ CollatzRel m n := by
  sorry

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
