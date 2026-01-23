module

import HumanEvalLean.Common.IsPrime

/-!
## Implementation
-/

def intersection (p : Int × Int) (q : Int × Int) : String :=
  let l := max p.1 q.1
  let r := min p.2 q.2
  let length := r - l
  if length > 0 ∧ isPrime length.toNat then "YES" else "NO"

/-!
## Tests
-/

example : intersection (1, 2) (2, 3) = "NO" := by native_decide
example : intersection (-1, 1) (0, 4) = "NO" := by native_decide
example : intersection (-3, -1) (-5, 5) = "YES" := by native_decide
example : intersection (-2, 2) (-4, 0) = "YES" := by native_decide
example : intersection (-11, 2) (-1, -1) = "NO" := by native_decide
example : intersection (1, 2) (3, 5) = "NO" := by native_decide
example : intersection (1, 2) (1, 2) = "NO" := by native_decide
example : intersection (-2, -2) (-3, -2) = "NO" := by native_decide

/-!
## Verification
-/

theorem intersection_swap {p q} :
    intersection p q = intersection q p := by
  grind [intersection]

theorem intersection_mem {p q} :
    intersection p q ∈ ["YES", "NO"] := by
  grind [intersection]

theorem Int.mem_filter_mem_rco_toList_rco {l₁ r₁ l₂ r₂ : Int} {x : Int} :
    x ∈ (l₁...r₁).toList.filter (· ∈ l₂...r₂) ↔ x ∈ ((max l₁ l₂)...(min r₁ r₂)) := by
  grind [Std.Rco.mem_toList_iff_mem, Std.Rco.mem_iff]

-- stolen from Init.Data.Range.Polymorphic.Lemmas, which is private
private theorem eq_of_pairwise_lt_of_mem_iff_mem {lt : α → α → Prop} [asymm : Std.Asymm lt]
    {l l' : List α} (hl : l.Pairwise lt) (hl' : l'.Pairwise lt)
    (h : ∀ a, a ∈ l ↔ a ∈ l') : l = l' := by
  induction l generalizing l'
  · cases l'
    · rfl
    · rename_i x xs
      specialize h x
      simp at h
  · rename_i x xs ih
    cases l'
    · specialize h x
      simp at h
    · have hx := (h x).mp (List.mem_cons_self)
      cases List.mem_cons.mp hx
      · rename_i y ys heq
        cases heq
        simp only [List.cons.injEq, true_and]
        apply ih hl.tail hl'.tail
        intro a
        specialize h a
        constructor
        · intro haxs
          replace h := h.mp (List.mem_cons_of_mem _ haxs)
          cases List.mem_cons.mp h
          · rename_i heq
            cases heq
            simp only [List.pairwise_cons] at hl
            have := hl.1 x haxs
            cases Std.Asymm.asymm _ _ this this
          · simp [*]
        · intro hays
          replace h := h.mpr (List.mem_cons_of_mem _ hays)
          cases List.mem_cons.mp h
          · rename_i heq
            cases heq
            simp only [List.pairwise_cons] at hl'
            have := hl'.1 x hays
            cases Std.Asymm.asymm _ _ this this
          · simp [*]
      · rename_i y ys hx
        simp only [List.pairwise_cons] at hl'
        have hlt := hl'.1 _ hx
        have hmem : y ∈ x :: xs := (h y).mpr List.mem_cons_self
        cases List.mem_cons.mp hmem
        · rename_i heq
          cases heq
          cases Std.Asymm.asymm _ _ hlt hlt
        · simp only [List.pairwise_cons] at hl
          have hgt := hl.1 y ‹_›
          cases Std.Asymm.asymm _ _ hlt hgt

-- not @[grind =] because `(· ∈ l₂...r₂)` cannot part of the discrimination key
theorem Int.filter_mem_rco_toList_rco {l₁ r₁ l₂ r₂ : Int} :
    (l₁...r₁).toList.filter (· ∈ l₂...r₂) = ((max l₁ l₂)...(min r₁ r₂)).toList := by
  apply eq_of_pairwise_lt_of_mem_iff_mem (lt := LT.lt)
  · apply List.Pairwise.filter
    apply Std.Rco.pairwise_toList_lt
  · apply Std.Rco.pairwise_toList_lt
  · grind [mem_filter_mem_rco_toList_rco, Std.Rco.mem_toList_iff_mem]

theorem intersection_spec {p q} :
    intersection p q = "YES" ↔ IsPrime ((p.1...p.2).toList.filter (· ∈ q.1...q.2)).length := by
  simp only [intersection, isPrime_eq_true_iff_isPrime, ite_eq_left_iff]
  suffices h : (min p.2 q.2 - max p.1 q.1).toNat = ((p.1...p.2).toList.filter (· ∈ q.1...q.2)).length by
    grind [isPrime_iff]
  simp [Int.filter_mem_rco_toList_rco]

/-!
## Prompt

```python3

def intersection(interval1, interval2):
    """You are given two intervals,
    where each interval is a pair of integers. For example, interval = (start, end) = (1, 2).
    The given intervals are closed which means that the interval (start, end)
    includes both start and end.
    For each given interval, it is assumed that its start is less or equal its end.
    Your task is to determine whether the length of intersection of these two
    intervals is a prime number.
    Example, the intersection of the intervals (1, 3), (2, 4) is (2, 3)
    which its length is 1, which not a prime number.
    If the length of the intersection is a prime number, return "YES",
    otherwise, return "NO".
    If the two intervals don't intersect, return "NO".


    [input/output] samples:
    intersection((1, 2), (2, 3)) ==> "NO"
    intersection((-1, 1), (0, 4)) ==> "NO"
    intersection((-3, -1), (-5, 5)) ==> "YES"
    """
```

## Canonical solution

```python3
    def is_prime(num):
        if num == 1 or num == 0:
            return False
        if num == 2:
            return True
        for i in range(2, num):
            if num%i == 0:
                return False
        return True

    l = max(interval1[0], interval2[0])
    r = min(interval1[1], interval2[1])
    length = r - l
    if length > 0 and is_prime(length):
        return "YES"
    return "NO"
```

## Tests

```python3
def check(candidate):

    # Check some simple cases
    assert candidate((1, 2), (2, 3)) == "NO"
    assert candidate((-1, 1), (0, 4)) == "NO"
    assert candidate((-3, -1), (-5, 5)) == "YES"
    assert candidate((-2, 2), (-4, 0)) == "YES"

    # Check some edge cases that are easy to work out by hand.
    assert candidate((-11, 2), (-1, -1)) == "NO"
    assert candidate((1, 2), (3, 5)) == "NO"
    assert candidate((1, 2), (1, 2)) == "NO"
    assert candidate((-2, -2), (-3, -2)) == "NO"

```
-/
