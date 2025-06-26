def fibfib (n : Nat): Nat :=
  match n with
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | (n+3) => fibfib (n+2) + fibfib (n+1) + fibfib n

theorem fibfib_of_three_le {n : Nat} (hn : 3 ≤ n) :
    fibfib n = fibfib (n - 1) + fibfib (n -2) + fibfib (n - 3) := by
  conv =>
    lhs
    unfold fibfib
  cases n with
  | zero => simp at hn
  | succ m =>
    cases m with
    | zero => simp at hn
    | succ n =>
      cases n with
      | zero => simp at hn
      | succ m =>
        simp

def computeFibfib (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | (m + 3) => go (m + 3) 1 0 0 3 where

  go (m prev1 prev2 prev3 curr : Nat) : Nat :=
    if curr ≥ m
    then prev1 + prev2 + prev3
    else go m (prev1 + prev2 + prev3) prev1 prev2 (curr + 1)
  termination_by m - curr

theorem testCase1 : computeFibfib 2 = 1 := by native_decide
theorem testCase2 : computeFibfib 1 = 0 := by native_decide
theorem testCase3 : computeFibfib 5 = 4 := by native_decide
theorem testCase4 : computeFibfib 8 = 24 := by native_decide
theorem testCase5 : computeFibfib 10 = 81 := by native_decide
theorem testCase6 : computeFibfib 12 = 274 := by native_decide
theorem testCase7 : computeFibfib 14 = 927 := by native_decide

theorem computeFibfib_correct (n : Nat) : computeFibfib n = fibfib n := by
  unfold computeFibfib
  unfold fibfib
  cases n with
  | zero => simp[fibfib]
  | succ m =>
    cases m with
    | zero => simp[fibfib]
    | succ n =>
      cases n with
      | zero => simp[fibfib]
      | succ m =>
        simp only
        suffices ∀ (m curr prev1 prev2 prev3 : Nat), 3 ≤ curr → curr ≤ m → prev1 = fibfib (curr - 1) →
          prev2 = fibfib (curr - 2) → prev3 = fibfib (curr - 3) →
            computeFibfib.go m prev1 prev2 prev3 curr = fibfib (m - 1) + fibfib (m - 2) + fibfib (m-3) by
          apply this
          · omega
          · omega
          · simp [fibfib]
          · simp [fibfib]
          · simp [fibfib]
        intro m curr
        induction h : m - curr generalizing curr with
        | zero =>
          simp [Nat.sub_eq_zero_iff_le] at h
          intro prev1 prev2 prev3 hcurr1 hcurr2 hprev1 hprev2 hprev3
          have : curr = m := by omega
          simp [computeFibfib.go, this, hprev1, hprev2, hprev3]
        | succ n ih =>
          intro prev1 prev2 prev3 hcurr1 hcurr2 hprev1 hprev2 hprev3
          unfold computeFibfib.go
          have : ¬ curr ≥ m := by omega
          simp only [ge_iff_le, this, ↓reduceIte]
          apply ih
          · omega
          · omega
          · omega
          · simp [fibfib_of_three_le, hcurr1, hprev1, hprev2, hprev3]
          · simp [hprev1]
          · simp [hprev2]

/-!
## Prompt

```python3


def fibfib(n: int):
    """The FibFib number sequence is a sequence similar to the Fibbonacci sequnece that's defined as follows:
    fibfib(0) == 0
    fibfib(1) == 0
    fibfib(2) == 1
    fibfib(n) == fibfib(n-1) + fibfib(n-2) + fibfib(n-3).
    Please write a function to efficiently compute the n-th element of the fibfib number sequence.
    >>> fibfib(1)
    0
    >>> fibfib(5)
    4
    >>> fibfib(8)
    24
    """
```

## Canonical solution

```python3
    if n == 0:
        return 0
    if n == 1:
        return 0
    if n == 2:
        return 1
    return fibfib(n - 1) + fibfib(n - 2) + fibfib(n - 3)
```

## Tests

```python3


METADATA = {}


def check(candidate):
    assert candidate(2) == 1
    assert candidate(1) == 0
    assert candidate(5) == 4
    assert candidate(8) == 24
    assert candidate(10) == 81
    assert candidate(12) == 274
    assert candidate(14) == 927

```
-/
