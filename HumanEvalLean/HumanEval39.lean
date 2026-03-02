module

public import HumanEvalLean.Common.IsPrime
meta import HumanEvalLean.Common.IsPrime

public section

/-! ## Implementation -/

def primeFib (n : Nat) : Nat :=
  go 0 1 (n - 1)
where
  go (i j n : Nat) : Nat :=
    if isPrime j then
      match n with
      | 0 => j
      | n' + 1 => go j (i + j) n'
    else
      go j (i + j) n
  partial_fixpoint

/-! ## Tests -/

example : primeFib 1 = 2 := by native_decide
example : primeFib 2 = 3 := by native_decide
example : primeFib 3 = 5 := by native_decide
example : primeFib 4 = 13 := by native_decide
example : primeFib 5 = 89 := by native_decide
example : primeFib 6 = 233 := by native_decide
example : primeFib 7 = 1597 := by native_decide
example : primeFib 8 = 28657 := by native_decide
example : primeFib 9 = 514229 := by native_decide
example : primeFib 10 = 433494437 := by native_decide

/-! ## Verification -/

noncomputable def fib (n : Nat) :=
    match n with
    | 0 => 0
    | 1 => 1
    | n + 2 => fib n + fib (n + 1)

theorem fib_pos {n : Nat} (h : 0 < n) :
    0 < fib n := by
  induction n using Nat.strongRecOn
  rename_i n ih
  fun_cases fib n <;> grind

private theorem primeFib_eq_go_fib_fib {n : Nat} :
    primeFib n = primeFib.go (fib 0) (fib 1) (n - 1) := by
  grind [primeFib, fib]

private theorem primeFibGo_fib_fib {i n : Nat} :
    primeFib.go (fib i) (fib (i + 1)) n =
      if isPrime (fib (i + 1)) then
        match n with
        | 0 => fib (i + 1)
        | n' + 1 => primeFib.go (fib (i + 1)) (fib (i + 2)) n'
      else
        primeFib.go (fib (i + 1)) (fib (i + 2)) n := by
  grind [primeFib.go.eq_def, fib]

set_option warn.sorry false in
/--
This lemma is a functional induction principle for `primeFib.go` assuming that
there are infinitely many prime Fibonacci numbers, such that the function terminates.
This is a mathematically hard problem, so we don't provide a proof.
-/
theorem primeFib_induction' (motive : Nat → Nat → Prop)
  (case1 : ∀ (i : Nat), isPrime (fib (i + 1)) = true → motive i 0)
  (case2 : ∀ (i : Nat), isPrime (fib (i + 1)) = true → ∀ (n' : Nat), motive (i + 1) n' → motive i n'.succ)
  (case3 : ∀ (i n : Nat), ¬isPrime (fib (i + 1)) = true → motive (i + 1) n → motive i n) (i n : Nat) :
    motive i n := by
  sorry

/--
`primeFib n` is a prime number.
-/
theorem isPrime_primeFib {n : Nat} :
    IsPrime (primeFib n) := by
  suffices ∀ (i n : Nat), IsPrime (primeFib.go (fib i) (fib (i + 1)) n) by
    grind [primeFib_eq_go_fib_fib]
  intro i n
  induction i, n using primeFib_induction'
  all_goals grind [primeFibGo_fib_fib, isPrime_eq_true_iff_isPrime]

/--
`primeFib n` is a Fibonacci number.
-/
theorem exists_primeFib_eq_fib {n : Nat} :
    ∃ m, primeFib n = fib m := by
  suffices ∀ (i : Nat) (n : Nat), ∃ m, primeFib.go (fib i) (fib (i + 1)) n = fib m by
    obtain ⟨m, hm⟩ := this 0 (n - 1)
    exact ⟨m, by grind [primeFib_eq_go_fib_fib]⟩
  intro i n
  induction i, n using primeFib_induction' <;> grind [primeFibGo_fib_fib]

private theorem le_primeFibGo {i n : Nat} :
    fib (i + 1) ≤ primeFib.go (fib i) (fib (i + 1)) n := by
  induction i, n using primeFib_induction'
  all_goals grind [fib, primeFibGo_fib_fib]

/--
`primeFib i` is strictly monotone in `i`,
starting from `i = 1` (`i = 0` is not considered a valid input by the problem description),
-/
theorem primeFib_mono {i j : Nat} (hi : 0 < i) (hj : i < j) :
    primeFib i < primeFib j := by
  suffices ∀ (i n : Nat), primeFib.go (fib i) (fib (i + 1)) n < primeFib.go (fib i) (fib (i + 1)) (n + 1) by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hj
    induction k
    · specialize this 0 (i - 1)
      grind [primeFib_eq_go_fib_fib]
    · grind [primeFib_eq_go_fib_fib]
  intro i n
  induction i, n using primeFib_induction'
  all_goals grind [primeFibGo_fib_fib, le_primeFibGo, fib, fib_pos,
    isPrime_eq_true_iff_isPrime, IsPrime]

/--
Every prime Fibonacci number is contained in the image of `primeFib`.
-/
theorem exists_eq_primeFib_of_isPrime_fib {n : Nat} (h : IsPrime (fib n)) :
    ∃ m, primeFib m = fib n := by
  suffices ∀ (i : Nat) (hi : i < n), ∃ m, primeFib.go (fib i) (fib (i + 1)) m = fib n by
    have hn : 0 < n := by grind [IsPrime, fib]
    obtain ⟨m, hm⟩ := this 0 (by grind)
    exact ⟨m + 1, by grind [primeFib_eq_go_fib_fib]⟩
  intro i hi
  induction h : n - i - 1 generalizing i
  · exact ⟨0, by grind [primeFibGo_fib_fib, isPrime_eq_true_iff_isPrime]⟩
  · rename_i k ih
    obtain ⟨m, hm⟩ := ih (i + 1) (by grind) (by grind)
    simp +singlePass only [primeFibGo_fib_fib]
    split
    · exact ⟨m + 1, by grind⟩
    · exact ⟨m, by grind⟩

/-!
## Prompt

```python3


def prime_fib(n: int):
    """
    prime_fib returns n-th number that is a Fibonacci number and it's also prime.
    >>> prime_fib(1)
    2
    >>> prime_fib(2)
    3
    >>> prime_fib(3)
    5
    >>> prime_fib(4)
    13
    >>> prime_fib(5)
    89
    """
```

## Canonical solution

```python3
    import math

    def is_prime(p):
        if p < 2:
            return False
        for k in range(2, min(int(math.sqrt(p)) + 1, p - 1)):
            if p % k == 0:
                return False
        return True
    f = [0, 1]
    while True:
        f.append(f[-1] + f[-2])
        if is_prime(f[-1]):
            n -= 1
        if n == 0:
            return f[-1]
```

## Tests

```python3


METADATA = {}


def check(candidate):
    assert candidate(1) == 2
    assert candidate(2) == 3
    assert candidate(3) == 5
    assert candidate(4) == 13
    assert candidate(5) == 89
    assert candidate(6) == 233
    assert candidate(7) == 1597
    assert candidate(8) == 28657
    assert candidate(9) == 514229
    assert candidate(10) == 433494437

```
-/
