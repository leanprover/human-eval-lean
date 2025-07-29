import Std.Data.HashSet
import HumanEvalLean.ProvedElsewhere

set_option grind.warning false

def Nat.Prime (p : Nat) : Prop := 2 ≤ p ∧ ∀ (m : Nat), m < p → 2 ≤ m → ¬ m ∣ p

def Nat.relativePrime (p n : Nat) : Prop := 2 ≤ p ∧ ∀ (m : Nat), m < p → m < n → 2 ≤ m → ¬ m ∣ p

theorem Nat.relativePrimeTo2 (p : Nat) (hp : 2 ≤ p) : Nat.relativePrime p 2 := by
  simp [Nat.relativePrime, hp]
  grind

theorem Nat.relativePrime_succ (p n : Nat) (hn₁ : 2 ≤ n) :
  Nat.relativePrime p n ∧ p % n ≠ 0 ↔ Nat.relativePrime p (n + 1) := by
  simp [relativePrime]
  constructor
  · intro h
    rcases h with ⟨h₁, h₃⟩
    rcases h₁ with ⟨h₁, h₂⟩
    apply And.intro h₁
    intro m hmp hmn h2m
    have : m < n ∨ m = n := by grind
    cases this with
    | inl h' =>
      apply h₂ m hmp h' h2m
    | inr h' =>
      simp [h', Nat.dvd_iff_mod_eq_zero, h₃]
  · intro h
    rcases h with ⟨h₁, h₂⟩
    constructor
    · apply And.intro h₁
      intro m hmp hmn h2m
      apply h₂ m hmp (by omega) h2m
    · rw [← Nat.dvd_iff_mod_eq_zero]
      sorry

def fillSieve (n : Nat) : Std.HashSet Nat := Std.HashSet.ofList (List.range' 2 (n-2))

theorem mem_fillSieve {n m : Nat} : m ∈ fillSieve n ↔ m ≥ 2 ∧ m < n := by
  simp only [fillSieve, Std.HashSet.mem_ofList, List.contains_eq_mem, List.mem_range'_1,
    Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq, ge_iff_le, and_congr_right_iff]
  omega

def eratosthenes_sieve (n : Nat) : List Nat :=
  if n < 2
  then []
  else
    let sieve := fillSieve n
    (eratosthenes_sieve.go n sieve 2).toList.mergeSort
where
  go (n : Nat) (sieve : Std.HashSet Nat) (curr : Nat) :=
    if curr < n
    then
      if curr ∈ sieve
      then eratosthenes_sieve.go n (sieve.filter (fun x => (x ≤ curr ∨ x % curr != 0))) (curr + 1)
      else eratosthenes_sieve.go n sieve (curr + 1)
    else
      sieve

theorem mem_eratosthenes_sieve_iff_prime_and_less_than (n m : Nat) :
    m ∈ eratosthenes_sieve n ↔ m.Prime ∧ m < n := by
  simp only [eratosthenes_sieve]
  split
  · admit
  · simp only [List.mem_mergeSort, Std.HashSet.mem_toList]
    suffices ∀ (n curr : Nat) (sieve : Std.HashSet Nat), (∀ (k : Nat), 2 ≤ k → (k ∈ sieve ↔ Nat.relativePrime k curr ∧ k < n)) → curr ≤ n →
    (m ∈ eratosthenes_sieve.go n sieve curr ↔ m.Prime ∧ m < n) by
      apply this n 2 (fillSieve n)
      · intro k hk
        simp [mem_fillSieve, Nat.relativePrimeTo2, hk]
      · omega
    intro n curr sieve h₁ h₂
    fun_induction eratosthenes_sieve.go with
    | case1 sieve curr h₄ h₅ ih =>
      unfold eratosthenes_sieve.go
      sorry
    | case2 sieve curr h₄ h₅ ih =>
      sorry
    | case3 sieve curr h =>
      unfold eratosthenes_sieve.go
      simp [h]
      sorry

theorem testCase1 : eratosthenes_sieve 5 = [2, 3] := by native_decide
theorem testCase2 : eratosthenes_sieve 6 = [2, 3, 5] := by native_decide
theorem testCase3 : eratosthenes_sieve 7 = [2, 3, 5] := by native_decide
theorem testCase4 : eratosthenes_sieve 10 = [2, 3, 5, 7] := by native_decide
theorem testCase5 : eratosthenes_sieve 0 = [] := by native_decide
theorem testCase6 : eratosthenes_sieve 22 = [2, 3, 5, 7, 11, 13, 17, 19] := by native_decide
theorem testCase7 : eratosthenes_sieve 1 = [] := by native_decide
theorem testCase8 : eratosthenes_sieve 18 = [2, 3, 5, 7, 11, 13, 17] := by native_decide
theorem testCase9 : eratosthenes_sieve 47 = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43] := by
    native_decide
theorem testCase10 : eratosthenes_sieve 101 = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43,
        47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97] := by
    native_decide

/-!
## Prompt

```python3

def count_up_to(n):
    """Implement a function that takes an non-negative integer and returns an array of the first n
    integers that are prime numbers and less than n.
    for example:
    count_up_to(5) => [2,3]
    count_up_to(11) => [2,3,5,7]
    count_up_to(0) => []
    count_up_to(20) => [2,3,5,7,11,13,17,19]
    count_up_to(1) => []
    count_up_to(18) => [2,3,5,7,11,13,17]
    """
```

## Canonical solution

```python3
    primes = []
    for i in range(2, n):
        is_prime = True
        for j in range(2, i):
            if i % j == 0:
                is_prime = False
                break
        if is_prime:
            primes.append(i)
    return primes

```

## Tests

```python3
def check(candidate):

    assert candidate(5) == [2,3]
    assert candidate(6) == [2,3,5]
    assert candidate(7) == [2,3,5]
    assert candidate(10) == [2,3,5,7]
    assert candidate(0) == []
    assert candidate(22) == [2,3,5,7,11,13,17,19]
    assert candidate(1) == []
    assert candidate(18) == [2,3,5,7,11,13,17]
    assert candidate(47) == [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43]
    assert candidate(101) == [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]

```
-/
