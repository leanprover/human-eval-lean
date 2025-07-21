import Std.Tactic.Do

def smallestPrimeFactor (n : Nat) : Nat := Id.run do
  for i in [2:n] do
    if i * i > n then
      break
    if i ∣ n then
      return i
  n

def isMultipleOfKPrimes (a : Nat) (k : Nat) : Bool := Id.run do
  let mut total := 0
  let mut a := a
  for _ in [0:k] do

    if a ≤ 1 then
      return false

    let p := smallestPrimeFactor a
    a := a / p
    total := total + 1

  total == k && a == 1

def isMultiplyPrime (a : Nat) : Bool := isMultipleOfKPrimes a 3

example : isMultiplyPrime 5 = false := by native_decide
example : isMultiplyPrime 30 = true := by native_decide
example : isMultiplyPrime 8 = true := by native_decide
example : isMultiplyPrime 10 = false := by native_decide
example : isMultiplyPrime 125 = true := by native_decide
example : isMultiplyPrime (3 * 5 * 7) = true := by native_decide
example : isMultiplyPrime (3 * 6 * 7) = false := by native_decide
example : isMultiplyPrime (9 * 9 * 9) = false := by native_decide
example : isMultiplyPrime (11 * 9 * 9) = false := by native_decide
example : isMultiplyPrime (11 * 13 * 7) = true := by native_decide

def Nat.IsPrime (n : Nat) : Prop :=
  n > 1 ∧ ∀ m, m ∣ n → m = 1 ∨ m = n

def IsMultiplyPrimeIff (solution : Nat → Bool) : Prop :=
  (a : Nat) → solution a ↔ ∃ (p₁ p₂ p₃ : Nat), p₁ * p₂ * p₃ = a ∧ Nat.IsPrime p₁ ∧ Nat.IsPrime p₂ ∧ Nat.IsPrime p₃

-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/BigOperators/Group/List/Defs.html#List.prod
def List.prod {α} [Mul α] [One α] : List α → α :=
  List.foldr (· * ·) 1

structure PrimeDecomposition (n : Nat) where
  -- Multiset is only available in mathlib, using List instead
  ps : List Nat
  all_prime : ∀ p ∈ ps, p.IsPrime
  is_decomposition : ps.prod = n

def PrimeDecomposition.length (d : PrimeDecomposition n) : Nat := d.ps.length

theorem isMultipleOfKPrimes_primeDecompositionLength (n k : Nat) :
  isMultipleOfKPrimes n k ↔ ∃ (d : PrimeDecomposition n), d.length = k := by


  sorry

theorem primeDecomposition_length_3 (n : Nat) :
  (∃ (p₁ p₂ p₃ : Nat), p₁ * p₂ * p₃ = n ∧ Nat.IsPrime p₁ ∧ Nat.IsPrime p₂ ∧ Nat.IsPrime p₃)
  ↔ ∃ (d : PrimeDecomposition n), d.length = 3 := by
  sorry

theorem isMultiplyPrime_is_correct : IsMultiplyPrimeIff isMultiplyPrime := by
  intro a
  rw [primeDecomposition_length_3 a]
  simp [isMultiplyPrime, isMultipleOfKPrimes_primeDecompositionLength]

/-!
## Prompt

```python3

def is_multiply_prime(a):
    """Write a function that returns true if the given number is the multiplication of 3 prime numbers
    and false otherwise.
    Knowing that (a) is less then 100.
    Example:
    is_multiply_prime(30) == True
    30 = 2 * 3 * 5
    """
```

## Canonical solution

```python3
    def is_prime(n):
        for j in range(2,n):
            if n%j == 0:
                return False
        return True

    for i in range(2,101):
        if not is_prime(i): continue
        for j in range(2,101):
            if not is_prime(j): continue
            for k in range(2,101):
                if not is_prime(k): continue
                if i*j*k == a: return True
    return False
```

## Tests

```python3
def check(candidate):

    assert candidate(5) == False
    assert candidate(30) == True
    assert candidate(8) == True
    assert candidate(10) == False
    assert candidate(125) == True
    assert candidate(3 * 5 * 7) == True
    assert candidate(3 * 6 * 7) == False
    assert candidate(9 * 9 * 9) == False
    assert candidate(11 * 9 * 9) == False
    assert candidate(11 * 13 * 7) == True

```
-/
