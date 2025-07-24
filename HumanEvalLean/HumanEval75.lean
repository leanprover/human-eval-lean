import Std.Tactic.Do
import Init.Data.Nat.Dvd

open Std Do

def smallestPrimeFactor (n : Nat) : Nat :=
  go 2
where
  go (i : Nat) : Nat :=
    if h : n < i * i then
      n
    else if h2 : i ∣ n then
      i
    else
      go (i + 1)
  termination_by n - i
  decreasing_by
    have : i < n := by
      match i with
      | 0 => omega
      | 1 => omega
      | i + 2 => exact Nat.lt_of_lt_of_le (Nat.lt_mul_self_iff.2 (by omega)) (Nat.not_lt.1 h)
    omega

def Nat.IsPrime (n : Nat) : Prop :=
  n > 1 ∧ ∀ m, m ∣ n → m = 1 ∨ m = n

theorem smallestPrimeFactor_div_n (n : Nat) (hn : 1 < n) : smallestPrimeFactor n ∣ n := by sorry

theorem smallestPrimeFactor_isPrime {n : Nat} (hn : 1 < n) : Nat.IsPrime $ smallestPrimeFactor n := by sorry

def isMultipleOfKPrimes (n : Nat) (k : Nat) : Bool :=
  if hn₀ : n = 0 then
    false
  else if hk : k = 0 then
      n = 1
  else if hn₁ : n = 1 then
    false
  else
    let p := smallestPrimeFactor n
    isMultipleOfKPrimes (n / p) (k - 1)
  termination_by k
  decreasing_by
    omega

theorem isMultipleOfKPrimes_zero (k : Nat) : isMultipleOfKPrimes 0 k = false := by
  simp [isMultipleOfKPrimes]

def isMultiplyPrime (n : Nat) : Bool := isMultipleOfKPrimes n 3

example : isMultiplyPrime 0 = false := by native_decide
example : isMultiplyPrime 1 = false := by native_decide
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

theorem Nat.isPrime_ne_zero (hp : Nat.IsPrime p) : p ≠ 0 := by
  intro h
  have h2 : 2 ∣ p := by simp [h]
  apply Or.elim (hp.right 2 h2)
  trivial
  rw [h]
  trivial

theorem Nat.IsPrime.zero_lt (hp : Nat.IsPrime p) : 0 < p := by match p with
  | p + 1 => simp
  | 0 => simp [Nat.IsPrime] at hp

theorem Nat.IsPrime.two_le (hp : Nat.IsPrime p) : 2 ≤ p := by sorry

def IsMultiplyPrimeIff (solution : Nat → Bool) : Prop :=
  (a : Nat) → solution a ↔ ∃ (p₁ p₂ p₃ : Nat), p₁ * p₂ * p₃ = a ∧ Nat.IsPrime p₁ ∧ Nat.IsPrime p₂ ∧ Nat.IsPrime p₃

-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/BigOperators/Group/List/Defs.html#List.prod
def List.prod {α} [Mul α] [One α] : List α → α :=
  List.foldr (· * ·) 1

theorem List.prod_head_eq_mul {α} [Mul α] [One α] (a : α) (l : List α) : (a :: l).prod = a * l.prod := by
  simp [List.prod]

theorem List.prod_ne_zero (l : List Nat) (h : ∀ x ∈ l, x ≠ 0) : l.prod ≠ 0 := by
  induction l with
  | nil => simp [List.prod]
  | cons x xs ih =>
    have : (x :: xs).prod = x * xs.prod := by simp [List.prod]
    rw [this]
    apply Nat.mul_ne_zero
    · apply h x; simp
    · apply ih; intro x1 hx; apply h; simp [hx]

theorem List.prod_nil {α} [Mul α] [One α] : ([] : List α).prod = 1 :=
  rfl

structure PrimeDecomposition (n : Nat) where
  -- Multiset is only available in mathlib, using List instead
  ps : List Nat
  all_prime : ∀ p ∈ ps, p.IsPrime
  is_decomposition : ps.prod = n

def PrimeDecomposition.length (d : PrimeDecomposition n) : Nat := d.ps.length

def PrimeDecomposition.push (d : PrimeDecomposition n) (p : Nat) (hp : p.IsPrime) : PrimeDecomposition (n * p) :=
  ⟨p :: d.ps,
  by
    intro p1 h
    simp at h
    apply Or.elim h
    · intro t; rw[t]; exact hp
    · exact (d.all_prime p1 ·),
  by
    simp [List.prod_head_eq_mul]
    rw [d.is_decomposition, Nat.mul_comm]
  ⟩

theorem List.prod_cons (a : α) (l : List α) [Mul α] [One α] : (a :: l).prod = a * l.prod := by
  simp [List.prod]


theorem List.dvd_prod {l : List Nat} {n : Nat} (h : n ∈ l) : n ∣ l.prod := by
  induction l with
  | nil => contradiction
  | cons head tail ih =>
    rw [List.prod_cons]
    if hd : head = n then
      simp [hd, Nat.dvd_mul_right]
    else
      have ht : n ∈ tail := by
          simp at h
          apply Or.elim h
          intro x; symm at x; contradiction
          simp
      exact Nat.dvd_mul_left_of_dvd (ih ht) head

theorem List.prod_erase (l : List Nat) (p : Nat) (h : p ∈ l) (h1 : 0 < p) : (l.erase p).prod = l.prod / p := by
  induction l with
  | nil => contradiction
  | cons head tail ih =>
    if hp : head = p then
      simp [hp, List.prod, Nat.mul_comm p, Nat.mul_div_cancel _ h1]
    else
      simp [List.prod_cons, hp]
      have ht : p ∈ tail := by
        simp at h
        apply Or.elim h
        intro x; symm at x; contradiction
        simp
      rw [ih ht, ← Nat.mul_div_assoc]
      exact List.dvd_prod ht

def PrimeDecomposition.erase_cons (d : PrimeDecomposition n) : PrimeDecomposition (n / d.ps.headD 1) := by
  match d.ps with
  | [] => sorry
  | head :: tail => sorry

theorem PrimeDecomposition.prime_mem (d : PrimeDecomposition n) (hp : p.IsPrime) (hd : p ∣ n) : p ∈ d.ps := by
  let ⟨ps, ha, hb⟩ := d
  induction ps generalizing n with
  | nil =>
    simp [List.prod] at hb
    symm at hb
    rw [hb] at hd
    let c := Nat.le_trans (hp.two_le) (Nat.le_of_dvd (by simp) hd)
    contradiction
  | cons head tail ih =>
    simp
    simp at ih
    if hp : p = head then
      simp [hp]
    else
      simp [hp]
      have hh : d.ps.headD 1 = head := by sorry
      let ih := ih d.erase_cons
      rw [hh] at ih
      have hd : p ∣ n / head := by sorry
      have hpp : ∀ p ∈ tail, p.IsPrime := by sorry
      apply ih hd hpp
      simp [List.prod_cons] at hb
      sorry

def PrimeDecomposition.erase (d : PrimeDecomposition n) (p : Nat) (hp : p.IsPrime) (hd : p ∣ n) : PrimeDecomposition (n / p) :=
  ⟨d.ps.erase p,
    fun p1 h1 => d.all_prime p1 (List.mem_of_mem_erase h1),
    by rw [List.prod_erase d.ps p (PrimeDecomposition.prime_mem d hp hd) hp.zero_lt]; simp [d.is_decomposition]⟩

theorem PrimeDecomposition.push_length_eq_length_plus_one {d : PrimeDecomposition n} : (d.push p hp).length = d.length + 1 := by
  simp [PrimeDecomposition.push, PrimeDecomposition.length]

theorem PrimeDecomposition.erase_length_eq_length_minus_one (d : PrimeDecomposition n) (p : Nat) (hp : p.IsPrime) (hd : p ∣ n) : (d.erase p hp hd).length = d.length - 1 := by
  simp [PrimeDecomposition.length, PrimeDecomposition.erase]
  rw [List.length_erase_of_mem (PrimeDecomposition.prime_mem d hp hd)]

def PrimeDecomposition.one : PrimeDecomposition 1 := ⟨[], by simp, (by simp [List.prod_nil])⟩

theorem PrimeDecomposition.zero_does_not_exist (d : PrimeDecomposition 0) : False := by
  apply List.prod_ne_zero d.ps
  · intro x h
    exact Nat.isPrime_ne_zero (d.all_prime x h)
  exact d.is_decomposition

theorem PrimeDecomposition.one_unique (d : PrimeDecomposition 1) : d = PrimeDecomposition.one := by
  simp [PrimeDecomposition.one]
  if h : d.ps = [] then
    sorry
  else
    sorry

theorem PrimeDecomposition.one_length_eq_zero (d : PrimeDecomposition 1) : d.length = 0 := by
  rw [PrimeDecomposition.one_unique d]
  simp [PrimeDecomposition.length, PrimeDecomposition.one]

theorem isMultipleOfKPrimes_primeDecompositionLength {n k : Nat} :
  isMultipleOfKPrimes n k ↔ ∃ (d : PrimeDecomposition n), d.length = k := by
    if hn₀ : n = 0 then
      rw [hn₀]
      simp [isMultipleOfKPrimes]
      intro x h
      exact PrimeDecomposition.zero_does_not_exist x
    else
      unfold isMultipleOfKPrimes
      simp [hn₀]
      if hk : k = 0 then
        simp [hk]
        constructor
        · intro h1
          rw [h1]
          exact ⟨PrimeDecomposition.one, by simp [PrimeDecomposition.one_length_eq_zero]⟩
        · intro ⟨d, hd⟩
          simp [PrimeDecomposition.length] at hd
          symm
          let x := d.is_decomposition
          simp [hd, List.prod] at x
          trivial
      else
        simp [hk]
        constructor
        · intro ⟨hn₁, hrec⟩
          let ⟨d, hd⟩ := isMultipleOfKPrimes_primeDecompositionLength.mp hrec
          have hn_ge_1 : 1 < n := by match n with
            | 0 => trivial
            | 1 => trivial
            | n + 2 => simp
          let d₁ := d.push (smallestPrimeFactor n) (smallestPrimeFactor_isPrime hn_ge_1)
          rw [← Nat.div_mul_cancel (smallestPrimeFactor_div_n n hn_ge_1)]
          suffices d₁.length = k by
            exact ⟨d₁, by simp [this]⟩
          rw [PrimeDecomposition.push_length_eq_length_plus_one, hd]
          have hk₀ : 1 ≤ k := by match k with
            | 0 => contradiction
            | k + 1 => simp
          rw [← Nat.sub_add_comm hk₀, Nat.add_sub_cancel]
        · intro ⟨d, hd⟩
          have hn_ge_1 : 1 < n := by match n with
            | 0 => trivial
            | 1 =>
              exfalso
              rw [PrimeDecomposition.one_length_eq_zero d] at hd
              symm at hd
              contradiction
            | n + 2 => simp
          constructor
          · intro h1
            revert hd d
            rw [h1]
            intro d hd
            rw [PrimeDecomposition.one_length_eq_zero d] at hd
            symm at hd
            contradiction
          · let d2 := d.erase (smallestPrimeFactor n) (smallestPrimeFactor_isPrime hn_ge_1) (smallestPrimeFactor_div_n n hn_ge_1)
            suffices d2.length = k - 1 by
              exact isMultipleOfKPrimes_primeDecompositionLength.mpr ⟨d2, by simp [this]⟩
            let x := PrimeDecomposition.erase_length_eq_length_minus_one d (smallestPrimeFactor n) (smallestPrimeFactor_isPrime hn_ge_1) (smallestPrimeFactor_div_n n hn_ge_1)
            rw [x, hd]

theorem List.prod_3_mul {a b c : Nat} : [a, b, c].prod = a * b * c := by
  simp [List.prod]
  rw [Nat.mul_assoc]

theorem primeDecomposition_length_3 (n : Nat) :
  (∃ (p₁ p₂ p₃ : Nat), p₁ * p₂ * p₃ = n ∧ Nat.IsPrime p₁ ∧ Nat.IsPrime p₂ ∧ Nat.IsPrime p₃)
  ↔ ∃ (d : PrimeDecomposition n), d.length = 3 := by
  constructor
  · intro ⟨a, b, c, ⟨h, ha, hb, hc⟩⟩
    let d := PrimeDecomposition.one.push a ha |>.push b hb |>.push c hc

    suffices ∃ d : PrimeDecomposition (1 * a * b * c), d.length = 3 by
      have h1 : 1 * a * b * c = n := by simp [h]
      rw [h1] at this
      exact this

    suffices d.length = 3 by
      exact ⟨d, this⟩

    repeat rw [PrimeDecomposition.push_length_eq_length_plus_one]
    rw [PrimeDecomposition.one_length_eq_zero]
  · intro ⟨⟨ps, hp, ha⟩, hd⟩
    simp [PrimeDecomposition.length] at hd
    match ps with
    | [] => contradiction
    | a₁ :: rest => match rest with
      | [] => simp at hd
      | a₂ :: rest => match rest with
        | [] => simp at hd
        | a₃ :: rest =>
          simp at hd
          rw [hd] at ha
          suffices a₁ * a₂ * a₃ = n ∧ a₁.IsPrime ∧ a₂.IsPrime ∧ a₃.IsPrime by
            exact ⟨a₁, a₂, a₃, this⟩
          rw [List.prod_3_mul] at ha
          constructor
          · exact ha
          constructor
          · let t := hp a₁
            simp at t
            trivial
          constructor
          · let t := hp a₂
            simp at t
            trivial
          · let t := hp a₃
            simp at t
            trivial

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
