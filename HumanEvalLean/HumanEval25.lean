module

public import Std
public import HumanEvalLean.Common.IsPrime

public section

/-! ## Implementation -/

def factorizeAssumingFactorsGE (x : Nat) (bound : Nat) (acc : Array Nat) (h : 2 ≤ bound := by grind) : Array Nat :=
  if x < bound * bound then
    if 1 < x then acc.push x else acc
  else if x % bound = 0 then
    factorizeAssumingFactorsGE (x / bound) bound (acc.push bound)
  else
    factorizeAssumingFactorsGE x (bound + 1) acc
termination_by x + 1 - bound
decreasing_by
  · have : bound ≤ bound * bound := Nat.le_mul_self bound
    have : x / bound < x := Nat.div_lt_self (by grind) (by grind)
    grind
  · have : bound ≤ bound * bound := Nat.le_mul_self bound
    grind [Nat.mod_self]

def factorize (x : Nat) : Array Nat :=
  factorizeAssumingFactorsGE x 2 #[]

/-! ## Tests -/

example : factorize 2 = #[2] := by native_decide
example : factorize 4 = #[2, 2] := by native_decide
example : factorize 8 = #[2, 2, 2] := by native_decide
example : factorize 25 = #[5, 5] := by native_decide
example : factorize 70 = #[2, 5, 7] := by native_decide
example : factorize 57 = #[3, 19] := by native_decide
example : factorize 3249 = #[3, 3, 19, 19] := by native_decide
example : factorize 185193 = #[3, 3, 3, 19, 19, 19] := by native_decide
example : factorize 20577 = #[3, 19, 19, 19] := by native_decide
example : factorize 18 = #[2, 3, 3] := by native_decide

/-! ## Verification -/

/-! ### Helper Predicates -/

def AllDivisorsGE (x bound : Nat) : Prop :=
  ∀ d, 2 ≤ d → d ∣ x → bound ≤ d

def IsSmallestDivisor (d x : Nat) : Prop :=
  2 ≤ d ∧ d ∣ x ∧ AllDivisorsGE x d

/--
The smallest divisor (besides `1`) of a number `x` is a prime number.
-/
@[grind →]
theorem IsSmallestDivisor.isPrime (h : IsSmallestDivisor d x) : IsPrime d := by
  simp only [IsPrime, IsSmallestDivisor] at h ⊢
  refine ⟨h.1, ?_⟩
  intro d' hd'
  have : d' ∣ x := by grind [Nat.dvd_trans]
  have : d' ≤ d := Nat.le_of_dvd (by grind) (by grind)
  by_cases 2 ≤ d'
  · grind [AllDivisorsGE]
  · grind [cases Nat, Nat.zero_dvd]

@[grind .]
theorem AllDivisorsGE.div (h : AllDivisorsGE x bound) (hd : d ∣ x) :
    AllDivisorsGE (x / d) bound := by
  simp only [AllDivisorsGE] at h ⊢
  grind [Nat.div_dvd_of_dvd, Nat.dvd_trans]

@[grind .]
theorem AllDivisorsGE.add_one (h : AllDivisorsGE x bound) (h' : ¬ bound ∣ x) :
    AllDivisorsGE x (bound + 1) := by
  grind [AllDivisorsGE]

/-! ### Verification of the Inner Loop -/

attribute [grind =] Nat.dvd_iff_mod_eq_zero

theorem pairwise_le_factorizeAssumingFactorsGE
    (h_bound : 2 ≤ bound ∧ AllDivisorsGE x bound)
    (h_acc : acc.toList.Pairwise (· ≤ ·) ∧ acc.all (· ≤ bound)) :
    (factorizeAssumingFactorsGE x bound acc).toList.Pairwise (· ≤ ·) := by
  fun_induction factorizeAssumingFactorsGE x bound acc
  · rename_i x bound acc _ _ _
    rw [factorizeAssumingFactorsGE]
    simp only [*, ↓reduceIte, Array.toList_push, List.pairwise_append, Array.mem_toList_iff,
      Array.forall_mem_iff_forall_getElem]
    grind [AllDivisorsGE, Nat.dvd_refl]
  · grind [factorizeAssumingFactorsGE]
  · rename_i ih
    simp only [Array.toList_push, List.pairwise_append, Array.mem_toList_iff,
      Array.forall_mem_iff_forall_getElem] at ih
    grind [factorizeAssumingFactorsGE]
  · grind [factorizeAssumingFactorsGE]

theorem isPrime_of_mem_factorizeAssumingFactorsGE
    (h_bound : 2 ≤ bound ∧ AllDivisorsGE x bound) (h_acc : ∀ d ∈ acc, IsPrime d)
    (hd : d ∈ factorizeAssumingFactorsGE x bound acc) :
    IsPrime d := by
  fun_induction factorizeAssumingFactorsGE x bound acc
  · rename_i x bound _ _ _ _
    rw [factorizeAssumingFactorsGE] at hd
    simp only [↓reduceIte, Array.mem_push, *] at hd
    cases hd
    · grind
    · rw [isPrime_iff_mul_self]
      simp only [*]
      refine ⟨by grind, ?_⟩
      intro d' h_gt h_dvd
      exact Std.lt_of_lt_of_le ‹_› (Nat.mul_self_le_mul_self (by grind [AllDivisorsGE]))
  · grind [factorizeAssumingFactorsGE]
  · rename_i x bound _ _ _ _ _
    have : IsSmallestDivisor bound x := by grind [IsSmallestDivisor]
    grind [factorizeAssumingFactorsGE]
  · grind [factorizeAssumingFactorsGE]

theorem foldl_mul_factorizeAssumingFactorsGE
    (h_bound : 2 ≤ bound ∧ AllDivisorsGE x bound) (hx : 0 < x) :
    (factorizeAssumingFactorsGE x bound acc).foldl (init := 1) (· * ·) =
      acc.foldl (init := 1) (· * ·) * x := by
  fun_induction factorizeAssumingFactorsGE x bound acc
  case case1 => grind [factorizeAssumingFactorsGE]
  case case2 => grind [factorizeAssumingFactorsGE]
  case case3 x bound _ _ _ h_dvd ih =>
    simp only [Nat.div_pos_iff] at ih
    simp only [← Nat.dvd_iff_mod_eq_zero] at h_dvd
    have := Nat.le_mul_self bound
    grind [factorizeAssumingFactorsGE, Nat.dvd_iff_div_mul_eq]
  case case4 => grind [factorizeAssumingFactorsGE]

/-!
### Main results

The following three theorems prove the correctness of `factorize`.
They uniquely determine its behavior for `x > 1` because it has a unique sorted prime factorization.
-/

theorem pairwise_le_factorize :
    (factorize x).toList.Pairwise (· ≤ ·) := by
  apply pairwise_le_factorizeAssumingFactorsGE <;> grind [List.Pairwise.nil, AllDivisorsGE]

theorem isPrime_of_mem_factorize
    (hd : d ∈ factorize x) :
    IsPrime d := by
  apply isPrime_of_mem_factorizeAssumingFactorsGE (hd := hd) <;> grind [AllDivisorsGE]

theorem foldl_mul_factorize (hx : 0 < x) :
    (factorize x).foldl (init := 1) (· * ·) = x := by
  rw [factorize, foldl_mul_factorizeAssumingFactorsGE] <;> grind [AllDivisorsGE]

/-!
## Prompt

```python3
from typing import List


def factorize(n: int) -> List[int]:
    """ Return list of prime factors of given integer in the order from smallest to largest.
    Each of the factors should be listed number of times corresponding to how many times it appeares in factorization.
    Input number should be equal to the product of all factors
    >>> factorize(8)
    [2, 2, 2]
    >>> factorize(25)
    [5, 5]
    >>> factorize(70)
    [2, 5, 7]
    """
```

## Canonical solution

```python3
    import math
    fact = []
    i = 2
    while i <= int(math.sqrt(n) + 1):
        if n % i == 0:
            fact.append(i)
            n //= i
        else:
            i += 1

    if n > 1:
        fact.append(n)
    return fact
```

## Tests

```python3


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    assert candidate(2) == [2]
    assert candidate(4) == [2, 2]
    assert candidate(8) == [2, 2, 2]
    assert candidate(3 * 19) == [3, 19]
    assert candidate(3 * 19 * 3 * 19) == [3, 3, 19, 19]
    assert candidate(3 * 19 * 3 * 19 * 3 * 19) == [3, 3, 3, 19, 19, 19]
    assert candidate(3 * 19 * 19 * 19) == [3, 19, 19, 19]
    assert candidate(3 * 2 * 3) == [2, 3, 3]
```
-/
