module

public import Std
public import HumanEvalLean.Common.IsPrime
import Init.Data.Nat.Coprime
open Std Std.Do

set_option mvcgen.warning false

public section

/-! ## Implementation -/

/--
Given natural numbers `n ≥ 1` and a `d ≥ 2`, returns `n / d ^ i` with the largest possible `i`
for which `d ^ i ∣ n`.
-/
def dividePower (n : { n : Nat // 0 < n }) (d : Nat) (hd : 1 < d) : { n : Nat // 0 < n} :=
  if hd' : d ∣ n.val then
    dividePower ⟨n.val / d, by grind [Nat.eq_zero_of_dvd_of_div_eq_zero]⟩ d hd
  else
    n
termination_by n.val
decreasing_by
  rwa [Nat.div_lt_iff_lt_mul (by grind), Nat.lt_mul_iff_one_lt_right (by grind)]

/--
Returns the largest prime factor of a given number by iteratively dividing away the smallest factor.

Other than the Python reference implementation, this one runs in `O(sqrt(n) + log(n))`.
-/
def largestPrimeFactor (n : Nat) : Nat := Id.run do
  if hn : 0 < n then
    let mut m : { m : Nat // 0 < m } := ⟨n, hn⟩
    let mut mostRecentFactor := 1
    for hd : d in 2...=n do
      if d * d ≤ m then
        if d ∣ m.val then
          mostRecentFactor := d
          m := dividePower m d (by grind [Rcc.mem_iff])
      else
        return max mostRecentFactor m
    return mostRecentFactor
  else
    return 1

/-! ## Tests -/

example : largestPrimeFactor 15 = 5 := by native_decide
example : largestPrimeFactor 27 = 3 := by native_decide
example : largestPrimeFactor 63 = 7 := by native_decide
example : largestPrimeFactor 330 = 11 := by native_decide
example : largestPrimeFactor 13195 = 29 := by native_decide

/-! ## Missing API -/

theorem eq_getElem_append_cons {pref suff : List α} {cur : α} :
    (pref ++ cur :: suff)[pref.length]? = cur := by
  simp

grind_pattern eq_getElem_append_cons => pref ++ cur :: suff
attribute [grind =] Nat.getElem?_toList_rcc
attribute [grind =] Nat.length_toList_rcc

/-!
## Verification

We prove two statements:

* `largestPrimeFactor n` divides `n`.
* `largestPrimeFactor n` a prime and greater than or equal to every prime factor of `n`, given that
  `n > 1`.
-/

theorem dividePower_dvd :
    (dividePower n d hd).val ∣ n.val := by
  fun_induction dividePower n d hd
  · rename_i n h_dvd ih
    have : n.val / d ∣ n.val := Nat.div_dvd_of_dvd h_dvd
    grind [Nat.dvd_trans]
  · apply Nat.dvd_refl

theorem dividePower_le :
    (dividePower n d hd).val ≤ n.val :=
  Nat.le_of_dvd (by grind) dividePower_dvd

theorem dividePower_lt (h : d ∣ n.val) :
    (dividePower n d hd).val < n.val := by
  fun_cases dividePower n d hd
  · exact Nat.lt_of_le_of_lt dividePower_le (Nat.div_lt_self (by grind) (by grind))
  · grind

theorem not_dvd_dividePower :
    ¬ d ∣ (dividePower n d hd).val := by
  fun_induction dividePower n d hd <;> assumption

theorem largestPrimeFactor_dvd :
    largestPrimeFactor n ∣ n := by
  generalize hwp : largestPrimeFactor n = wp
  apply Id.of_wp_run_eq hwp
  mvcgen
  invariants
  · .withEarlyReturn (fun cur ⟨m, factor⟩ => ⌜factor ∣ n ∧ m.val ∣ n⌝) (fun ret ⟨m, factor⟩ => ⌜ret ∣ n⌝)
  with grind [dividePower_dvd, Nat.dvd_trans, Nat.dvd_refl]

theorem Nat.div_div_eq_div_mul' {a b c : Nat} (h : b ∣ a) (h' : c ∣ b) : a / (b / c) = a / b * c := by
  by_cases a = 0
  · simp [*]
  · have : 0 < b := Nat.pos_of_dvd_of_pos h (by grind)
    have : 0 < c := Nat.pos_of_dvd_of_pos h' (by grind)
    rw [Nat.div_eq_iff_eq_mul_left]
    · rw [Nat.mul_assoc, ← Nat.mul_div_assoc, Nat.mul_div_cancel_left, Nat.div_mul_cancel]
      all_goals assumption
    · have : c ≤ b := Nat.le_of_dvd ‹_› ‹_›
      simp only [Nat.div_pos_iff]
      grind
    · refine Nat.dvd_trans ?_ h
      apply Nat.div_dvd_of_dvd
      assumption

theorem dvd_or_dvd_of_dvd_self_div_dividePower {e : Nat} (h : m.val ∣ n)
    (h : e ∣ n / (dividePower m d hd)) (hp : IsPrime e) :
    e ∣ n / m ∨ e ∣ d := by
  fun_induction dividePower m d hd
  · rename_i ih _
    simp only at ih
    specialize ih (by grind [Nat.dvd_trans, Nat.div_dvd_of_dvd]) h
    cases ih
    · rename_i h'
      grind [hp.dvd_mul_iff, Nat.div_div_eq_div_mul']
    · grind
  · grind

/--
Main theorem: `largestPrimeFactor n` is prime and maximal.
Even though the problem description does not require it, we also prove this statement for
`n` prime.

The loop invariant tracks that `factor` divides `n`, all prime divisors of `m` are ≥ the current
trial divisor, and `factor` is the largest prime factor found so far among those already divided
out. -/
theorem isPrime_largestPrimeFactor (h : 1 < n) :
    IsPrime (largestPrimeFactor n) ∧ ∀ d : Nat, d ∣ n → IsPrime d → d ≤ (largestPrimeFactor n) := by
  generalize hwp : largestPrimeFactor n = wp
  apply Id.of_wp_run_eq hwp
  mvcgen
  invariants
  · .withEarlyReturn
    (fun cur ⟨m, mostRecentFactor⟩ =>
      ⌜let i := cur.pos + 2; -- loop variable
        -- At the beginning of the loop, the `mostRecentFactor` variable is less than the loop variable.
        mostRecentFactor < i ∧
        -- The `m` variable is a divisor of `n`.
        m.val ∣ n ∧
        -- Except if `m = n`, `mostRecentFactor` is the largest prime factor of `n / m`.
        (if m.val = n then
            mostRecentFactor = 1
          else
            IsPrime mostRecentFactor ∧ ∀ e : Nat, e ∣ n / m → IsPrime e → e ≤ mostRecentFactor) ∧
        -- Every nontrivial divisor of `m` is at least as large as the loop variable.
        ∀ e : Nat, e ∣ m → e = 1 ∨ i ≤ e⌝)
    (fun ret ⟨m, factor⟩ => ⌜IsPrime ret ∧ ∀ d : Nat, d ∣ n → IsPrime d → d ≤ ret⌝)
  case vc1 pref cur suf _ _ _ m _ _ _ ih =>
    simp only [reduceCtorEq, false_and, exists_false, or_false]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · grind
    · grind
    · grind [dividePower_dvd, Nat.dvd_trans]
    · simp at *
      have : (dividePower m cur (by grind)).val < m.val := dividePower_lt (by grind)
      have : m.val ≤ n := Nat.le_of_dvd ‹0 < n› ih.2.2.1
      rw [if_neg (by grind)]
      constructor
      · rw [IsPrime]
        constructor
        · grind
        · intro d hd
          have := ih.2.2.2.2 d (by grind [Nat.dvd_trans])
          have : d ≤ cur := Nat.le_of_dvd (by grind) hd
          grind
      · intro e he hep
        have := ih.2.2.2.1
        replace he := dvd_or_dvd_of_dvd_self_div_dividePower (by grind) he hep
        split at this
        · have : m = ⟨n, ‹_›⟩ := by grind
          rw [this] at he
          simp only [Nat.div_self ‹0 < n›, Nat.dvd_one] at he
          cases he
          · grind
          · exact Nat.le_of_dvd (by grind) ‹_›
        · replace this := this.2 e
          cases he
          · grind
          · exact Nat.le_of_dvd (by grind) ‹_›
    · simp only [List.Cursor.pos_mk, reduceCtorEq, false_and, and_false, exists_const, or_false] at *
      intro e he
      have : e ≠ cur := by grind [not_dvd_dividePower]
      replace ih := ih.2.2.2.2 e
      grind [dividePower_dvd, Nat.dvd_trans]
  case vc2 pref cur suf _ _ _ _ _ _ _ ih =>
    simp only [List.Cursor.pos_mk, true_and, reduceCtorEq, false_and, exists_const, or_false]
    simp only [List.Cursor.pos_mk, reduceCtorEq, false_and, and_false, exists_const, or_false] at ih
    refine ⟨?_, ?_, ?_, ?_⟩
    · grind
    · grind
    · grind
    · intro e he
      have : e ≠ cur := by grind
      replace ih := ih.2.2.2.2 e
      grind
  case vc4 =>
    simp only [List.Cursor.pos_mk, true_and, reduceCtorEq, false_and, exists_const, or_false]
    refine ⟨?_, ?_, ?_, ?_⟩
    · grind
    · grind [Nat.dvd_refl]
    · grind
    · simp at *
      intro e he
      have : 0 < e := Nat.pos_of_dvd_of_pos he ‹0 < n›
      grind
  case vc5 r _ ih =>
    simp only [List.Cursor.pos_mk, Rcc.length_toList, Nat.size_rcc, Nat.reduceSubDiff,
      true_and] at *
    simp_all only [true_and, reduceCtorEq, false_and, exists_const, or_false]
    have := ih.2.2.2 _ (Nat.dvd_refl _)
    have : r.2.1.val ≤ n := Nat.le_of_dvd ‹0 < n› ih.2.1
    have : r.2.1.val = 1 := by grind
    have := ih.2.2.1
    rw [if_neg (by grind)] at this
    simpa [*] using this
  case vc7 => grind
  -- Early return verification conditions:
  case vc3 pref cur suff _ _ _ m _ hlt ih =>
    simp_all only [Nat.not_le, List.Cursor.pos_mk, reduceCtorEq, false_and, and_false, exists_const,
      or_false, Option.some.injEq, true_and, exists_eq_left', false_or]
    rw [max_eq_if]
    split
    · constructor
      · grind
      · intro d hd hdp
        rw [if_neg (by grind)] at ih
        rw [← show n / m.val * m.val = n from Nat.div_mul_cancel (by grind)] at hd
        rw [hdp.dvd_mul_iff] at hd
        cases hd
        · grind
        · have := ih.2.2.2.2 d ‹_›
          cases this
          · grind
          · have : cur ≤ d := by grind
            have : m.val / d ∣ m.val := Nat.div_dvd_of_dvd ‹_›
            have : m.val / d < cur := by
              rw [Nat.div_lt_iff_lt_mul (by grind)]
              exact Nat.lt_of_lt_of_le hlt (Nat.mul_le_mul_left cur ‹_›)
            have := ih.2.2.2.2 (m.val / d) ‹_›
            cases this
            · rename_i h
              rw [Nat.div_eq_iff_eq_mul_left (by grind) (by grind)] at h
              grind
            · grind
    · constructor
      · rw [isPrime_iff_mul_self]
        constructor
        · grind [IsPrime]
        · intro e he he'
          refine Nat.lt_of_lt_of_le hlt ?_
          have := ih.2.2.2.2 e he'
          exact Nat.mul_self_le_mul_self (by grind)
      · intro d hd hdp
        rw [← show n / m.val * m.val = n from Nat.div_mul_cancel (by grind)] at hd
        rw [hdp.dvd_mul_iff] at hd
        cases hd
        · grind [Nat.div_self, Nat.dvd_one]
        · exact Nat.le_of_dvd (by grind) ‹_›
  case vc6 => grind

/-!
## Prompt

```python3


def largest_prime_factor(n: int):
    """Return the largest prime factor of n. Assume n > 1 and is not a prime.
    >>> largest_prime_factor(13195)
    29
    >>> largest_prime_factor(2048)
    2
    """
```

## Canonical solution

```python3
    def is_prime(k):
        if k < 2:
            return False
        for i in range(2, k - 1):
            if k % i == 0:
                return False
        return True
    largest = 1
    for j in range(2, n + 1):
        if n % j == 0 and is_prime(j):
            largest = max(largest, j)
    return largest
```

## Tests

```python3


METADATA = {}


def check(candidate):
    assert candidate(15) == 5
    assert candidate(27) == 3
    assert candidate(63) == 7
    assert candidate(330) == 11
    assert candidate(13195) == 29

```
-/
