module

public import Std
public import HumanEvalLean.Common.IsPrime
import Init.Data.Nat.Coprime
open Std Std.Do

set_option mvcgen.warning false

public section

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
-/
def largestPrimeFactor (n : Nat) : Nat := Id.run do
  if hn : 0 < n then
    let mut m : { m : Nat // 0 < m } := ⟨n, hn⟩
    let mut mostRecentFactor := 1
    for hd : d in 2...=n do
      if d ∣ m.val then
        mostRecentFactor := d
        m := dividePower m d (by grind [Rcc.mem_iff])
    return mostRecentFactor
  else
    return 1

theorem eq_getElem_append_cons {pref suff : List α} {cur : α} :
    (pref ++ cur :: suff)[pref.length]? = cur := by
  simp

grind_pattern eq_getElem_append_cons => pref ++ cur :: suff
attribute [grind =] Nat.getElem?_toList_rcc
attribute [grind =] Nat.length_toList_rcc

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

theorem not_dvd_dividePower_dvd :
    ¬ d ∣ (dividePower n d hd).val := by
  fun_induction dividePower n d hd <;> assumption

theorem largestPrimeFactor_dvd :
    largestPrimeFactor n ∣ n := by
  generalize hwp : largestPrimeFactor n = wp
  apply Id.of_wp_run_eq hwp
  mvcgen
  invariants
  · ⇓⟨cur, m, factor⟩ => ⌜factor ∣ n ∧ m.val ∣ n⌝
  with grind [dividePower_dvd, Nat.dvd_trans, Nat.dvd_refl]

theorem IsPrime.dvd_mul_iff (h : IsPrime d) :
    d ∣ a * b ↔ d ∣ a ∨ d ∣ b := by
  constructor
  · by_cases d ∣ a
    · grind
    · have : Nat.Coprime d a := by grind [IsPrime, Nat.gcd_dvd_left, Nat.gcd_dvd_right]
      exact Or.inr ∘ this.dvd_of_dvd_mul_left
  · grind

theorem or_of_dvd_self_div_dividePower {e : Nat} (h : m.val ∣ n)
    (h : e ∣ n / (dividePower m d hd)) (hp : IsPrime e) :
    e ∣ n / m ∨ e ∣ d := by
  fun_induction dividePower m d hd
  · rename_i ih _
    simp only at ih
    specialize ih (by grind [Nat.dvd_trans, Nat.div_dvd_of_dvd]) h
    cases ih
    · rename_i h'
      have (a b c : Nat) (h : b ∣ a) (h' : c ∣ b) : a / (b / c) = a / b * c := by
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
      grind [hp.dvd_mul_iff]
    · grind
  · grind

theorem isPrime_largestPrimeFactor (h : 1 < n) :
    IsPrime (largestPrimeFactor n) ∧ ∀ d : Nat, d ∣ n → IsPrime d → d ≤ (largestPrimeFactor n) := by
  generalize hwp : largestPrimeFactor n = wp
  apply Id.of_wp_run_eq hwp
  mvcgen
  invariants
  · ⇓⟨cur, m, factor⟩ =>
      ⌜let i := cur.pos + 2;
        factor < i ∧
          m.val ∣ n ∧
          (if m.val = n then factor = 1 else IsPrime factor ∧ ∀ e : Nat, e ∣ n / m → IsPrime e → e ≤ factor) ∧
          ∀ e : Nat, e ∣ m → e = 1 ∨ i ≤ e⌝
  case vc1 pref cur suf _ _ m _ _ ih =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · grind
    · grind [dividePower_dvd, Nat.dvd_trans]
    · simp at *
      have : (dividePower m cur (by grind)).val < m.val := dividePower_lt (by grind)
      have : m.val ≤ n := Nat.le_of_dvd ‹0 < n› ih.2.1
      rw [if_neg (by grind)]
      constructor
      · rw [IsPrime]
        constructor
        · grind
        · intro d hd
          have := ih.2.2.2 d (by grind [Nat.dvd_trans])
          have : d ≤ cur := Nat.le_of_dvd (by grind) hd
          grind
      · intro e he hep
        have := ih.2.2.1
        replace he := or_of_dvd_self_div_dividePower (by grind) he hep
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
    · intro e he
      have : e ≠ cur := by grind [not_dvd_dividePower_dvd]
      replace ih := ih.2.2.2 e
      grind [dividePower_dvd, Nat.dvd_trans]
  case vc2 pref cur suf _ _ _ _ _ ih =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · grind
    · grind
    · grind
    · intro e he
      have : e ≠ cur := by grind
      replace ih := ih.2.2.2 e
      grind
  case vc3 =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · grind
    · grind [Nat.dvd_refl]
    · grind
    · simp at *
      intro e he
      have : 0 < e := Nat.pos_of_dvd_of_pos he ‹0 < n›
      grind
  case vc4 r ih =>
    simp at *
    have := ih.2.2.2 _ (Nat.dvd_refl _)
    have : r.fst.val ≤ n := Nat.le_of_dvd ‹0 < n› ih.2.1
    have : r.fst.val = 1 := by grind
    have := ih.2.2.1
    rw [if_neg (by grind)] at this
    simpa [*] using this
  case vc5 => grind

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
