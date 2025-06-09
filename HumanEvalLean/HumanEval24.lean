/-- Computes the largest divisor in O(sqrt n) via trial divison. -/
def largestDivisor (n : Nat) : Nat :=
  go 2
where
  go (i : Nat) : Nat :=
    if h : n < i * i then
      1
    else if n % i = 0 then
      n / i
    else go (i + 1)
  termination_by n - i
  decreasing_by
    have : i < n := by
      match i with
      | 0 => omega
      | 1 => omega
      | i + 2 => exact Nat.lt_of_lt_of_le (Nat.lt_mul_self_iff.2 (by omega)) (Nat.not_lt.1 h)
    omega

example : largestDivisor 3 = 1 := by native_decide
example : largestDivisor 7 = 1 := by native_decide
example : largestDivisor 10 = 5 := by native_decide
example : largestDivisor 100 = 50 := by native_decide
example : largestDivisor 49 = 7 := by native_decide

inductive LargestDivisorSpec (n : Nat) : Nat → Prop
  | one : (∀ j, 2 ≤ j → j * j ≤ n → n % j ≠ 0) → LargestDivisorSpec n 1
  | div {i} : (∀ j, 2 ≤ j → j < i → n % j ≠ 0) → 2 ≤ i → n % i = 0 → LargestDivisorSpec n (n / i)

theorem largestDivisorSpec_go {n i : Nat} (hi : 2 ≤ i)
    (hi' : ∀ j, 2 ≤ j → j < i → n % j ≠ 0) : LargestDivisorSpec n (largestDivisor.go n i) := by
  fun_induction largestDivisor.go n i
  case case1 i hni =>
    rw [largestDivisor.go, dif_pos hni]
    apply LargestDivisorSpec.one
    intro j hj hj'
    apply hi' _ hj
    exact Nat.mul_self_lt_mul_self_iff.1 (Nat.lt_of_le_of_lt hj' hni)
  case case2 i hni hni' =>
    rw [largestDivisor.go, dif_neg hni, if_pos hni']
    exact LargestDivisorSpec.div hi' hi hni'
  case case3 i hni hni' ih =>
    rw [largestDivisor.go, dif_neg hni, if_neg hni']
    apply ih (by omega)
    intro j hj hij
    by_cases hij' : j = i
    · exact hij' ▸ hni'
    · exact hi' _ hj (by omega)

theorem largestDivisorSpec_largestDivisor {n : Nat} :
    LargestDivisorSpec n (largestDivisor n) := by
  rw [largestDivisor]
  exact largestDivisorSpec_go (Nat.le_refl _) (by omega)

theorem Nat.lt_mul_iff {a b : Nat} : a < a * b ↔ 0 < a ∧ 1 < b := by
  obtain (rfl|ha) := Nat.eq_zero_or_pos a
  · simp
  · simp [ha]

theorem helper {n i : Nat} (hn : 1 < n) (h : ∀ j, 2 ≤ j → j < i → n % j ≠ 0) (hi : n % i = 0)
    (k : Nat) (hk : n / i < k) (hk₁ : k < n) : n % k ≠ 0 := by
  intro hk₂
  obtain ⟨d, rfl⟩ := Nat.dvd_of_mod_eq_zero hk₂
  rw [Nat.lt_mul_iff] at hk₁
  have hi₀ : 0 < i := by
    apply Nat.pos_iff_ne_zero.2
    rintro rfl
    simp only [Nat.mod_zero] at hi
    omega
  refine h d ?_ ?_ (by simp)
  · omega
  · rw [Nat.div_lt_iff_lt_mul hi₀] at hk
    exact Nat.lt_of_mul_lt_mul_left hk

theorem similar_helper {n : Nat} (hn : 1 < n) (h : ∀ j, 2 ≤ j → j * j ≤ n → n % j ≠ 0)
    (k : Nat) (hk : n < k * k) (hk₁ : k < n) : n % k ≠ 0 := by
  intro hk₂
  obtain ⟨d, rfl⟩ := Nat.dvd_of_mod_eq_zero hk₂
  rw [Nat.lt_mul_iff] at hk₁
  refine h d ?_ ?_ (by simp)
  · omega
  · refine Nat.mul_le_mul_right _ (Nat.le_of_lt ?_)
    exact Nat.lt_of_mul_lt_mul_left hk

theorem largestDivisorSpec_iff {n i : Nat} (hn : 1 < n) :
    LargestDivisorSpec n i ↔ i < n ∧ n % i = 0 ∧ ∀ j, j < n → n % j = 0 → j ≤ i := by
  constructor
  · rintro (h|h)
    · refine ⟨hn, Nat.mod_one _, fun j hj hj₁ => Nat.not_lt.1 (fun hj₂ => ?_)⟩
      by_cases hj₃ : j * j ≤ n
      · exact h j (by omega) hj₃ hj₁
      · exact similar_helper hn h j (by omega) hj hj₁
    · rename_i i hi hi'
      refine ⟨?_, ?_, fun j hj hj₁ => ?_⟩
      · apply Nat.div_lt_self <;> omega
      · exact Nat.mod_eq_zero_of_dvd (Nat.div_dvd_of_dvd (Nat.dvd_of_mod_eq_zero hi'))
      · exact Nat.not_lt.1 (fun hj₂ => helper hn h hi' j hj₂ hj hj₁)
  · rintro ⟨hi₁, hi₂, hi₃⟩
    obtain (h|rfl|h) := Nat.lt_trichotomy i 1
    · obtain rfl : i = 0 := by omega
      omega
    · refine LargestDivisorSpec.one (fun j hj hj₁ hj₂ => absurd (hi₃ j ?_ hj₂) (by omega))
      exact Nat.lt_of_lt_of_le (Nat.lt_mul_self_iff.2 (by omega)) hj₁
    · obtain ⟨d, rfl⟩ := Nat.dvd_of_mod_eq_zero hi₂
      have hd : 0 < d := Nat.pos_iff_ne_zero.2 (fun hd => by simp [hd] at hn)
      rw (occs := [2]) [← Nat.mul_div_cancel (m := i) (n := d) hd]
      refine LargestDivisorSpec.div ?_ ?_ (by simp)
      · intro j hj₁ hj₂ hj₃
        have : ¬ i * d / j ≤ i := by
          rw [Nat.not_le, Nat.lt_div_iff_mul_lt_of_dvd (by omega) (Nat.dvd_of_mod_eq_zero hj₃)]
          exact Nat.mul_lt_mul_of_pos_left hj₂ (by omega)
        refine absurd (hi₃ _ ?_ ?_) this
        · apply Nat.div_lt_self (by omega) (by omega)
        · exact Nat.mod_eq_zero_of_dvd (Nat.div_dvd_of_dvd (Nat.dvd_of_mod_eq_zero hj₃))
      · rw [Nat.lt_mul_iff] at hi₁
        omega

theorem largestDivisorSpec_unique {n i k : Nat} (hn : 1 < n)
    (hi : LargestDivisorSpec n i) (hk : LargestDivisorSpec n k) : i = k := by
  simp only [largestDivisorSpec_iff hn] at hi hk
  apply Nat.le_antisymm
  · apply hk.2.2 _ hi.1 hi.2.1
  · apply hi.2.2 _ hk.1 hk.2.1

theorem largestDivisor_eq_iff {n i : Nat} (hn : 1 < n) :
    largestDivisor n = i ↔ i < n ∧ n % i = 0 ∧ ∀ j, j < n → n % j = 0 → j ≤ i := by
  rw [← largestDivisorSpec_iff hn]
  refine ⟨?_, fun hi => ?_⟩
  · rintro rfl
    apply largestDivisorSpec_largestDivisor
  · apply largestDivisorSpec_unique hn largestDivisorSpec_largestDivisor hi

/-!
## Prompt

```python3


def largest_divisor(n: int) -> int:
    """ For a given number n, find the largest number that divides n evenly, smaller than n
    >>> largest_divisor(15)
    5
    """
```

## Canonical solution

```python3
    for i in reversed(range(n)):
        if n % i == 0:
            return i
```

## Tests

```python3


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    assert candidate(3) == 1
    assert candidate(7) == 1
    assert candidate(10) == 5
    assert candidate(100) == 50
    assert candidate(49) == 7
```
-/
