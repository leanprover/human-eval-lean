module

import Std.Data.Iterators
import Std.Tactic.Do

open Std

public def isPrime (n : Nat) : Bool :=
  let divisors := (2...<n).iter.takeWhile (fun i => i * i ≤ n) |>.filter (· ∣ n)
  2 ≤ n ∧ divisors.fold (init := 0) (fun count _ => count + 1) = 0

@[expose]
public def IsPrime (n : Nat) : Prop :=
  2 ≤ n ∧ ∀ d : Nat, d ∣ n → d = 1 ∨ d = n

public theorem isPrime_iff {n : Nat} :
    IsPrime n ↔ (2 ≤ n ∧ ∀ d : Nat, d ∣ n → d = 1 ∨ d = n) :=
  Iff.rfl

public theorem two_le_of_isPrime {n : Nat} (h : IsPrime n) :
    2 ≤ n := by
  grind [isPrime_iff]

public theorem isPrime_eq_true_iff {n : Nat} :
    isPrime n = true ↔ 2 ≤ n ∧
        (List.filter (· ∣ n) (List.takeWhile (fun i => i * i ≤ n) (2...n).toList)).length = 0 := by
  simp [isPrime, ← Iter.foldl_toList]

public theorem isPrime_iff_mul_self {n : Nat} :
    IsPrime n ↔ (2 ≤ n ∧ ∀ (a : Nat), 2 ≤ a ∧ a < n → a ∣ n → n < a * a) := by
  rw [IsPrime]
  by_cases hn : 2 ≤ n; rotate_left; grind
  apply Iff.intro
  · grind
  · rintro ⟨hn, h⟩
    refine ⟨hn, fun d hd => ?_⟩
    have : 0 < d := Nat.pos_of_dvd_of_pos hd (by grind)
    have : d ≤ n := Nat.le_of_dvd (by grind) hd
    false_or_by_contra
    by_cases hsq : d * d ≤ n
    · specialize h d
      grind
    · replace h := h (n / d) ?_ ?_; rotate_left
      · have : d ≥ 2 := by grind
        refine ⟨?_, Nat.div_lt_self (n := n) (k := d) (by grind) (by grind)⟩
        false_or_by_contra; rename_i hc
        have : n / d * d ≤ 1 * d := Nat.mul_le_mul_right d (Nat.le_of_lt_succ (Nat.lt_of_not_ge hc))
        grind [Nat.dvd_iff_div_mul_eq]
      · exact Nat.div_dvd_of_dvd hd
      simp only [Nat.not_le] at hsq
      have := Nat.mul_lt_mul_of_lt_of_lt h hsq
      replace : n * n < ((n / d) * d) * ((n / d) * d) := by grind
      rw [Nat.dvd_iff_div_mul_eq] at hd
      rw [hd] at this
      grind

theorem List.takeWhile_eq_filter {P : α → Bool} {xs : List α}
    (h : xs.Pairwise (fun x y => P y → P x)) :
    xs.takeWhile P = xs.filter P := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [takeWhile_cons, filter_cons]
    simp only [pairwise_cons] at h
    split
    · simp [*]
    · simpa [*] using h

public theorem isPrime_eq_true_iff_isPrime {n : Nat} :
    isPrime n ↔ IsPrime n := by
  simp only [isPrime_eq_true_iff]
  by_cases hn : 2 ≤ n; rotate_left
  · grind [IsPrime]
  rw [List.takeWhile_eq_filter]; rotate_left
  · apply Std.Rco.pairwise_toList_le.imp
    intro a b hab hb
    have := Nat.mul_self_le_mul_self hab
    grind
  -- `mem_toList_iff_mem` and `mem_iff` should be simp lemmas
  simp [hn, isPrime_iff_mul_self, Std.Rco.mem_toList_iff_mem, Std.Rco.mem_iff]
