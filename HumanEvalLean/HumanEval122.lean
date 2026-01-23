module

import Std
import all Init.Data.Repr

open Std

/-!
## Implementation
-/

-- As soon as there is enough API, use `toString x`
def intToString (x : Int) : String :=
  match x with
    | Int.ofNat m => String.ofList (Nat.toDigits 10 m)
    | Int.negSucc m => "-" ++ (String.ofList (Nat.toDigits 10 m.succ))

def addElements (xs : Array Int) (k : Nat) : Int :=
  xs.iter.take k
    |>.filter (fun x => (toString x).length ≤ 2)
    |>.fold (init := 0) (· + ·)

/-!
## Tests
-/

example : addElements #[1,-2,-3,41,57,76,87,88,99] 3 = -4 := by native_decide
example : addElements #[111,121,3,4000,5,6] 2 = 0 := by native_decide
example : addElements #[11,21,3,90,5,6,7,8,9] 4 = 125 := by native_decide
example : addElements #[111,21,3,4000,5,6,7,8,9] 4 = 24 := by native_decide
example : addElements #[1] 1 = 1 := by native_decide

/-!
## Missing API
-/

theorem intToString_of_nonneg {x : Int} (h : 0 ≤ x) :
    intToString x = String.ofList (Nat.toDigits 10 x.toNat) := by
  grind [intToString]

theorem intToString_of_neg {x : Int} (h : x < 0) :
    intToString x = "-" ++ intToString (- x) := by
  rw [intToString.eq_def]
  split <;> grind [intToString_of_nonneg]

theorem toDigits_zero :
    Nat.toDigits 10 0 = ['0'] := by
  decide

theorem toDigits_of_lt_ten {n : Nat} (h : n < 10) :
    Nat.toDigits 10 n = [Nat.digitChar n] := by
  revert n; decide

theorem toDigitsCore_eq_append {fuel : Nat} {n : Nat} {acc : List Char} (hf : n < fuel) :
    Nat.toDigitsCore 10 fuel n acc = Nat.toDigitsCore 10 fuel n [] ++ acc := by
  induction fuel generalizing n acc <;> grind [Nat.toDigitsCore]

theorem toDigitsCore_eq_toDigitsCore {fuel fuel' : Nat} {n : Nat} {acc : List Char} (hf : n < fuel) (hf' : n < fuel') :
    Nat.toDigitsCore 10 fuel n acc = Nat.toDigitsCore 10 fuel' n [] ++ acc := by
  induction fuel generalizing n acc fuel'
  · grind [Nat.toDigitsCore]
  · obtain ⟨fuel', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := fuel') (by grind)
    grind [Nat.toDigitsCore, toDigitsCore_eq_append]

theorem toDigitsCore_eq_toDigits {fuel : Nat} {n : Nat} {acc : List Char} (hf : n < fuel) :
    Nat.toDigitsCore 10 fuel n acc = Nat.toDigits 10 n ++ acc := by
  grind [Nat.toDigits, toDigitsCore_eq_toDigitsCore]

theorem toDigits_eq_if {n : Nat} :
    Nat.toDigits 10 n = if n < 10 then [Nat.digitChar n] else Nat.toDigits 10 (n / 10) ++ [Nat.digitChar (n % 10)] := by
  grind [Nat.toDigits, Nat.toDigitsCore, toDigitsCore_eq_toDigits]

theorem toDigits_of_ten_le {n : Nat} (h : 10 ≤ n) :
    Nat.toDigits 10 n = (Nat.toDigits 10 (n / 10)) ++ [Nat.digitChar (n % 10)] := by
  grind [toDigits_eq_if]

theorem intToString_zero :
    intToString 0 = "0" := by
  decide

theorem length_toDigits_le_iff {n k : Nat} (h : 0 < k) :
    (Nat.toDigits 10 n).length ≤ k ↔ n < 10 ^ k := by
  match k with
  | 0 => contradiction
  | k + 1 => induction k generalizing n <;> grind [toDigits_eq_if]

/-- arithmetic characterization of an integer's length as a string -/
theorem length_toString_le_two_iff {x : Int} :
    (intToString x).length ≤ 2 ↔ x ∈ (-9)...=99 := by
  simp [intToString, Std.Rcc.mem_iff]
  split
  · grind [length_toDigits_le_iff, String.length_ofList]
  · have : "-".length = 1 := by decide
    simp only [String.length_append, this, Nat.reduceLeDiff, ← Nat.le_sub_iff_add_le']
    grind [length_toDigits_le_iff, String.length_ofList]

theorem List.sum_append_int {xs ys : List Int} :
    (xs ++ ys).sum = xs.sum + ys.sum := by
  induction xs generalizing ys <;> grind

theorem List.sum_reverse_int {xs : List Int} :
    xs.sum = xs.reverse.sum := by
  induction xs <;> simp_all [sum_append_int, Int.add_comm]

theorem List.sum_eq_foldl_int {xs : List Int} :
    xs.sum = xs.foldl (init := 0) (· + ·) := by
  simp only [List.foldl_eq_foldr_reverse, Int.add_comm]
  rw [← List.sum, List.sum_reverse_int]

theorem Array.sum_append_int {xs ys : Array Int} :
    (xs ++ ys).sum = xs.sum + ys.sum := by
  simp [← sum_eq_sum_toList, Array.toList_append, List.sum_append_int]

theorem Array.sum_eq_foldl_int {xs : Array Int} :
    xs.sum = xs.foldl (init := 0) (· + ·) := by
  simp [← sum_eq_sum_toList, List.sum_eq_foldl_int]

attribute [simp] Iter.toArray_filter

/-!
## Verification
-/

/-- characterization of `addElements` in terms of `Array` operations -/
theorem addElements_spec {xs : Array Int} {k : Nat} :
    addElements xs k = ((xs.extract 0 k).filter (fun x => (toString x).length ≤ 2)).sum := by
  simp [addElements, ← Iter.foldl_toArray, Array.sum_eq_foldl_int]

-- next, we state and verify the behavior from different angles

theorem addElements_append {xs ys : Array Int} {k : Nat} :
    addElements (xs ++ ys) k = addElements xs k + addElements ys (k - xs.size) := by
  simp [addElements_spec, Array.sum_append_int]

theorem addElements_zero {xs : Array Int} :
    addElements xs 0 = 0 := by
  simp [addElements_spec]


/-!
## Prompt

```python3

def add_elements(arr, k):
    """
    Given a non-empty array of integers arr and an integer k, return
    the sum of the elements with at most two digits from the first k elements of arr.

    Example:

        Input: arr = [111,21,3,4000,5,6,7,8,9], k = 4
        Output: 24 # sum of 21 + 3

    Constraints:
        1. 1 <= len(arr) <= 100
        2. 1 <= k <= len(arr)
    """
```

## Canonical solution

```python3
    return sum(elem for elem in arr[:k] if len(str(elem)) <= 2)
```

## Tests

```python3
def check(candidate):

    # Check some simple cases
    assert candidate([1,-2,-3,41,57,76,87,88,99], 3) == -4
    assert candidate([111,121,3,4000,5,6], 2) == 0
    assert candidate([11,21,3,90,5,6,7,8,9], 4) == 125
    assert candidate([111,21,3,4000,5,6,7,8,9], 4) == 24, "This prints if this assert fails 1 (good for debugging!)"

    # Check some edge cases that are easy to work out by hand.
    assert candidate([1], 1) == 1, "This prints if this assert fails 2 (also good for debugging!)"

```
-/
