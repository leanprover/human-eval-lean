import Std

open Std Std.Do

set_option mvcgen.warning false

/-!
# HumanEval 128: Sum of magnitudes times product of signs

This problem description asks us to compute the sum of absolute values of an array, multiplied by
the product of the signs of all elements. We demonstrate how to implement and verify an
efficient implementation using `do` notation and `mvcgen`.
-/

/-!
## Missing API
-/

def List.product (xs : List Int) : Int :=
  xs.foldr (· * ·) 1

@[grind =]
theorem List.product_nil : ([] : List Int).product = 1 := by
  rfl

@[grind =]
theorem List.product_cons {x : Int} {xs : List Int} :
    (x :: xs).product = x * xs.product := by
  grind [List.product]

@[grind =]
theorem List.product_append {xs ys : List Int} :
    (xs ++ ys).product = xs.product * ys.product := by
  induction xs <;> grind [List.product_cons, Int.mul_assoc]

theorem List.product_eq_zero_iff {xs : List Int} :
    xs.product = 0 ↔ 0 ∈ xs := by
  induction xs <;> grind [List.product_cons, Int.mul_eq_zero]

theorem Option.of_wp {α} {prog : Option α} (P : Option α → Prop) :
    (⊢ₛ wp⟦prog⟧ post⟨fun a => ⌜P (some a)⌝, fun _ => ⌜P none⌝⟩) → P prog := by
  intro hspec
  simp only [wp, PredTrans.apply_pushOption, PredTrans.apply_Pure_pure, SPred.entails_nil,
    SPred.down_pure, forall_const] at hspec
  split at hspec
  case h_1 a s' heq => rw [← heq] at hspec; exact hspec
  case h_2 s' heq => rw [← heq] at hspec; exact hspec

theorem Option.of_wp_eq {α : Type} {x : Option α} {prog : Option α} (h : prog = x) (P : Option α → Prop) :
    (⊢ₛ wp⟦prog⟧ post⟨fun a => ⌜P (some a)⌝, fun _ => ⌜P none⌝⟩) → P x := by
  rw [← h]
  apply Option.of_wp

/-!
## Implementation
-/

def prodSigns (arr : List Int) : Option Int := do
  if arr.isEmpty then
    none
  let mut sum := 0
  let mut sign := 1
  for x in arr do
    if x = 0 then
      return 0
    sum := sum + x.natAbs
    sign := sign * x.sign
  return sum * sign

/-!
## Tests
-/

example : prodSigns [1, 2, 2, -4] = some (-9) := by native_decide
example : prodSigns [0, 1] = some 0 := by native_decide
example : prodSigns [] = none := by native_decide
example : prodSigns [1, 1, 1, 2, 3, -1, 1] = some (-10) := by native_decide
example : prodSigns [2, 4, 1, 2, -1, -1, 9] = some 20 := by native_decide
example : prodSigns [-1, 1, -1, 1] = some 4 := by native_decide
example : prodSigns [-1, 1, 1, 1] = some (-4) := by native_decide
example : prodSigns [-1, 1, 1, 0] = some 0 := by native_decide

/-!
## Verification
-/

theorem prodSigns_nil :
    prodSigns [] = none := by
  grind [prodSigns]

theorem prodSigns_of_ne_nil {xs : List Int} (h : xs ≠ []) :
    prodSigns xs = some ((xs.map Int.natAbs).sum * (xs.map Int.sign).product) := by
  generalize hwp : prodSigns xs = wp
  apply Option.of_wp_eq hwp
  mvcgen [prodSigns]
  invariants
  · .withEarlyReturn
      (fun cur ⟨sign, sum⟩ => ⌜sum = (cur.prefix.map Int.natAbs).sum ∧ sign = (cur.prefix.map Int.sign).product⌝)
      (fun ret ⟨sign, sum⟩ => ⌜ret = 0 ∧ 0 ∈ xs⌝)
  with grind [List.product_eq_zero_iff]

/-!
## Prompt

```python3

def prod_signs(arr):
    """
    You are given an array arr of integers and you need to return
    sum of magnitudes of integers multiplied by product of all signs
    of each number in the array, represented by 1, -1 or 0.
    Note: return None for empty arr.

    Example:
    >>> prod_signs([1, 2, 2, -4]) == -9
    >>> prod_signs([0, 1]) == 0
    >>> prod_signs([]) == None
    """
```

## Canonical solution

```python3
    if not arr: return None
    prod = 0 if 0 in arr else (-1) ** len(list(filter(lambda x: x < 0, arr)))
    return prod * sum([abs(i) for i in arr])
```

## Tests

```python3
def check(candidate):

    # Check some simple cases
    assert True, "This prints if this assert fails 1 (good for debugging!)"
    assert candidate([1, 2, 2, -4]) == -9
    assert candidate([0, 1]) == 0
    assert candidate([1, 1, 1, 2, 3, -1, 1]) == -10
    assert candidate([]) == None
    assert candidate([2, 4,1, 2, -1, -1, 9]) == 20
    assert candidate([-1, 1, -1, 1]) == 4
    assert candidate([-1, 1, 1, 1]) == -4
    assert candidate([-1, 1, 1, 0]) == 0

    # Check some edge cases that are easy to work out by hand.
    assert True, "This prints if this assert fails 2 (also good for debugging!)"

```
-/
