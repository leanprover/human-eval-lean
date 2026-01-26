import Std

open Std Std.Do

set_option mvcgen.warning false

/-!
# HumanEval 128: Sum of magnitudes times product of signs

This problem description asks us to compute the sum of absolute values of an array, multiplied by
the product of the signs of all elements. We demonstrate two approaches:

1. a declarative implementation using `List.sum` and `List.product` operations
2. an efficient imperative implementation using do-notation with early exit when encountering zero
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
  simp only [wp, PredTrans.pushOption_apply, PredTrans.pure_apply] at hspec
  split at hspec
  case h_1 a s' heq => rw [← heq] at hspec; exact hspec True.intro
  case h_2 s' heq => rw [← heq] at hspec; exact hspec True.intro

theorem Option.of_wp_eq {α : Type} {x : Option α} {prog : Option α} (h : prog = x) (P : Option α → Prop) :
    (⊢ₛ wp⟦prog⟧ post⟨fun a => ⌜P (some a)⌝, fun _ => ⌜P none⌝⟩) → P x := by
  rw [← h]
  apply Option.of_wp

/-!
## Implementation 1: Using `List.sum` and `List.product`
-/

def prodSigns₁ (arr : List Int) : Option Int :=
  if arr.isEmpty then
    none
  else
    some ((arr.map Int.natAbs).sum * (arr.map Int.sign).product)

/-!
## Tests 1
-/

example : prodSigns₁ [1, 2, 2, -4] = some (-9) := by native_decide
example : prodSigns₁ [0, 1] = some 0 := by native_decide
example : prodSigns₁ [] = none := by native_decide
example : prodSigns₁ [1, 1, 1, 2, 3, -1, 1] = some (-10) := by native_decide
example : prodSigns₁ [2, 4, 1, 2, -1, -1, 9] = some 20 := by native_decide
example : prodSigns₁ [-1, 1, -1, 1] = some 4 := by native_decide
example : prodSigns₁ [-1, 1, 1, 1] = some (-4) := by native_decide
example : prodSigns₁ [-1, 1, 1, 0] = some 0 := by native_decide

/-!
## Verification 1
-/

theorem prodSigns₁_nil :
    prodSigns₁ [] = none := by
  grind [prodSigns₁]

theorem prodSigns₁_of_ne_nil {arr : List Int} (h : arr ≠ []) :
    prodSigns₁ arr = some ((arr.map Int.natAbs).sum * (arr.map Int.sign).product) := by
  simp only [prodSigns₁]
  have : ¬arr.isEmpty := by
    cases arr
    · contradiction
    · simp [List.isEmpty]
  simp [this]

/-!
## Implementation 2: Efficient `do`-based implementation with early exit

This implementation is more efficient as it
- exits early when encountering a zero (since the product will be zero)
- uses a single pass through the array
- avoids creating intermediate lists
-/

def prodSigns₂ (arr : List Int) : Option Int := do
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
## Tests 2
-/

example : prodSigns₂ [1, 2, 2, -4] = some (-9) := by native_decide
example : prodSigns₂ [0, 1] = some 0 := by native_decide
example : prodSigns₂ [] = none := by native_decide
example : prodSigns₂ [1, 1, 1, 2, 3, -1, 1] = some (-10) := by native_decide
example : prodSigns₂ [2, 4, 1, 2, -1, -1, 9] = some 20 := by native_decide
example : prodSigns₂ [-1, 1, -1, 1] = some 4 := by native_decide
example : prodSigns₂ [-1, 1, 1, 1] = some (-4) := by native_decide
example : prodSigns₂ [-1, 1, 1, 0] = some 0 := by native_decide

/-!
## Verification 2
-/

theorem prodSigns₂_nil :
    prodSigns₂ [] = none := by
  grind [prodSigns₂]

theorem prodSigns₂_of_ne_nil {xs : List Int} (h : xs ≠ []) :
    prodSigns₂ xs = some ((xs.map Int.natAbs).sum * (xs.map Int.sign).product) := by
  generalize hwp : prodSigns₂ xs = wp
  apply Option.of_wp_eq hwp
  mvcgen [prodSigns₂]
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
