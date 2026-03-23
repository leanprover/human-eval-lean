module

import HumanEvalLean.Common.Brackets
import Std.Tactic.Do

def computeMaxDepth (s : String.Slice) : Int := Id.run do
  let mut depth : Int := 0
  let mut maxDepth : Int := 0
  for c in s do
    if c == '(' then
      depth := depth + 1
      maxDepth := max maxDepth depth
    else if c == ')' then
      depth := depth - 1
      maxDepth := max maxDepth depth
  return maxDepth

def parseNestedParens (parenString : String.Slice) : Array Int :=
  (parenString.split ' ').map computeMaxDepth |>.toArray

example : parseNestedParens "(()()) ((())) () ((())()())" = #[2, 3, 1, 3] := by native_decide
example : parseNestedParens "() (()) ((())) (((())))" = #[1, 2, 3, 4] := by native_decide
example : parseNestedParens "(()(())((())))" = #[4] := by native_decide

open Std.Do

set_option mvcgen.warning false
theorem computeMaxDepth_eq {s : String.Slice} :
    computeMaxDepth s = maxBalance (parens '(' ')' s.copy) := by
  generalize hwp : computeMaxDepth s = w
  apply Std.Do.Id.of_wp_run_eq hwp
  mvcgen
  case inv1 => exact (⇓(pos, ⟨bal, maxBal⟩) => ⌜∀ (t₁ t₂ : String), pos.Splits t₁ t₂ →
    bal = balance (parens '(' ')' t₁) ∧ maxBal = maxBalance (parens '(' ')' t₁)⌝)
  next pos _ hp bal minBal h newBal newMinBal ih =>
    simp only [↓Char.isValue, SPred.down_pure] at ⊢ ih
    intro t₁ t₂ hsp
    obtain ⟨t₁, rfl⟩ := hsp.exists_eq_append_singleton
    simp only [↓Char.isValue, beq_iff_eq] at h
    simp only [↓Char.isValue, h, String.append_singleton, parens_push, ↓reduceIte,
      Option.toList_some, balance_append, balance_cons, Paren.toInt_open, balance_nil, Int.add_zero,
      maxBalance_append_singleton]
    have := ih _ _ hsp.of_next
    grind
  next pos _ hp bal minBal h₁ h₂ newBal newMinBal ih =>
    simp only [↓Char.isValue, SPred.down_pure] at ⊢ ih
    intro t₁ t₂ hsp
    obtain ⟨t₁, rfl⟩ := hsp.exists_eq_append_singleton
    simp only [↓Char.isValue, beq_iff_eq] at h₂
    simp only [↓Char.isValue, h₂, String.append_singleton, parens_push, Char.reduceEq, ↓reduceIte,
      Option.toList_some, balance_append, balance_cons, Paren.toInt_close, Int.reduceNeg,
      balance_nil, Int.add_zero, maxBalance_append_singleton]
    have := ih _ _ hsp.of_next
    grind
  next pos _ hp bal minBal h₁ h₂ ih =>
    simp only [↓Char.isValue, SPred.down_pure] at ⊢ ih
    intro t₁ t₂ hsp
    obtain ⟨t₁, rfl⟩ := hsp.exists_eq_append_singleton
    simp only [↓Char.isValue, beq_iff_eq] at h₁ h₂
    simp only [↓Char.isValue, String.append_singleton, parens_push, h₁, ↓reduceIte, h₂,
      Option.toList_none, List.append_nil]
    have := ih _ _ hsp.of_next
    grind
  next => simp
  next => simp_all

theorem computeMaxDepth_eq_comp : computeMaxDepth = (maxBalance <| parens '(' ')' ·) ∘ String.Slice.copy := by
  funext s
  exact computeMaxDepth_eq

theorem parseNestedParens_intercalate (l : List String) (hl : l ≠ [])
    (hl' : ∀ s ∈ l, ∀ c ∈ s.toList, c = '(' ∨ c = ')')  :
    parseNestedParens (" ".intercalate l) = (l.map (maxBalance <| parens '(' ')' ·)).toArray := by
  simp only [parseNestedParens, ↓Char.isValue, Std.Iter.toArray_map, computeMaxDepth_eq_comp,
    ← Array.toList_inj, Array.toList_map, Std.Iter.toList_toArray, ← List.map_map]
  erw [← String.split_eq_split_toSlice, String.toList_split_intercalate (by grind), if_neg hl]

/-!
## Prompt

```python3
from typing import List


def parse_nested_parens(paren_string: str) -> List[int]:
    """ Input to this function is a string represented multiple groups for nested parentheses separated by spaces.
    For each of the group, output the deepest level of nesting of parentheses.
    E.g. (()()) has maximum two levels of nesting while ((())) has three.

    >>> parse_nested_parens('(()()) ((())) () ((())()())')
    [2, 3, 1, 3]
    """
```

## Canonical solution

```python3
    def parse_paren_group(s):
        depth = 0
        max_depth = 0
        for c in s:
            if c == '(':
                depth += 1
                max_depth = max(depth, max_depth)
            else:
                depth -= 1

        return max_depth

    return [parse_paren_group(x) for x in paren_string.split(' ') if x]
```

## Tests

```python3


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    assert candidate('(()()) ((())) () ((())()())') == [2, 3, 1, 3]
    assert candidate('() (()) ((())) (((())))') == [1, 2, 3, 4]
    assert candidate('(()(())((())))') == [4]
```
-/
