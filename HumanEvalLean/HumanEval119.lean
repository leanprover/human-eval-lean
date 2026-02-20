module

import HumanEvalLean.Common.Brackets
import Std.Tactic.Do

def computeBalance (s : String.Slice) : Int × Int := Id.run do
  let mut balance := 0
  let mut minBalance := 0
  for c in s do
    if c == '(' then
      balance := balance + 1
      minBalance := min minBalance balance
    else if c == ')' then
      balance := balance - 1
      minBalance := min minBalance balance
  return (balance, minBalance)

def matchParens (s₁ s₂ : String.Slice) : Bool :=
  let (bal₁, minBal₁) := computeBalance s₁
  let (bal₂, minBal₂) := computeBalance s₂
  bal₁ + bal₂ == 0 && ((minBal₁ == 0 && bal₁ + minBal₂ == 0) || (minBal₂ == 0 && bal₂ + minBal₁ == 0))

example : matchParens "()(" ")" = true := by native_decide
example : matchParens ")" ")" = false := by native_decide
example : matchParens "(()(())" "())())" = false := by native_decide
example : matchParens ")())" "(()()(" = true := by native_decide
example : matchParens "(())))" "(()())((" = true := by native_decide
example : matchParens "()" "())" = false := by native_decide
example : matchParens "(()(" "()))()" = true := by native_decide
example : matchParens "((((" "((())" = false := by native_decide
example : matchParens ")(()" "(()(" = false := by native_decide
example : matchParens ")(" ")(" = false := by native_decide
example : matchParens "(" ")" = true := by native_decide
example : matchParens ")" "(" = true := by native_decide

open Std.Do

set_option mvcgen.warning false
theorem computeBalance_eq {s : String.Slice} :
    computeBalance s = (balance (parens '(' ')' s.copy), minBalance (parens '(' ')' s.copy)) := by
  generalize hwp : computeBalance s = w
  apply Std.Do.Id.of_wp_run_eq hwp
  mvcgen
  case inv => exact (⇓(pos, ⟨bal, minBal⟩) => ⌜∀ (t₁ t₂ : String), pos.Splits t₁ t₂ →
    bal = balance (parens '(' ')' t₁) ∧ minBal = minBalance (parens '(' ')' t₁)⌝)
  next pos _ hp bal minBal h newBal newMinBal ih =>
    simp only [↓Char.isValue, SPred.down_pure] at ⊢ ih
    intro t₁ t₂ hsp
    obtain ⟨t₁, rfl⟩ := hsp.exists_eq_append_singleton
    simp only [↓Char.isValue, beq_iff_eq] at h
    simp only [↓Char.isValue, h, String.append_singleton, parens_push, ↓reduceIte,
      Option.toList_some, balance_append, balance_cons, Paren.toInt_open, balance_nil, Int.add_zero,
      minBalance_append_singleton]
    have := ih _ _ hsp.of_next
    grind
  next pos _ hp bal minBal h₁ h₂ newBal newMinBal ih =>
    simp only [↓Char.isValue, SPred.down_pure] at ⊢ ih
    intro t₁ t₂ hsp
    obtain ⟨t₁, rfl⟩ := hsp.exists_eq_append_singleton
    simp only [↓Char.isValue, beq_iff_eq] at h₂
    simp only [↓Char.isValue, h₂, String.append_singleton, parens_push, Char.reduceEq, ↓reduceIte,
      Option.toList_some, balance_append, balance_cons, Paren.toInt_close, Int.reduceNeg,
      balance_nil, Int.add_zero, minBalance_append_singleton]
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

theorem matchParens_eq_true_iff {s₁ s₂ : String.Slice} :
    matchParens s₁ s₂ = true ↔ IsBalanced (parens '(' ')' (s₁.copy ++ s₂.copy)) ∨ IsBalanced (parens '(' ')' (s₂.copy ++ s₁.copy)) := by
  simp [matchParens, computeBalance_eq, isBalanced_iff, minBalance_append]
  have := minBalance_nonpos (parens '(' ')' s₁.copy)
  have := minBalance_nonpos (parens '(' ')' s₂.copy)
  have := minBalance_le_balance (parens '(' ')' s₁.copy)
  have := minBalance_le_balance (parens '(' ')' s₂.copy)
  grind

/-!
## Prompt

```python3

def match_parens(lst):
    '''
    You are given a list of two strings, both strings consist of open
    parentheses '(' or close parentheses ')' only.
    Your job is to check if it is possible to concatenate the two strings in
    some order, that the resulting string will be good.
    A string S is considered to be good if and only if all parentheses in S
    are balanced. For example: the string '(())()' is good, while the string
    '())' is not.
    Return 'Yes' if there's a way to make a good string, and return 'No' otherwise.

    Examples:
    match_parens(['()(', ')']) == 'Yes'
    match_parens([')', ')']) == 'No'
    '''
```

## Canonical solution

```python3
    def check(s):
        val = 0
        for i in s:
            if i == '(':
                val = val + 1
            else:
                val = val - 1
            if val < 0:
                return False
        return True if val == 0 else False

    S1 = lst[0] + lst[1]
    S2 = lst[1] + lst[0]
    return 'Yes' if check(S1) or check(S2) else 'No'
```

## Tests

```python3
def check(candidate):

    # Check some simple cases
    assert candidate(['()(', ')']) == 'Yes'
    assert candidate([')', ')']) == 'No'
    assert candidate(['(()(())', '())())']) == 'No'
    assert candidate([')())', '(()()(']) == 'Yes'
    assert candidate(['(())))', '(()())((']) == 'Yes'
    assert candidate(['()', '())']) == 'No'
    assert candidate(['(()(', '()))()']) == 'Yes'
    assert candidate(['((((', '((())']) == 'No'
    assert candidate([')(()', '(()(']) == 'No'
    assert candidate([')(', ')(']) == 'No'


    # Check some edge cases that are easy to work out by hand.
    assert candidate(['(', ')']) == 'Yes'
    assert candidate([')', '(']) == 'Yes'

```
-/
