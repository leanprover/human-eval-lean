module

import HumanEvalLean.Common.Brackets
import Std.Tactic.Do

def separateParenGroups (parenString : String) : Array String := Id.run do
  let mut result := #[]
  let mut curr := ""
  let mut depth := 0
  for c in parenString do
    if c == '(' then
      depth := depth + 1
      curr := curr.push c
    else if c == ')' then
      depth := depth - 1
      curr := curr.push c
      if depth = 0 then
        result := result.push curr
        curr := ""
  return result

section Verification

/-- A group is always of the form `(` followed by any balanced paren string followed by `)`. -/
inductive IsGroup : List Paren → Prop where
  | enclose (l) : IsBalanced l → IsGroup (.open :: l ++ [.close])

theorem IsGroup.balance_eq_zero {l : List Paren} (h : IsGroup l) : balance l = 0 := by
  cases h
  simp [IsBalanced.balance_eq_zero ‹_›]

@[simp]
theorem String.append_push {s₁ s₂ : String} {c : Char} : s₁ ++ s₂.push c = (s₁ ++ s₂).push c := by
  simp [← toList_inj]

theorem isGroup_push_of_exists {s : String}
    (h : minBalance (parens '(' ')' s) = 0)
    (h' : balance (parens '(' ')' s) = 0) :
    IsGroup (parens '(' ')' (("(" ++ s).push ')')) := by
  have : "(" = "".push '(' := rfl -- TODO: this is terrible
  simp only [↓Char.isValue, this, parens_push, parens_append, parens_empty, ↓reduceIte,
    Option.toList_some, List.nil_append, List.cons_append, Char.reduceEq]
  apply IsGroup.enclose
  grind [isBalanced_iff]

set_option mvcgen.warning false
open Std.Do
theorem goal {s : String} {hbal : IsBalanced (parens '(' ')' s)} :
    /- Concatenating the groups back together yields the original string after filtering for `(` and `)` only. -/
    (separateParenGroups s).toList.flatMap String.toList = s.toList.filter (fun c => c = '(' ∨ c = ')') ∧
    /- Every returned group is indeed a group. -/
    ∀ g ∈ separateParenGroups s, IsGroup (parens '(' ')' g) := by
  generalize hwp : separateParenGroups s = w
  apply Std.Do.Id.of_wp_run_eq hwp
  mvcgen
  case vc1.inv => exact ⇓⟨pos, ⟨curr, depth, result⟩⟩ =>
    ⌜∀ t₁ t₂, pos.Splits t₁ t₂ →
      result.toList.flatMap (parens '(' ')') ++ (parens '(' ')' curr) = parens '(' ')' t₁ ∧
      result.toList.flatMap String.toList ++ curr.toList = t₁.toList.filter (fun c => c = '(' ∨ c = ')') ∧
      (∀ g ∈ result, IsGroup (parens '(' ')' g)) ∧
      depth = balance (parens '(' ')' curr) ∧
      (curr = "" ∨ ∃ curr', curr = "(" ++ curr' ∧ minBalance (parens '(' ')' curr') = 0)⌝
  next pos _ h curr _ depth result h₁ ih =>
    simp [curr] at ⊢ ih
    intro t₁ t₂ hsp
    obtain ⟨t₁, rfl⟩ := hsp.exists_eq_append_singleton
    simp only [↓Char.isValue, beq_iff_eq] at h₁
    simp [h₁]
    have := ih _ _ hsp.of_next
    refine ⟨by grind, by grind, by grind, by grind, ?_⟩
    obtain (h|⟨curr', hc₁, hc₂⟩) := this.2.2.2.2
    · refine ⟨"", ?_⟩
      simp [← String.toList_inj, *]
      rfl -- TODO: this is terrible
    · refine ⟨curr'.push '(', ?_⟩
      simp [hc₂]
      have := minBalance_le_balance (parens '(' ')' curr')
      grind
  next pos b h curr _ depth result h₁ h₂ decreasedDepth newCurr hdec ih =>
    simp [newCurr] at ⊢ ih
    intro t₁ t₂ hsp
    obtain ⟨t₁, rfl⟩ := hsp.exists_eq_append_singleton
    simp only [↓Char.isValue, beq_iff_eq] at h₂
    simp [h₂]
    have := ih _ _ hsp.of_next
    refine ⟨by grind, by grind, ?_, by grind⟩
    rintro g (hg|rfl)
    · exact this.2.2.1 _ hg
    · have hy : parens '(' ')' s = parens '(' ')' (t₁ ++ String.singleton (pos.get h)) ++ parens '(' ')' t₂ := by
        simp [hsp.eq_append]
      have hx := balance_nonneg_of_isBalanced_append (hy ▸ hbal)
      simp [h₂, ← this.1] at hx
      rw [List.sum_eq_zero] at hx
      · obtain (h₀|⟨curr', hc₁, hc₂⟩) := this.2.2.2.2
        · simp [h₀] at hx
        · subst curr
          rw [hc₁]
          apply isGroup_push_of_exists hc₂
          have hhelp : "(" = "".push '(' := rfl -- TODO: this is terrible
          simp only [↓Char.isValue, hc₁, hhelp, parens_append, parens_push, parens_empty,
            ↓reduceIte, Option.toList_some, List.nil_append, List.cons_append, balance_cons,
            Paren.toInt_open, Int.reduceNeg, Int.zero_add, String.append_eq_empty_iff,
            String.push_ne_empty, false_and, String.append_right_inj, exists_eq_left',
            false_or] at hx this
          grind
      · simp only [↓Char.isValue, List.mem_map, Array.mem_toList_iff, Function.comp_apply,
          forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
        exact fun g hg => (this.2.2.1 g hg).balance_eq_zero
  next pos b h curr _ depth result h₁ h₂ decreasedDepth newCurr hd ih =>
    simp [newCurr] at ⊢ ih
    intro t₁ t₂ hsp
    obtain ⟨t₁, rfl⟩ := hsp.exists_eq_append_singleton
    simp only [↓Char.isValue, beq_iff_eq] at h₂
    simp [h₂]
    have := ih _ _ hsp.of_next
    refine ⟨by grind, by grind, by grind, by grind, ?_⟩
    have hy : parens '(' ')' s = parens '(' ')' (t₁ ++ String.singleton (pos.get h)) ++ parens '(' ')' t₂ := by
      simp [hsp.eq_append]
    have hx := balance_nonneg_of_isBalanced_append (hy ▸ hbal)
    simp [h₂, ← this.1] at hx
    rw [List.sum_eq_zero] at hx
    · obtain (h|⟨curr', hc₁, hc₂⟩) := this.2.2.2.2
      · simp [h] at hx
      · refine ⟨curr'.push ')', ?_⟩
        have hhelp : "(" = "".push '(' := rfl -- TODO: this is terrible
        simp only [↓Char.isValue, hc₁, hhelp, parens_append, parens_push, parens_empty, ↓reduceIte,
          Option.toList_some, List.nil_append, List.cons_append, balance_cons, Paren.toInt_open,
          Int.reduceNeg, Int.zero_add, String.append_eq_empty_iff, String.push_ne_empty, false_and,
          String.append_right_inj, exists_eq_left', hc₂, or_true, and_true, String.append_push,
          Char.reduceEq, minBalance_append_singleton, Paren.toInt_close, true_and,
          curr] at ⊢ hx this
        grind
    · simp only [↓Char.isValue, List.mem_map, Array.mem_toList_iff, Function.comp_apply,
        forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      exact fun g hg => (this.2.2.1 g hg).balance_eq_zero
  next pos _ h curr _ depth h₁ h₂ ih =>
    simp only [↓Char.isValue, SPred.down_pure] at ih ⊢
    intro t₁ t₂ hsp
    obtain ⟨t₁, rfl⟩ := hsp.exists_eq_append_singleton
    simp only [↓Char.isValue, beq_iff_eq] at h₁ h₂
    simp [h₁, h₂]
    have := ih _ _ hsp.of_next
    grind
  next => simp
  next ih =>
    simp only [String.splits_endPos_iff, ↓Char.isValue, and_imp, forall_eq_apply_imp_iff, forall_eq,
      SPred.down_pure, Bool.decide_or] at ih ⊢
    refine ⟨?_, ih.2.2.1⟩
    simp [← ih.2.1]
    obtain (h|⟨curr', hc₁, hc₂⟩) := ih.2.2.2.2
    · simp [h]
    · have := ih.1 ▸ hbal.balance_eq_zero
      simp at this
      rw [List.sum_eq_zero] at this
      · have hhelp : "(" = "".push '(' := rfl -- TODO: this is terrible
        simp [hc₁, hhelp] at this
        have := minBalance_le_balance (parens '(' ')' curr')
        grind
      · simp only [↓Char.isValue, List.mem_map, Array.mem_toList_iff, Function.comp_apply,
          forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
        refine fun g hg => (ih.2.2.1 g hg).balance_eq_zero

end Verification

/-!
## Prompt

```python3
from typing import List


def separate_paren_groups(paren_string: str) -> List[str]:
    """ Input to this function is a string containing multiple groups of nested parentheses. Your goal is to
    separate those group into separate strings and return the list of those.
    Separate groups are balanced (each open brace is properly closed) and not nested within each other
    Ignore any spaces in the input string.
    >>> separate_paren_groups('( ) (( )) (( )( ))')
    ['()', '(())', '(()())']
    """
```

## Canonical solution

```python3
    result = []
    current_string = []
    current_depth = 0

    for c in paren_string:
        if c == '(':
            current_depth += 1
            current_string.append(c)
        elif c == ')':
            current_depth -= 1
            current_string.append(c)

            if current_depth == 0:
                result.append(''.join(current_string))
                current_string.clear()

    return result
```

## Tests

```python3


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    assert candidate('(()()) ((())) () ((())()())') == [
        '(()())', '((()))', '()', '((())()())'
    ]
    assert candidate('() (()) ((())) (((())))') == [
        '()', '(())', '((()))', '(((())))'
    ]
    assert candidate('(()(())((())))') == [
        '(()(())((())))'
    ]
    assert candidate('( ) (( )) (( )( ))') == ['()', '(())', '(()())']
```
-/
