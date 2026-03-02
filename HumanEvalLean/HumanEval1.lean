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
    simp only [↓Char.isValue, h₁, ↓reduceIte, Option.toList_some, String.append_singleton,
      parens_push, String.toList_push, List.filter_append, decide_true, Char.reduceEq, decide_false,
      Bool.or_false, List.filter_cons_of_pos, List.filter_nil, balance_cons, Paren.toInt_open,
      balance_nil, Int.add_zero, Int.add_left_inj]
    have := ih _ _ hsp.of_next
    refine ⟨by grind, by grind, by grind, by grind, ?_⟩
    obtain (h|⟨curr', hc₁, hc₂⟩) := this.2.2.2.2
    · exact ⟨"", by simp [*]⟩
    · refine ⟨curr'.push '(', ?_⟩
      simp only [↓Char.isValue, String.append_push, String.push_inj, and_true, parens_push,
        ↓reduceIte, Option.toList_some, minBalance_append_singleton, hc₂, Paren.toInt_open]
      have := minBalance_le_balance (parens '(' ')' curr')
      grind
  next pos b h curr _ depth result h₁ h₂ decreasedDepth newCurr hdec ih =>
    simp only [↓Char.isValue, Bool.decide_or, SPred.down_pure, Array.toList_push,
      List.flatMap_append, List.flatMap_cons, parens_push, List.flatMap_nil, List.append_nil,
      parens_empty, String.toList_push, String.toList_empty, Array.mem_push, balance_nil,
      Int.natCast_eq_zero, String.empty_eq_iff, String.append_eq_empty_iff, String.reduceEq,
      false_and, exists_const, or_false, and_true, newCurr] at ⊢ ih
    intro t₁ t₂ hsp
    obtain ⟨t₁, rfl⟩ := hsp.exists_eq_append_singleton
    simp only [↓Char.isValue, beq_iff_eq] at h₂
    simp only [↓Char.isValue, h₂, Char.reduceEq, ↓reduceIte, Option.toList_some,
      String.append_singleton, parens_push, String.toList_push, List.filter_append, decide_false,
      decide_true, Bool.or_true, List.filter_cons_of_pos, List.filter_nil]
    have := ih _ _ hsp.of_next
    refine ⟨by grind, by grind, ?_, by grind⟩
    rintro g (hg|rfl)
    · exact this.2.2.1 _ hg
    · have hy : parens '(' ')' s = parens '(' ')' (t₁ ++ String.singleton (pos.get h)) ++ parens '(' ')' t₂ := by
        simp [hsp.eq_append]
      have hx := balance_nonneg_of_isBalanced_append (hy ▸ hbal)
      simp only [↓Char.isValue, h₂, String.append_singleton, parens_push, ← this.1, Char.reduceEq,
        ↓reduceIte, Option.toList_some, List.append_assoc, balance_append, balance_flatMap,
        balance_cons, Paren.toInt_close, Int.reduceNeg, balance_nil, Int.add_zero] at hx
      rw [List.sum_eq_zero] at hx
      · obtain (h₀|⟨curr', hc₁, hc₂⟩) := this.2.2.2.2
        · simp [-String.reduceSingleton, h₀] at hx
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
    simp only [↓Char.isValue, Bool.decide_or, SPred.down_pure, parens_push, String.toList_push,
      balance_append, String.push_ne_empty, false_or, newCurr] at ⊢ ih
    intro t₁ t₂ hsp
    obtain ⟨t₁, rfl⟩ := hsp.exists_eq_append_singleton
    simp only [↓Char.isValue, beq_iff_eq] at h₂
    simp only [↓Char.isValue, h₂, Char.reduceEq, ↓reduceIte, Option.toList_some,
      String.append_singleton, parens_push, String.toList_push, List.filter_append, decide_false,
      decide_true, Bool.or_true, List.filter_cons_of_pos, List.filter_nil, balance_cons,
      Paren.toInt_close, Int.reduceNeg, balance_nil, Int.add_zero]
    have := ih _ _ hsp.of_next
    refine ⟨by grind, by grind, by grind, by grind, ?_⟩
    have hy : parens '(' ')' s = parens '(' ')' (t₁ ++ String.singleton (pos.get h)) ++ parens '(' ')' t₂ := by
      simp [hsp.eq_append]
    have hx := balance_nonneg_of_isBalanced_append (hy ▸ hbal)
    simp only [↓Char.isValue, h₂, String.append_singleton, parens_push, ← this.1, Char.reduceEq,
      ↓reduceIte, Option.toList_some, List.append_assoc, balance_append, balance_flatMap,
      balance_cons, Paren.toInt_close, Int.reduceNeg, balance_nil, Int.add_zero] at hx
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
    simp only [↓Char.isValue, String.append_singleton, parens_push, h₁, ↓reduceIte, h₂,
      Option.toList_none, List.append_nil, Bool.decide_or, String.toList_push, List.filter_append,
      decide_false, Bool.or_self, Bool.false_eq_true, not_false_eq_true, List.filter_cons_of_neg,
      List.filter_nil]
    have := ih _ _ hsp.of_next
    grind
  next => simp
  next ih =>
    simp only [String.splits_endPos_iff, ↓Char.isValue, and_imp, forall_eq_apply_imp_iff, forall_eq,
      SPred.down_pure, Bool.decide_or] at ih ⊢
    refine ⟨?_, ih.2.2.1⟩
    simp only [↓Char.isValue, ← ih.2.1, List.self_eq_append_right, String.toList_eq_nil_iff]
    obtain (h|⟨curr', hc₁, hc₂⟩) := ih.2.2.2.2
    · simp [h]
    · have := ih.1 ▸ hbal.balance_eq_zero
      simp at this
      rw [List.sum_eq_zero] at this
      · have hhelp : "(" = "".push '(' := rfl -- TODO: this is terrible
        simp only [↓Char.isValue, hc₁, hhelp, String.push_empty, String.reduceSingleton,
          parens_append, balance_append, Int.zero_add] at this
        rw [hhelp] at this
        simp only [parens_push] at this
        have := minBalance_le_balance (parens '(' ')' curr')
        grind [parens_empty]
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
