module

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

inductive Paren where
  | open : Paren
  | close : Paren

def Paren.toInt : Paren → Int
  | .open => 1
  | .close => -1

@[simp, grind =] theorem Paren.toInt_open : Paren.open.toInt = 1 := rfl
@[simp, grind =] theorem Paren.toInt_close : Paren.close.toInt = -1 := rfl

inductive IsBalanced : List Paren → Prop where
  | empty : IsBalanced []
  | append (l₁ l₂) : IsBalanced l₁ → IsBalanced l₂ → IsBalanced (l₁ ++ l₂)
  | enclose (l) : IsBalanced l → IsBalanced (.open :: l ++ [.close])

attribute [simp] IsBalanced.empty

inductive IsGroup : List Paren → Prop where
  | enclose : IsBalanced l → IsGroup (.open :: l ++ [.close])

def parens (s : String) : List Paren :=
  s.toList.filterMap (fun c => if c = '(' then some .open else if c = ')' then some .close else none)

-- theorem List.take_append_eq_if {l₁ l₂ : List α} {n} :
--     (l₁ ++ l₂).take n = if n ≤ l₁.length then l₁.take n else l₁ ++ l₂.take (n - l₁.length) := by
--   split
--   case isTrue h => rw [List.take_append_of_le_length h]
--   next h => rw [List.take_append, take_of_length_le (by omega)]

def balance (l : List Paren) : Int :=
  l.map (·.toInt) |>.sum

@[simp, grind =]
theorem balance_nil : balance [] = 0 := by
  simp [balance]

@[simp, grind =]
theorem balance_append : balance (l₁ ++ l₂) = balance l₁ + balance l₂ := by
  simp [balance]

@[simp, grind =]
theorem balance_cons : balance (p :: l) = p.toInt + balance l := by
  simp [balance]

theorem List.take_cons_eq_if {l : List α} {a : α} {n : Nat} :
    (a::l).take n = if 0 < n then a :: l.take (n - 1) else [] := by
  split
  · exact take_cons ‹_›
  · obtain rfl : n = 0 := by omega
    simp

theorem List.take_singleton {a : α} {n : Nat} : [a].take n = if n = 0 then [] else [a] := by
  sorry

theorem isBalanced_iff {l : List Paren} :
    IsBalanced l ↔ (balance l = 0 ∧ ∀ k, 0 ≤ balance (l.take k)) := by
  refine ⟨fun h => ?_, fun ⟨h₁, h₂⟩ => ?_⟩
  ·  induction h with
    | empty => simp
    | append l₁ l₂ ih₁ ih₂ h₁ h₂ => exact ⟨by grind, by grind [List.take_append]⟩ -- https://github.com/leanprover/lean4/issues/12581
    | enclose l h ih =>
      refine ⟨by grind, fun k => ?_⟩
      simp only [List.cons_append, List.take_cons_eq_if]
      grind [List.take_append, List.take_singleton]
  ·
  -- generalize h : l.length = n
  -- induction n using Nat.strongRecOn generalizing l with | ind n ih
  -- refine ⟨fun h => ?_, ?_⟩
  -- ·
  --   induction h generalizing n with
  --   | empty => simp
  --   | append l₁ l₂ ih₁ ih₂ h₁ h₂ =>

  --     skip


  --   | enclose => sorry
  -- · sorry


  -- | zero => simp_all
  -- | succ n ih =>




namespace Std.Do
variable {β : Type u} {m : Type u → Type v} {ps : PostShape.{u}}
variable [Monad m] [WPMonad m ps]

@[spec]
theorem Spec.forIn_string
    {s : String} {init : β} {f : Char → β → m (ForInStep β)}
    (inv : PostCond (s.Pos × β) ps)
    (step : ∀ pos b (h : pos ≠ s.endPos),
      Triple
        (f (pos.get h) b)
        (inv.1 (pos, b))
        (fun r => match r with
          | .yield b' => inv.1 (pos.next h, b')
          | .done b' => inv.1 (s.endPos, b'), inv.2)) :
    Triple (forIn s init f) (inv.1 (s.startPos, init)) (fun b => inv.1 (s.endPos, b), inv.2) := by
  suffices h : ∀ (p : s.Pos) (t₁ t₂ : String) (h : p.Splits t₁ t₂),
      Triple (forIn t₂.toList init f) (inv.1 (p, init)) (fun b => inv.1 (s.endPos, b), inv.2) by
    simpa using h s.startPos _ _ s.splits_startPos
  intro p
  induction p using String.Pos.next_induction generalizing init with
  | next p hp ih =>
    intro t₁ t₂ hsp
    obtain ⟨t₂, rfl⟩ := hsp.exists_eq_singleton_append hp
    simp only [String.toList_append, String.toList_singleton, List.cons_append, List.nil_append,
      List.forIn_cons]
    apply Triple.bind
    case hx => exact step _ _ hp
    case hf =>
      intro r
      split
      next => apply Triple.pure; simp
      next b => simp [ih _ _ hsp.next]
  | endPos => simpa using Triple.pure _ (by simp)

end Std.Do

open Std.Do

/-- You might want to invoke `Pos.Splits.exists_eq_singleton_append` to be able to apply this. -/
theorem String.Pos.Splits.of_next {s : String} {p : s.Pos} {h}
    (h : (p.next h).Splits (t₁ ++ singleton c) t₂) : p.Splits t₁ (singleton c ++ t₂) := by
  sorry
  --   -- (h : p.Splits t₁ (singleton c ++ t₂)) : (p.next h.ne_endPos_of_singleton).Splits (t₁ ++ singleton c) t₂
  --   := by
  -- generalize h.ne_endPos_of_singleton = hp
  -- obtain ⟨rfl, rfl, rfl⟩ := by simpa using h.eq (splits_next_right p hp)
  -- exact splits_next p hp

@[simp]
theorem List.self_eq_filter {l : List α} {p : α → Bool} : l = l.filter p ↔ ∀ a ∈ l, p a := by
  simp [eq_comm (a := l)]

theorem goal₁ {s : String} {h : IsBalanced (parens s)} :
    (separateParenGroups s).toList.flatMap String.toList = s.toList.filter (fun c => c = '(' ∨ c = ')') := by
  generalize hwp : separateParenGroups s = w
  apply Std.Do.Id.of_wp_run_eq hwp
  mvcgen
  case vc1.inv => exact ⇓⟨pos, ⟨curr, depth, result⟩⟩ =>
    ⌜(curr = "" ↔ depth = 0) ∧
        ∀ t₁ t₂, pos.Splits t₁ t₂ →
          result.toList.flatMap String.toList ++ curr.toList = t₁.toList.filter (fun c => c = '(' ∨ c = ')')

          ⌝
  next pos _ h curr _ depth result h₁ ih =>
    simp at ih
    simp
    intro t₁ t₂ hsp
    obtain ⟨t₁, rfl⟩ := hsp.exists_eq_append_singleton
    rw [← List.append_assoc, ih.2 _ _ hsp.of_next]
    simp only [↓Char.isValue, beq_iff_eq] at h₁
    simp [h₁]
  next pos _ h curr _ depth result h₁ h₂ decreasedDepth newCurr newDepth ih =>
    simp at ih
    simp [newCurr]
    intro t₁ t₂ hsp
    obtain ⟨t₁, rfl⟩ := hsp.exists_eq_append_singleton
    rw [← List.append_assoc, ih _ _ hsp.of_next]
    simp at h₂
    simp [h₂]
  next pos _ h curr _ depth result h₁ h₂ decreasedDepth newCurr hd ih =>
    simp at ih
    simp [newCurr]
    intro t₁ t₂ hsp
    obtain ⟨t₁, rfl⟩ := hsp.exists_eq_append_singleton
    rw [← List.append_assoc, ih _ _ hsp.of_next]
    simp at h₂
    simp [h₂]
  next pos _ h curr _ depth h₁ h₂ ih =>
    simp at ih
    simp
    intro t₁ t₂ hsp
    obtain ⟨t₁, rfl⟩ := hsp.exists_eq_append_singleton
    rw [ih _ _ hsp.of_next]
    simp at h₁ h₂
    simp [h₁, h₂]
  next => simp
  next ih =>
    simp at ih
    simp [← ih]













theorem goal₂ {s : String} {h : IsBalanced (parens s)} :
    ∀ t ∈ separateParenGroups s, IsGroup (parens t) := sorry

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
