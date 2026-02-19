module

import Std.Tactic.Do

inductive Paren where
  | open : Paren
  | close : Paren

def Paren.toInt : Paren → Int
  | .open => 1
  | .close => -1

@[simp, grind =] theorem Paren.toInt_open : Paren.open.toInt = 1 := rfl
@[simp, grind =] theorem Paren.toInt_close : Paren.close.toInt = -1 := rfl

@[simp] theorem Paren.toInt_nonneg_iff {p : Paren} : 0 ≤ p.toInt ↔ p = .open := by cases p <;> simp
@[simp] theorem Paren.toInt_pos_iff {p : Paren} : 0 < p.toInt ↔ p = .open := by cases p <;> simp
@[simp] theorem Paren.toInt_nonpos_iff {p : Paren} : p.toInt ≤ 0 ↔ p = .close := by cases p <;> simp
@[simp] theorem Paren.toInt_neg_iff {p : Paren} : p.toInt < 0 ↔ p = .close := by cases p <;> simp
@[simp] theorem Paren.toInt_eq_one_iff {p : Paren} : p.toInt = 1 ↔ p = .open := by cases p <;> simp
@[simp] theorem Paren.toInt_eq_neg_one_iff {p : Paren} : p.toInt = -1 ↔ p = .close := by cases p <;> simp

inductive IsBalanced : List Paren → Prop where
  | empty : IsBalanced []
  | append (l₁ l₂) : IsBalanced l₁ → IsBalanced l₂ → IsBalanced (l₁ ++ l₂)
  | enclose (l) : IsBalanced l → IsBalanced (.open :: l ++ [.close])

attribute [simp] IsBalanced.empty

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

theorem List.take_singleton {a : α} {n : Nat} : [a].take n = if 0 < n then [a] else [] := by
  rw [List.take_cons_eq_if, List.take_nil]

def minBalance (l : List Paren) : Int :=
  (0...=l.length).toList.map (fun k => balance (l.take k)) |>.min (by simp)

attribute [-simp] Nat.toList_rcc_eq_append
attribute [simp] Std.Rcc.mem_toList_iff_mem Std.Rcc.mem_iff

theorem minBalance_nonpos {l : List Paren} : minBalance l ≤ 0 := by
  rw [minBalance]
  apply List.min_le_of_mem
  simp only [List.mem_map, Std.Rcc.mem_toList_iff_mem, Std.Rcc.mem_iff, Nat.zero_le, true_and]
  exact ⟨0, by simp⟩

@[simp]
theorem minBalance_nil : minBalance [] = 0 := by
  simp [minBalance]

attribute [simp] Nat.min_le_left Nat.min_le_right

theorem minBalance_eq_zero_iff {l : List Paren} : minBalance l = 0 ↔ ∀ k, 0 ≤ balance (l.take k) := by
  simp only [← Std.le_antisymm_iff, minBalance_nonpos, true_and]
  simp only [minBalance, List.le_min_iff, List.mem_map, Std.Rcc.mem_toList_iff_mem, Std.Rcc.mem_iff,
    Nat.zero_le, true_and, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  exact ⟨fun h n => List.take_eq_take_min ▸ h (min n l.length) (by simp), fun h n _ => h n⟩

theorem List.min_cons_cons {a b : α} {l : List α} [Min α] :
    (a :: b :: l).min (by simp) = (min a b :: l).min (by simp) := by rfl

theorem List.min_cons {a : α} {l : List α} [Min α] [Std.Associative (α := α) Min.min] {h} :
    (a :: l).min h = l.min?.elim a (min a ·) :=
  match l with
  | nil => by simp
  | cons hd tl => by simp [List.min?_cons, List.min_eq_get_min?]

@[simp]
theorem List.min_cons_cons_nil [Min α] {a b : α} : [a, b].min (by simp) = min a b := by
  simp [List.min_cons_cons]

theorem List.ne_nil_induction {P : (l : List α) → Prop} (l : List α)
    (nil : P [])
    (singleton : (a : α) → P [a]) (cons : (a : α) → (l : List α) → (h : l ≠ []) → P l → P (a :: l)) : P l := by
  induction l with
  | nil => exact nil
  | cons hd tl ih =>
    match tl with
    | [] => exact singleton _
    | t::tl => exact cons _ _ (by simp) ih

theorem add_min [Add α] [Min α] [LE α] [comm : Std.Commutative (α := α) (· + ·)] [Std.IsPartialOrder α] [Std.LawfulOrderMin α]
    [Lean.Grind.OrderedAdd α] {a b c : α} : a + min b c = min (a + b) (a + c) := by
  refine Std.le_antisymm ?_ ?_
  · rw [Std.le_min_iff, comm.comm a, comm.comm a, ← Lean.Grind.OrderedAdd.add_le_left_iff,
      comm.comm a, ← Lean.Grind.OrderedAdd.add_le_left_iff]
    exact ⟨Std.min_le_left, Std.min_le_right⟩
  · rw [Std.min_le, comm.comm a, comm.comm a, ← Lean.Grind.OrderedAdd.add_le_left_iff,
      comm.comm a, ← Lean.Grind.OrderedAdd.add_le_left_iff]
    obtain (h|h) := Std.min_eq_or (a := b) (b := c)
    · rw (occs := [1]) [← h]
      simp
    · rw (occs := [2]) [← h]
      simp

theorem List.add_min [Add α] [Min α] [LE α] [comm : Std.Commutative (α := α) (· + ·)] [Std.IsPartialOrder α] [Std.LawfulOrderMin α]
    [Lean.Grind.OrderedAdd α] {a : α} {l : List α} {h} :
    a + l.min h = (l.map (a + ·)).min (by simpa) := by
  generalize hlen : l.length = n
  induction n generalizing l with
  | zero => simp_all
  | succ n ih =>
    match n, l, hlen with
    | 0, [b], _ => simp
    | 1, [b, c], _ => simp [_root_.add_min]
    | n + 2, b :: c :: tl, _ =>
      simp only [min_cons_cons, map_cons]
      rw [ih (by grind)]
      simp [map_cons, _root_.add_min]

@[simp]
theorem minBalance_cons {l : List Paren} {p : Paren} :
    minBalance (p :: l) = min 0 (p.toInt + minBalance l) := by
  rw [minBalance]
  simp [Nat.toList_rcc_succ_right_eq_cons_map]
  rw [List.min_cons, List.min?_eq_some_min (by simp)]
  simp only [Option.elim_some, minBalance, List.add_min, List.map_map]
  congr 1

theorem minBalance_append {l m : List Paren} :
    minBalance (l ++ m) = min (minBalance l) (balance l + minBalance m) := by
  induction l with
  | nil => simpa using (Int.min_eq_right minBalance_nonpos).symm
  | cons p l ih => grind [minBalance_cons]

theorem isBalanced_iff {l : List Paren} :
    IsBalanced l ↔ (balance l = 0 ∧ minBalance l = 0) := by
  rw [minBalance_eq_zero_iff]
  refine ⟨fun h => ?_, fun h => ?_⟩
  ·  induction h with
    | empty => simp
    | append l₁ l₂ ih₁ ih₂ h₁ h₂ => exact ⟨by grind, by grind [List.take_append]⟩ -- https://github.com/leanprover/lean4/issues/12581
    | enclose l h ih =>
      refine ⟨by grind, fun k => ?_⟩
      simp only [List.cons_append, List.take_cons_eq_if]
      grind [List.take_append, List.take_singleton]
  · rcases h with ⟨h₁, h₂⟩
    generalize h : l.length = n
    induction n using Nat.strongRecOn generalizing l with | ind n ih
    subst h
    by_cases h : ∃ k, 0 < k ∧ k < l.length ∧ balance (l.take k) = 0
    · obtain ⟨k, hk₁, hk₂, hk₃⟩ := h
      rw [← List.take_append_drop k l]
      have := List.take_append_drop k l
      refine IsBalanced.append (l.take k) (l.drop k)
        (ih k (by grind) (by grind) (by grind) (by grind))
        (ih (l.length - k) (by grind) (by grind) (fun n => ?_) (by grind))
      suffices balance (List.take n (List.drop k l)) = balance (List.take ((l.take k).length + n) l) by
        simpa [this] using h₂ _
      rw (occs := [3]) [← this]
      rw [List.take_length_add_append, balance_append, hk₃, Int.zero_add]
    · by_cases h₀ : l.length = 0
      · simp_all
      · have h' : ∀ k, 0 < k → k < l.length → 0 < balance (l.take k) := by grind
        obtain ⟨l, rfl⟩ : ∃ l', l = .open :: l' ++ [.close] := by
          obtain ⟨l, rfl⟩ : ∃ l', l = .open :: l' := by
            refine ⟨l.tail, ?_⟩
            rw (occs := [1]) [← List.cons_head_tail (l := l) (by grind), List.cons.injEq]
            have := h₂ 1
            simp_all [List.take_one, List.head?_eq_some_head (l := l) (by grind)]
          refine ⟨l.take (l.length - 1), ?_⟩
          have : l ≠ [] := by grind
          have hl : l = l.take (l.length - 1) ++ [l[l.length - 1]'(by grind)] := by
            rw (occs := [1]) [← List.take_append_drop (l.length - 1) l, List.append_right_inj]
            rw [List.drop_sub_one (by grind), List.drop_length, List.append_nil,
              getElem?_pos _ _ (by grind), Option.toList_some]
          suffices l[l.length - 1]'(by grind) = .close by
            rw (occs := [1]) [hl, this, List.cons_append]
          have : balance [l[l.length - 1]'(by grind)] ≤ 0 := by grind
          simpa using this
        refine IsBalanced.enclose l (ih _ (by grind) (by grind) (fun k => ?_) rfl)
        rw [List.take_eq_take_min]
        have := h' (min k l.length + 1)
        grind

theorem not_isBalanced_append_of_balance_neg {l m : List Paren} (h : balance l < 0) :
    ¬ IsBalanced (l ++ m) := by
  simpa [isBalanced_iff, minBalance_eq_zero_iff] using fun _ => ⟨l.length, by simp [h]⟩

def parens (openBracket closeBracket : Char) (s : String) : List Paren :=
  s.toList.filterMap (fun c => if c = openBracket then some .open else if c = closeBracket then some .close else none)

@[simp]
theorem parens_empty {o c : Char} : parens o c "" = [] := by
  simp [parens]

@[simp]
theorem parens_append {o c : Char} {s t : String} :
    parens o c (s ++ t) = parens o c s ++ parens o c t := by
  simp [parens]

@[simp]
theorem parens_push {o c : Char} {s : String} {t : Char} :
    parens o c (s.push t) =
      parens o c s ++ (if t = o then some Paren.open else if t = c then some Paren.close else none).toList := by
  simp only [parens, String.toList_push, List.filterMap_append, List.filterMap_cons,
    List.filterMap_nil, List.append_cancel_left_eq]
  grind

def isBalanced (openBracket closeBracket : Char) (s : String) : Bool := Id.run do
  let mut depth := 0
  for c in s do
    if c == openBracket then
      depth := depth + 1
    else if c == closeBracket then
      if depth == 0 then
        return false
      depth := depth - 1
  return depth == 0

namespace Std.Do
variable {β : Type u} {m : Type u → Type v} {ps : PostShape.{u}}
variable [Monad m] [WPMonad m ps]

abbrev StringInvariant.withEarlyReturn {s : String}
  (onContinue : s.Pos → β → Assertion ps)
  (onReturn : γ → β → Assertion ps)
  (onExcept : ExceptConds ps := ExceptConds.false) :
    PostCond (s.Pos × MProd (Option γ) β) ps
    :=
  ⟨fun ⟨pos, x, b⟩ => spred(
        (⌜x = none⌝ ∧ onContinue pos b)
      ∨ (∃ r, ⌜x = some r⌝ ∧ ⌜pos = s.endPos⌝ ∧ onReturn r b)),
   onExcept⟩

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

#check String.Pos.Splits.next

theorem String.Pos.Splits.of_next {s : String} {p : s.Pos} {hp}
    (h : (p.next hp).Splits (t₁ ++ singleton c) t₂) : p.Splits t₁ (singleton c ++ t₂) := by
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := by simpa using h.eq (splits_next p hp)
  exact splits_next_right p hp

set_option mvcgen.warning false
theorem isBalanced_eq_true_iff {openBracket closeBracket : Char} {s : String} (h : openBracket ≠ closeBracket) :
    isBalanced openBracket closeBracket s = true ↔ IsBalanced (parens openBracket closeBracket s) := by
  generalize hwp : isBalanced openBracket closeBracket s = w
  apply Std.Do.Id.of_wp_run_eq hwp
  mvcgen
  case inv =>
    exact Std.Do.StringInvariant.withEarlyReturn
      (fun pos depth => ⌜∀ t₁ t₂, pos.Splits t₁ t₂ → minBalance (parens openBracket closeBracket t₁) = 0 ∧ depth = balance (parens openBracket closeBracket t₁)⌝)
      (fun res depth => ⌜res = false ∧ ¬ IsBalanced (parens openBracket closeBracket s)⌝)
  next pos _ hp depth h₁ ih =>
    simp only [SPred.and_nil, SPred.down_pure, SPred.exists_nil, Bool.exists_bool, true_and,
      Bool.true_eq_false, false_and, and_false, or_false, SPred.or_nil] at ih
    have := ih.resolve_right (by simp [hp])
    simp only [Int.natCast_add, Int.cast_ofNat_Int, SPred.and_nil, SPred.down_pure, true_and,
      reduceCtorEq, false_and, SPred.exists_nil, exists_const, SPred.or_nil, or_false]
    intro t₁ t₂ hsp
    obtain ⟨t₁, rfl⟩ := hsp.exists_eq_append_singleton
    simp only [beq_iff_eq] at h₁
    simp only [h₁, String.append_singleton, parens_push, ↓reduceIte, Option.toList_some,
      minBalance_append, minBalance_cons, Paren.toInt_open, minBalance_nil, Int.add_zero,
      balance_append, balance_cons, balance_nil, Int.add_left_inj]
    have := this.2 _ _ hsp.of_next
    grind
  next pos _ hp depth h₁ h₂ h₃ ih =>
    simp only [SPred.and_nil, SPred.down_pure, SPred.exists_nil, Bool.exists_bool, true_and,
      Bool.true_eq_false, false_and, and_false, or_false, SPred.or_nil, reduceCtorEq,
      String.splits_endPos_iff, and_imp, forall_eq_apply_imp_iff, forall_eq, Option.some.injEq,
      Bool.false_eq, and_self_left, exists_eq_left, false_or] at ⊢ ih
    have := ih.resolve_right (by simp [hp])
    obtain ⟨t₁, t₂, hsp⟩ : ∃ t₁ t₂, (pos.next hp).Splits t₁ t₂ := ⟨_, _, (pos.next hp).splits⟩
    obtain ⟨t₁, rfl⟩ := hsp.exists_eq_append_singleton
    rw [hsp.eq_append, parens_append]
    apply not_isBalanced_append_of_balance_neg
    simp only [beq_iff_eq] at h₂ h₃
    simp only [h₂, String.append_singleton, parens_push, Ne.symm h, ↓reduceIte, Option.toList_some,
      balance_append, balance_cons, Paren.toInt_close, Int.reduceNeg, balance_nil, Int.add_zero]
    have := this.2 _ _ hsp.of_next
    grind
  next pos _ hp depth h₁ h₂ h₃ ih =>
    simp only [SPred.and_nil, SPred.down_pure, SPred.exists_nil, Bool.exists_bool, true_and,
      Bool.true_eq_false, false_and, and_false, or_false, SPred.or_nil, reduceCtorEq,
      exists_const] at ⊢ ih
    have := ih.resolve_right (by simp [hp])
    intro t₁ t₂ hsp
    obtain ⟨t₁, rfl⟩ := hsp.exists_eq_append_singleton
    simp only [beq_iff_eq] at h₂ h₃
    simp only [h₂, String.append_singleton, parens_push, Ne.symm h, ↓reduceIte, Option.toList_some,
      minBalance_append, minBalance_cons, Paren.toInt_close, Int.reduceNeg, minBalance_nil,
      Int.add_zero, balance_append, balance_cons, balance_nil]
    have := this.2 _ _ hsp.of_next
    grind
  next pos _ hp depth h₁ h₂ ih =>
    simp only [SPred.and_nil, SPred.down_pure, SPred.exists_nil, Bool.exists_bool, true_and,
      Bool.true_eq_false, false_and, and_false, or_false, SPred.or_nil, reduceCtorEq,
      exists_const] at ⊢ ih
    have := ih.resolve_right (by simp [hp])
    intro t₁ t₂ hsp
    obtain ⟨t₁, rfl⟩ := hsp.exists_eq_append_singleton
    simp only [beq_iff_eq] at h₁ h₂
    simpa [h₁, h₂] using this.2 _ _ hsp.of_next
  next => simp
  next p h ih =>
    simp only [h, String.splits_endPos_iff, and_imp, forall_eq_apply_imp_iff, forall_eq,
      SPred.and_nil, SPred.down_pure, true_and, reduceCtorEq, false_and, SPred.exists_nil,
      exists_const, SPred.or_nil, or_false, beq_iff_eq] at ⊢ ih
    rw [isBalanced_iff]
    grind
  next p b h ih => simp_all
