import Std

open Std

theorem Acc.invTransGen {x y : α} (h₁ : Acc r x) (h₂ : Relation.TransGen r y x) : Acc r y := by
  simpa [acc_transGen_iff] using h₁.transGen.inv h₂

section Extrinsic
open Relation

variable {α : Sort _} {β : α → Sort _} {γ : (a : α) → β a → Sort _}
  {C : α → Sort _} {C₂ : (a : α) → β a → Sort _} {C₃ : (a : α) → (b : β a) → γ a b → Sort _}

@[inline]
public def WellFounded.partialExtrinsicFix [∀ a, Nonempty (C a)] (R : α → α → Prop)
    (F : ∀ a, (∀ a', R a' a → C a') → C a) (a : α) : C a :=
  extrinsicFix (α := { a' : α // a' = a ∨ TransGen R a' a }) (C := (C ·.1))
      (fun p q => R p.1 q.1)
      (fun a recur => F a.1 fun a' hR => recur ⟨a', by
        cases a.property
        · grind [TransGen.single]
        · apply Or.inr
          apply TransGen.trans ?_ ‹_›
          apply TransGen.single
          assumption⟩ ‹_›) ⟨a, Or.inl rfl⟩

public theorem WellFounded.bla {α' : Sort _} [∀ a, Nonempty (C a)] (R : α → α → Prop) (f : α' → α)
    (F : ∀ a, (∀ a', R a' a → C a') → C a) (F' : ∀ a, (∀ a', R (f a') (f a) → C (f a')) → C (f a))
    (h : ∀ a r, F (f a) r = F' a fun a' hR => r (f a') hR) (a : α') (h : WellFounded R) :
    extrinsicFix (C := (C <| f ·)) (InvImage R f) F' a = extrinsicFix (C := C) R F (f a) := by
  have h' := h
  rcases h with ⟨h⟩
  specialize h (f a)
  have : Acc (InvImage R f) a := InvImage.accessible _ h
  clear h
  induction this
  rename_i ih
  rw [extrinsicFix_eq_apply, extrinsicFix_eq_apply, h]
  · congr; ext a x
    rw [ih _ x]
  · assumption
  · exact InvImage.wf _ ‹_›

public theorem WellFounded.partialExtrinsicFix_eq [∀ a, Nonempty (C a)] (R : α → α → Prop)
    (F : ∀ a, (∀ a', R a' a → C a') → C a) (a : α) (h : Acc R a) :
    partialExtrinsicFix R F a = F a (fun a' _ => partialExtrinsicFix R F a') := by
  simp only [partialExtrinsicFix]
  rw [extrinsicFix_eq_apply]
  congr; ext a' hR
  simp
  let f (x : { x : α // x = a' ∨ TransGen R x a' }) : { x : α // x = a ∨ TransGen R x a } :=
    ⟨x.val, by
      cases x.property
      · rename_i h
        rw [h]
        exact Or.inr (.single hR)
      · rename_i h
        apply Or.inr
        refine TransGen.trans h ?_
        exact .single hR⟩
  have := bla (C := (C ·.val)) (R := (R ·.1 ·.1)) (f := f) (F := fun a r => F a.1 fun a' hR => r ⟨a', Or.inr (by cases a.2; grind [TransGen.single]; exact .trans (.single hR) ‹_›)⟩ hR)
    (F' := fun a r => F a.1 fun a' hR => r ⟨a', by cases a.2; grind [TransGen.single]; exact Or.inr (.trans (.single hR) ‹_›)⟩ hR)
  unfold InvImage at this
  rw [this]
  · grind
  · constructor
    intro x
    refine InvImage.accessible _ ?_
    cases x.2 <;> rename_i hx
    · rwa [hx]
    · exact h.invTransGen hx
  · constructor
    intro x
    refine InvImage.accessible _ ?_
    cases x.2 <;> rename_i hx
    · rwa [hx]
    · exact h.invTransGen hx

@[inline]
public def WellFounded.partialExtrinsicFix₂ [∀ a b, Nonempty (C₂ a b)]
    (R : (a : α) ×' β a → (a : α) ×' β a → Prop)
    (F : (a : α) → (b : β a) → ((a' : α) → (b' : β a') → R ⟨a', b'⟩ ⟨a, b⟩ → C₂ a' b') → C₂ a b)
    (a : α) (b : β a) :
    C₂ a b :=
  extrinsicFix₂ (α := α) (β := fun a' => { b' : β a' // (PSigma.mk a' b') = (PSigma.mk a b) ∨ TransGen R ⟨a', b'⟩ ⟨a, b⟩ })
      (C₂ := (C₂ · ·.1))
      (fun p q => R ⟨p.1, p.2.1⟩ ⟨q.1, q.2.1⟩)
      (fun a b recur => F a b.1 fun a' b' hR => recur a' ⟨b', Or.inr (by
        cases b.property
        · grind [TransGen.single]
        · apply TransGen.trans ?_ ‹_›
          apply TransGen.single
          assumption)⟩ ‹_›) a ⟨b, Or.inl rfl⟩

public theorem WellFounded.partialExtrinsicFix₂_eq_partialExtrinsicFix [∀ a b, Nonempty (C₂ a b)]
    (R : (a : α) ×' β a → (a : α) ×' β a → Prop)
    (F : (a : α) → (b : β a) → ((a' : α) → (b' : β a') → R ⟨a', b'⟩ ⟨a, b⟩ → C₂ a' b') → C₂ a b)
    (a : α) (b : β a) (h : Acc R ⟨a, b⟩) :
    partialExtrinsicFix₂ R F a b = partialExtrinsicFix (α := PSigma β) (C := fun a => C₂ a.1 a.2) R (fun p r => F p.1 p.2 fun a' b' hR => r ⟨a', b'⟩ hR) ⟨a, b⟩ := by
  simp only [partialExtrinsicFix, partialExtrinsicFix₂, extrinsicFix₂]
  let f (x : ((a' : α) ×' { b' // PSigma.mk a' b' = ⟨a, b⟩ ∨ TransGen R ⟨a', b'⟩ ⟨a, b⟩ })) : { a' // a' = ⟨a, b⟩ ∨ TransGen R a' ⟨a, b⟩ } :=
    ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  have := bla (C := fun a => C₂ a.1.1 a.1.2) (f := f) (R := (R ·.1 ·.1))
    (F := fun a r => F a.1.1 a.1.2 fun a' b' hR => r ⟨⟨a', b'⟩, ?refine_a⟩ hR)
    (F' := fun a r => F a.1 a.2.1 fun a' b' hR => r ⟨a', b', ?refine_b⟩ hR)
    (a := ⟨a, b, ?refine_c⟩); rotate_left
  · cases a.2 <;> rename_i heq
    · rw [heq] at hR
      exact .inr (.single hR)
    · exact .inr (.trans (.single hR) heq)
  · cases a.2.2 <;> rename_i heq
    · rw [heq] at hR
      exact .inr (.single hR)
    · exact .inr (.trans (.single hR) heq)
  · exact .inl rfl
  unfold InvImage f at this
  simp at this
  rw [this]
  constructor
  intro x
  apply InvImage.accessible
  cases x.2 <;> rename_i heq
  · rwa [heq]
  · exact h.invTransGen heq

public def WellFounded.partialExtrinsicFix₂_eq [∀ a b, Nonempty (C₂ a b)]
    {R : (a : α) ×' β a → (a : α) ×' β a → Prop}
    {F : (a : α) → (b : β a) → ((a' : α) → (b' : β a') → R ⟨a', b'⟩ ⟨a, b⟩ → C₂ a' b') → C₂ a b}
    {a : α} {b : β a} (h : Acc R ⟨a, b⟩) :
    partialExtrinsicFix₂ R F a b = F a b (fun a' b' _ => partialExtrinsicFix₂ R F a' b') := by
  simp only [partialExtrinsicFix₂_eq_partialExtrinsicFix (h := h)]
  rw [partialExtrinsicFix_eq (h := h)]
  have (a' b') (hR : R ⟨a', b'⟩ ⟨a, b⟩) : Acc R ⟨a', b'⟩ := h.inv hR
  conv => rhs; congr; intro a' b' hR; rw [partialExtrinsicFix₂_eq_partialExtrinsicFix (h := this a' b' hR)]

end Extrinsic

/-!
## Implementation 1: no termination proof required
-/

def collatzStep (n : Nat) : Nat :=
    if n % 2 = 0 then n / 2 else n * 3 + 1

def CollatzRel : Nat → Nat → Prop := fun m n =>
    n > 1 ∧ collatzStep n = m

theorem collatzRel_collatzStep {n : Nat} (h : n > 1) :
    CollatzRel (collatzStep n) n := by
  grind [CollatzRel]

def oddCollatz₁ (n : Nat) : List Nat :=
  (collectOddCollatz ⟨n, Or.inl rfl⟩ ∅).toList
where
  -- This function is recursive and, depending on the Collatz conjecture, it may or may not terminate.
  -- By relying on the fixpoint combinator `extrinsicFix₂` instead of using the `partial` modifier,
  -- we will be able to verify the function whenever the Collatz sequence terminates after
  -- finitely many steps. A termination proof is not required for *calling* this function,
  -- only for verifying it.
  collectOddCollatz : (n : { m // m = n ∨ Relation.TransGen CollatzRel m n }) → (acc : TreeSet Nat compare) → TreeSet Nat compare :=
    WellFounded.extrinsicFix₂ (CollatzRel ·.1 ·.1) fun n acc recur =>
      if h : n.val > 1 then
        recur ⟨collatzStep n.val, by apply Or.inr; cases n.property; rename_i h'; rw [h']; apply Relation.TransGen.single; grind [collatzRel_collatzStep]; refine Relation.TransGen.trans ?_ ‹_›; apply Relation.TransGen.single; grind [collatzRel_collatzStep]⟩
          (if n.val % 2 = 0 then acc else acc.insert n) (by grind [CollatzRel])
      else if n.val = 1 then
        acc.insert 1
      else
        acc

/-!
## Tests 1
-/

example : oddCollatz₁ 14 = [1, 5, 7, 11, 13, 17] := by native_decide
example : oddCollatz₁ 5 = [1, 5] := by native_decide
example : oddCollatz₁ 12 = [1, 3, 5] := by native_decide
example : oddCollatz₁ 1 = [1] := by native_decide

/-!
We'll verify `oddCollatz₁` after having verified `oddCollatz₂`.
-/

/-!
## Preliminaries regarding termination

Next, we provide an implementation using well-founded recursion. `oddCollatz₂ n` is guaranteed to
terminate, but calling it requires a proof that the Collatz sequence for `n` is finite.
In order to make this function easier to use, we start by providing a tactic that automatically
proves the finiteness.
-/

theorem acc_collatzRel_collatzStep_iff {n : Nat} (h : n > 1) :
    Acc CollatzRel (collatzStep n) ↔ Acc CollatzRel n := by
  apply Iff.intro
  · exact fun h => ⟨_, fun m hm => by grind [CollatzRel]⟩
  · exact fun h => by grind [Acc.inv, collatzRel_collatzStep]

def tryDecideTermination (n : Nat) (fuel : Nat) (h : Acc CollatzRel n ↔ P) :
    Option (Decidable P) := do
  match fuel with
  | 0 => none
  | fuel + 1 => do
    if hn : n > 1 then
      have := acc_collatzRel_collatzStep_iff hn
      tryDecideTermination (collatzStep n) fuel (this.trans h)
    else
      return .isTrue (h.mp ⟨_, fun m hm => by grind [CollatzRel]⟩)

def extractProof (d : Option (Decidable P)) : Option (PLift P) := do
  match ← d with
  | .isTrue h => return .up h
  | .isFalse _ => none

example : (extractProof (tryDecideTermination 14 50 Iff.rfl)).isSome := by decide

macro "try_decide" : tactic => `(tactic| exact ((extractProof (tryDecideTermination _ 100 Iff.rfl)).get (by decide)).down)

/-!
## Implementation
-/

instance : WellFoundedRelation { m : Nat // Acc CollatzRel m } := Acc.wfRel

def oddCollatz₂ (n : Nat) (h : Acc CollatzRel n := by try_decide) : List Nat :=
  (collectOddCollatz ⟨n, h⟩ ∅).toList
where
  -- We attach a proof that `1` is reachable from `n` in finitely many steps to ensure termination.
  collectOddCollatz (n : { n : Nat // Acc CollatzRel n }) (acc : TreeSet Nat compare) :
      TreeSet Nat compare :=
    if h : n.val > 1 then
      collectOddCollatz ⟨collatzStep n, n.property.inv (by grind [CollatzRel])⟩
        (if n.val % 2 = 0 then acc else acc.insert n.val)
    else if n.val = 1 then
      acc.insert 1
    else
      acc
  termination_by n
  decreasing_by
    grind [CollatzRel]

/-!
## Tests

Observe that while `oddCollatz₂` is guaranteed to terminate, we do not need to manually supply
the termination proofs. These proofs are derived automatically using the `try_decide` tactic.
-/

example : oddCollatz₂ 14 = [1, 5, 7, 11, 13, 17] := by native_decide
example : oddCollatz₂ 5 = [1, 5] := by native_decide
example : oddCollatz₂ 12 = [1, 3, 5] := by native_decide
example : oddCollatz₂ 1 = [1] := by native_decide

/-!
## Missing API
-/

theorem Std.compare_ne_eq [Ord α] [LawfulEqOrd α] {x y : α} :
    compare x y ≠ .eq ↔ x ≠ y := by
  simp

instance : LawfulOrderOrd Nat where
  isLE_compare := by grind [Nat.isLE_compare]
  isGE_compare := by grind [Nat.isGE_compare]

/-!
## Verification
-/

theorem oddCollatz₂_pairwise_distinct {n : Nat} {h : Acc CollatzRel n} :
    (oddCollatz₂ n h).Pairwise (· ≠ ·) := by
  simpa [oddCollatz₂] using TreeSet.distinct_toList (α := Nat) (cmp := compare)

theorem oddCollatz₂_pairwise_lt {n : Nat} {h : Acc CollatzRel n} :
    (oddCollatz₂ n h).Pairwise (· < ·) := by
  simpa [oddCollatz₂, compare_eq_lt] using TreeSet.ordered_toList (α := Nat) (cmp := compare)

theorem mod_two_eq_one_of_mem_oddCollatz₂ {m n : Nat} {h : Acc CollatzRel n} (hm : m ∈ oddCollatz₂ n h) :
    m % 2 = 1 := by
  simp only [oddCollatz₂, TreeSet.mem_toList] at hm
  generalize (⟨n, h⟩ : Subtype _) = n at hm
  generalize hg : (∅ : TreeSet Nat) = acc at hm
  have hm' (k : Nat) : k ∈ acc → k % 2 = 1 := by simp [← hg]
  clear hg
  fun_induction oddCollatz₂.collectOddCollatz n acc <;> grind

theorem transGen_collatzRel_of_mem_oddCollatz₂ {m n : Nat} {h : Acc CollatzRel n} (hm : m ∈ oddCollatz₂ n h)
    (hne : m ≠ n) :
    Relation.TransGen CollatzRel m n := by
  simp only [oddCollatz₂, TreeSet.mem_toList] at hm
  generalize htmp : (⟨n, h⟩ : Subtype _) = s at hm
  rw [show n = s.val by grind] at hne ⊢
  clear htmp
  generalize hg : (∅ : TreeSet Nat) = acc at hm
  have hm' (k : Nat) : k ∈ acc → k ≠ s → Relation.TransGen CollatzRel k s := by simp [← hg]
  clear hg
  generalize htmp : s = n₀ at hm' hne ⊢
  have hs : s = n₀ ∨ Relation.TransGen CollatzRel s n₀ := Or.inl htmp
  clear htmp
  fun_induction oddCollatz₂.collectOddCollatz s acc
  · rename_i n' acc' h' ih
    apply ih hm
    · grind
    · apply Or.inr
      rcases hs with rfl | hs
      · exact .single (collatzRel_collatzStep (by grind))
      · refine .trans ?_ hs
        exact .single (collatzRel_collatzStep (by grind))
  · grind
  · grind

theorem mem_collectOddCollatz_of_mem {n : { n : Nat // Acc CollatzRel n }} {acc : TreeSet Nat}
    {m : Nat} (h : m ∈ acc) :
    m ∈ oddCollatz₂.collectOddCollatz n acc := by
  fun_induction oddCollatz₂.collectOddCollatz n acc <;> grind

theorem mem_self_collectOddCollatz {n : { n : Nat // Acc CollatzRel n }} {acc : TreeSet Nat}
    (h : n.val % 2 = 1) :
    n.val ∈ oddCollatz₂.collectOddCollatz n acc := by
  fun_cases oddCollatz₂.collectOddCollatz n acc <;> grind [mem_collectOddCollatz_of_mem]

attribute [grind =] TreeSet.mem_toList

theorem mem_self_oddCollatz₂ {n : Nat} {h : Acc CollatzRel n} (h' : n % 2 = 1) :
    n ∈ oddCollatz₂ n h := by
  grind [oddCollatz₂, mem_self_collectOddCollatz]

theorem collectOddCollatz_mono {n : { n : Nat // Acc CollatzRel n }} {acc' acc : TreeSet Nat}
    (h : ∀ x, x ∈ acc' → x ∈ acc) {x : Nat} (hx : x ∈ oddCollatz₂.collectOddCollatz n acc') :
    x ∈ oddCollatz₂.collectOddCollatz n acc := by
  fun_induction oddCollatz₂.collectOddCollatz n acc generalizing acc' <;>
    grind [oddCollatz₂.collectOddCollatz]

theorem mem_oddCollatz₂_of_mem_oddCollatz₂_of_collatzRel {k m n : Nat} {hm hn}
    (hmem : k ∈ oddCollatz₂ m hm) (hrel : CollatzRel m n) :
    k ∈ oddCollatz₂ n hn := by
  grind [oddCollatz₂, CollatzRel, oddCollatz₂.collectOddCollatz, collectOddCollatz_mono]

theorem mem_oddCollatz₂_of_mem_oddCollatz₂_of_transGen {k m n : Nat} {hn}
    (hrel : Relation.TransGen CollatzRel m n) (hmem : k ∈ oddCollatz₂ m (hn.invTransGen hrel)) :
    k ∈ oddCollatz₂ n hn := by
  induction hrel
  · grind [mem_oddCollatz₂_of_mem_oddCollatz₂_of_collatzRel]
  · grind [Acc.inv, mem_oddCollatz₂_of_mem_oddCollatz₂_of_collatzRel]

theorem mem_oddCollatz₂_of_transGen {m n : Nat} {hn : Acc CollatzRel n}
    (h : Relation.TransGen CollatzRel m n) (h' : m % 2 = 1) :
    m ∈ oddCollatz₂ n hn := by
  grind [mem_oddCollatz₂_of_mem_oddCollatz₂_of_transGen, mem_self_oddCollatz₂]

theorem mem_oddCollatz₂_iff {m n : Nat} {h : Acc CollatzRel n} :
    m ∈ oddCollatz₂ n h ↔ m % 2 = 1 ∧ (m = n ∨ Relation.TransGen CollatzRel m n) := by
  grind [mod_two_eq_one_of_mem_oddCollatz₂, transGen_collatzRel_of_mem_oddCollatz₂,
    mem_self_oddCollatz₂, mem_oddCollatz₂_of_transGen]

/-!
## Verification 1
-/

theorem collectOddCollatz_eq_collectOddCollatz {n : Nat} {m hm'} (hn : Acc CollatzRel n) :
    oddCollatz₁.collectOddCollatz n ⟨m, hm'⟩ acc = oddCollatz₂.collectOddCollatz ⟨m, sorry⟩ acc := by
  rw [oddCollatz₁.collectOddCollatz]
  have : WellFounded fun (x1 x2 : (_ : { m : Nat // m = n ∨ Relation.TransGen CollatzRel m n }) ×' TreeSet Nat) => CollatzRel x1.fst.val x2.fst.val := by
    have := InvImage.wf (α := (_ : { m : Nat // m = n ∨ Relation.TransGen CollatzRel m n }) ×' TreeSet Nat) (β := { m : Nat // m = n ∨ Relation.TransGen CollatzRel m n }) (r := (CollatzRel ·.val ·.val)) (·.fst)
    apply this
    constructor
    intro s
    have hs : Acc CollatzRel s.val := sorry
    apply InvImage.accessible _ hs
  have hm : Acc CollatzRel m := sorry
  generalize h' : (⟨m, hm⟩ : Subtype _) = s
  have hs : s.val = n ∨ Relation.TransGen CollatzRel s.val n := by grind
  simp only [show Subtype.mk m hm' = Subtype.mk (p := fun x => x = n ∨ Relation.TransGen CollatzRel x n) s.val hs by grind]
  clear h'
  rw [oddCollatz₁.collectOddCollatz, WellFounded.extrinsicFix₂_eq_fix (wf := this)]
  fun_induction oddCollatz₂.collectOddCollatz s acc <;> grind [WellFounded.fix_eq]

theorem oddCollatz₁_eq_oddCollatz₂ {n : Nat} (hn : Acc CollatzRel n) :
    oddCollatz₁ n = oddCollatz₂ n hn := by
  rw [oddCollatz₁, oddCollatz₂]
  grind [collectOddCollatz_eq_collectOddCollatz]

theorem mem_oddCollatz₁_iff {m n : Nat} (h : Acc CollatzRel n) :
    m ∈ oddCollatz₁ n ↔ m % 2 = 1 ∧ (m = n ∨ Relation.TransGen CollatzRel m n) := by
  grind [mem_oddCollatz₂_iff, oddCollatz₁_eq_oddCollatz₂]

/-!
## Prompt

```python3

def get_odd_collatz(n):
    """
    Given a positive integer n, return a sorted list that has the odd numbers in collatz sequence.

    The Collatz conjecture is a conjecture in mathematics that concerns a sequence defined
    as follows: start with any positive integer n. Then each term is obtained from the
    previous term as follows: if the previous term is even, the next term is one half of
    the previous term. If the previous term is odd, the next term is 3 times the previous
    term plus 1. The conjecture is that no matter what value of n, the sequence will always reach 1.

    Note:
        1. Collatz(1) is [1].
        2. returned list sorted in increasing order.

    For example:
    get_odd_collatz(5) returns [1, 5] # The collatz sequence for 5 is [5, 16, 8, 4, 2, 1], so the odd numbers are only 1, and 5.
    """
```

## Canonical solution

```python3
    if n%2==0:
        odd_collatz = []
    else:
        odd_collatz = [n]
    while n > 1:
        if n % 2 == 0:
            n = n/2
        else:
            n = n*3 + 1

        if n%2 == 1:
            odd_collatz.append(int(n))

    return sorted(odd_collatz)
```

## Tests

```python3
def check(candidate):

    # Check some simple cases
    assert candidate(14) == [1, 5, 7, 11, 13, 17]
    assert candidate(5) == [1, 5]
    assert candidate(12) == [1, 3, 5], "This prints if this assert fails 1 (good for debugging!)"

    # Check some edge cases that are easy to work out by hand.
    assert candidate(1) == [1], "This prints if this assert fails 2 (also good for debugging!)"

```
-/
