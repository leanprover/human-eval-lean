theorem List.length_one_eq_getElem_zero {l : List α} (h : l.length = 1) : l = [l[0]] := by
  cases l <;> try cases ‹List _›
  all_goals simp at h ⊢

inductive Op where
  | add
  | sub
  | mul
  | div
  | pow

structure Input where
  ops  : List Op  := []
  args : List Nat := []

@[simp]
abbrev Input.Wellformed (inp : Input) : Prop :=
  inp.args.length = inp.ops.length + 1

abbrev Priority := Nat

namespace Op

def prio : Op → Priority
  | add | sub => 0
  | mul | div => 1
  | pow       => 2

inductive Associativity where
  | left
  | right

def assoc : Op → Associativity
  | add | sub => .left
  | mul | div => .left
  | pow       => .right

inductive Side where
  | left
  | right

-- Given an `op` and another expression of priority `other` appearing on a given `side` of `op`,
-- this function indicates whether `op`'s parsing should occur after that of `other`. For example,
-- if `op` is `+` and `other` appears to the `.right` with a priority of `3`, then `other` should be
-- parsed before `op`. If however `other` had a priority of `1`, then `op` should be parsed before.
def after (op : Op) (other : Priority) (side : Side) : Bool :=
  match op.assoc, side with
  | .left, .left  | .right, .right => op.prio ≤ other
  | .left, .right | .right, .left  => op.prio < other

def interpret : Op → (Nat → Nat → Nat)
  | add => (· + ·)
  | sub => (· - ·)
  | mul => (· * ·)
  | div => (· / ·)
  | pow => (· ^ ·)

end Op

inductive Expr where
  | lit (n : Nat)
  | app (op : Op) (arg₁ arg₂ : Expr)

namespace Expr

def eval : Expr → Nat
  | lit n            => n
  | app op arg₁ arg₂ => op.interpret arg₁.eval arg₂.eval

def lits : Expr → List Nat
  | lit n           => [n]
  | app _ arg₁ arg₂ => arg₁.lits ++ arg₂.lits

def apps : Expr → List Op
  | lit _            => []
  | app op arg₁ arg₂ => arg₁.apps ++ op :: arg₂.apps

def prio : Expr → Priority
  | lit _     => 3
  | app op .. => op.prio

-- An expression is lawful if its structure adheres to the operator priorities (`Op.prio`) and
-- associativity rules (`Op.assoc`).
inductive Lawful : Expr → Prop where
  | lit (n : Nat) : Lawful (lit n)
  | app (h₁ : op.after arg₁.prio .left) (h₂ : op.after arg₂.prio .right) :
      Lawful arg₁ → Lawful arg₂ → Lawful (app op arg₁ arg₂)

-- A given expression is equivalent to a list of operators and arguments if the expression contains
-- the same symbols when read from left to right while also being well-structured (`lawful`).
structure Equivalent (e : Expr) (inp : Input) where
  ops    : e.apps = inp.ops
  args   : e.lits = inp.args
  lawful : Lawful e

infix:50 " ≈ " => Equivalent

abbrev Parser := Input → Option Expr

-- This defines what it means for a parser to be correct: It produces a result iff the input is
-- wellformed (`success`), and when it produces a result it is equivalent to the input (`equiv`).
structure Parser.Correct (par : Parser) where
  success : (∃ e, par inp = some e) ↔ inp.Wellformed
  equiv   : (par inp = some e) → e ≈ inp

structure ParseState extends Input where
  hold   : List Op   := []
  output : List Expr := []

namespace ParseState

instance : Coe Input ParseState where
  coe inp := { inp with }

instance : Coe ParseState Input where
  coe := toInput

def lits (σ : ParseState) : List Nat :=
  go σ.output
where
  go : List Expr → List Nat
  | []       => []
  | e :: out => go out ++ e.lits

theorem output_eq_lits_eq {σ₁ σ₂ : ParseState} (h : σ₁.output = σ₂.output) : σ₁.lits = σ₂.lits := by
  simp only [lits, h]

macro_rules
  | `(tactic| decreasing_tactic) => `(tactic| simp +arith [*])

structure Wellformed (σ : ParseState) where
  external : Input.Wellformed σ
  internal : σ.hold.length = σ.output.length

theorem Wellformed.of_external_cons
    (wf : Wellformed σ) (ho : σ.ops = op :: os) (ha : σ.args = arg :: as) :
    Wellformed { σ with ops := os, args := as } where
  external := have ⟨_, _⟩ := wf; by simp_all
  internal := wf.internal

structure Lawful (σ : ParseState) where
  output : ∀ e ∈ σ.output, e.Lawful
  prios  : ∀ {o os e₁ e₂ es}, (σ.hold = o :: os) → (σ.output = e₂ :: e₁ :: es) →
            (o.after e₁.prio .left) ∧ (o.after e₂.prio .right)

theorem _root_.Input.lawful (inp : Input) : Lawful inp where
  output := nofun
  prios  := nofun

@[simp]
def pushArg (σ : ParseState) (arg : Nat) : ParseState :=
  { σ with output := (lit arg) :: σ.output }

theorem pushArg_lawful (law : Lawful σ) (arg) : Lawful (σ.pushArg arg) := by
  sorry

def pushOp? (σ : ParseState) (op : Op) : Option ParseState :=
  match _ : σ.hold with
  | [] => some { σ with hold := [op] }
  | top :: hold =>
    match top.after op.prio .right, σ.output with
    | true,  _                   => some { σ with hold := op :: top :: hold }
    | false, arg₂ :: arg₁ :: out => pushOp? { σ with hold, output := app top arg₁ arg₂ :: out } op
    | false, _                   => none
termination_by σ.hold.length

macro "pushOp?_cases " h:ident : tactic => `(tactic|(
  rw [pushOp?] at $h:ident
  repeat' split at $h:ident
  all_goals try contradiction
  all_goals try injection $h with $h
  all_goals try rw [← $h]
))

theorem pushOp?_args {σ₁ : ParseState} (h : σ₁.pushOp? op = some σ₂) : σ₁.args = σ₂.args := by
  pushOp?_cases h <;> rw [pushOp?_args h]
termination_by σ₁.hold

theorem pushOp?_ops {σ₁ : ParseState} (h : σ₁.pushOp? op = some σ₂) : σ₁.ops = σ₂.ops := by
  pushOp?_cases h <;> rw [pushOp?_ops h]
termination_by σ₁.hold

theorem pushOp?_lits {σ₁ : ParseState} (h : σ₁.pushOp? op = some σ₂) : σ₁.lits = σ₂.lits := by
  pushOp?_cases h
  all_goals
    first
    | have : σ₁.lits = σ₂.lits := output_eq_lits_eq (h ▸ rfl); simp_all only
    | rw [← pushOp?_lits h]; simp_all [Expr.lits, lits, lits.go]
termination_by σ₁.hold

theorem pushOp?_output_hold_length
    {σ₁ : ParseState} (hp : σ₁.pushOp? op = some σ₂) (hl : σ₁.hold.length < σ₁.output.length) :
    σ₂.output.length - σ₂.hold.length = σ₁.output.length - σ₁.hold.length - 1 := by
  pushOp?_cases hp
  all_goals
    try have hp := pushOp?_output_hold_length hp
    simp_all only [List.length_cons, ← hp]
    omega
termination_by σ₁.hold

theorem pushOp?_hold_length_le_output_length
    {σ₁ : ParseState} (hp : σ₁.pushOp? op = some σ₂) (hl : σ₁.hold.length < σ₁.output.length) :
    σ₂.hold.length ≤ σ₂.output.length := by
  pushOp?_cases hp
  all_goals
    first
      | exact pushOp?_hold_length_le_output_length hp (by simp_all)
      | simp_all +arith [← hp]
termination_by σ₁.hold

theorem pushOp?_some {σ₁ : ParseState} (h : σ₁.hold.length < σ₁.output.length) :
    ∃ σ₂, σ₁.pushOp? op = some σ₂ := by
  rw [pushOp?]
  repeat' split
  all_goals try apply pushOp?_some
  all_goals try cases _ : σ₁.output <;> cases ‹List Expr›
  all_goals simp_all
termination_by σ₁.hold

theorem pushOp?_lawful (law : Lawful σ₁) (h : σ₁.pushOp? op = some σ₂) : Lawful σ₂ := by
  constructor
  case output =>
    intro e he
    pushOp?_cases h
    · rw [← h] at he; exact law.output _ he
    · rw [← h] at he; exact law.output _ he
    case _ top hold hh _ _ e₂ e₁ out ha ho =>
      refine pushOp?_lawful ⟨?_, ?_⟩ h |>.output _ he
      · have := law.prios hh ho
        grind [Lawful, Expr.Lawful]
      · simp
        intro o os e₁ e₂ es ho ha he
        simp_all
        sorry
  case prios =>
    pushOp?_cases h
    · simp; sorry
    · simp; sorry
    · sorry
termination_by σ₁.hold

def push? (σ : ParseState) (arg : Nat) (op : Op) : Option ParseState :=
  σ.pushArg arg |>.pushOp? op

theorem push?_args {σ₁ : ParseState} (h : σ₁.push? arg op = some σ₂) : σ₁.args = σ₂.args := by
  rw [push?, pushArg] at h
  have := pushOp?_args h
  repeat simp_all only

theorem push?_ops {σ₁ : ParseState} (h : σ₁.push? arg op = some σ₂) : σ₁.ops = σ₂.ops := by
  rw [push?, pushArg] at h
  have := pushOp?_ops h
  repeat simp_all only

macro_rules
  | `(tactic| decreasing_tactic) => `(tactic| have := push?_ops ‹_›; simp_all +arith)

theorem push?_lits {σ₁ : ParseState} (h : σ₁.push? arg op = some σ₂) : σ₂.lits = σ₁.lits ++ [arg] :=
  pushOp?_lits h |>.symm

theorem push?_output_hold_length
    {σ₁ : ParseState} (hp : σ₁.push? arg op = some σ₂) (hl : σ₁.hold.length ≤ σ₁.output.length) :
    σ₁.output.length - σ₁.hold.length = σ₂.output.length - σ₂.hold.length := by
  rw [push?, pushArg] at hp
  have hh : σ₁.hold.length < σ₁.output.length + 1 := by omega
  simp only [pushOp?_output_hold_length hp hh, List.length_cons]
  omega

theorem push?_output_length_eq_hold_length
    {σ₁ : ParseState} (hp : σ₁.push? arg op = some σ₂) (he : σ₁.hold.length = σ₁.output.length) :
    σ₂.hold.length = σ₂.output.length := by
  simp only [push?, pushArg] at hp
  have := push?_output_hold_length hp (Nat.le_of_eq he)
  have := pushOp?_hold_length_le_output_length hp (by simp_all)
  omega

theorem push?_lawful (law : Lawful σ₁) (h : σ₁.push? arg op = some σ₂) : Lawful σ₂ :=
  pushOp?_lawful (pushArg_lawful law arg) h

theorem push?_wf (wf : Wellformed σ₁) (arg op) : ∃ σ₂, σ₁.push? arg op = some σ₂ :=
  pushOp?_some <| by simp [wf.internal]

theorem Wellformed.push? (hp : σ₁.push? arg op = some σ₂) (wf : Wellformed σ₁) : Wellformed σ₂ where
  external := by
    have ⟨ex, _⟩ := wf
    simp_all [push?_args hp, push?_ops hp]
  internal := push?_output_length_eq_hold_length hp wf.internal

def finalize (σ : ParseState) : ParseState :=
  match _ : σ.hold, σ.output with
  | op :: hold, arg₂ :: arg₁ :: out => finalize { σ with hold, output := app op arg₁ arg₂ :: out }
  | _, _                            => σ
termination_by σ.hold

@[simp]
theorem finalize_lits (σ : ParseState) : σ.finalize.lits = σ.lits := by
  rw [finalize]
  split
  · rw [finalize_lits]
    simp_all [Expr.lits, lits, lits.go]
  · rfl
termination_by σ.hold

theorem finalize_output_length {σ : ParseState} (h : σ.hold.length < σ.output.length) :
    σ.finalize.output.length = σ.output.length - σ.hold.length := by
  replace { ops, args, hold, output } := σ
  induction hold generalizing output <;> cases output <;> rw [finalize]
  case cons.cons out => cases out <;> simp_all
  all_goals simp_all

theorem finalize_lawful (law : Lawful σ) : Lawful σ.finalize := by
  sorry

def run? (σ : ParseState) : Option ParseState :=
  match _ : σ.ops, σ.args with
  | op :: ops, arg :: args =>
    match _ : { σ with ops, args }.push? arg op with
    | none   => none
    | some σ => run? σ
  | [], [arg] => { σ with args := [] } |>.pushArg arg |>.finalize
  | _, _  => none
termination_by σ.ops

macro "run?_cases " h:ident : tactic => `(tactic|(
  rw [run?] at $h:ident
  repeat' split at $h:ident
  all_goals try contradiction
))

theorem run?_lits {σ₁ : ParseState} (hr : σ₁.run? = some σ₂) : σ₂.lits = σ₁.lits ++ σ₁.args := by
  run?_cases hr
  next h =>
    rw [run?_lits hr]
    have := push?_lits h
    have := push?_args h
    simp_all [lits]
  · injection hr with hr
    rw [← hr, finalize_lits]
    simp_all [Expr.lits, lits, lits.go]
termination_by σ₁.ops.length

theorem run?_output_length
    {σ₁ : ParseState} (hr : σ₁.run? = some σ₂) (hl : σ₁.hold.length ≤ σ₁.output.length) :
    σ₂.output.length = σ₁.output.length + 1 - σ₁.hold.length := by
  run?_cases hr
  next ops₁ _ _ _ _  σ' h =>
    have hl' := pushOp?_hold_length_le_output_length h <| by simp_all +arith
    have := push?_output_hold_length h hl
    simp only [run?_output_length hr hl'] at *
    omega
  · injection hr with hr
    rw [← hr, finalize_output_length]
    repeat simp only [pushArg, List.length_cons]
    omega
termination_by σ₁.ops.length

-- This implies that `parse?` either fails, or returns precisely a single output element.
theorem run?_output_singleton {ops args} (h : run? { ops, args } = some σ) : σ.output.length = 1 :=
  run?_output_length h .refl

theorem run?_lawful (law : Lawful σ₁) (hr : σ₁.run? = some σ₂) : Lawful σ₂ := by
  run?_cases hr
  · sorry
  · sorry

theorem run?_wf (wf : Wellformed σ₁) : ∃ σ₂, σ₁.run? = some σ₂ := by
  rw [run?]
  repeat split
  next op _ arg _ ho ha _ =>
    have := push?_wf (wf.of_external_cons ho ha) arg op
    simp_all
  next ho ha _ h =>
    exact run?_wf <| (wf.of_external_cons ho ha).push? h
  · simp
  next h _ =>
    have ⟨_, _⟩ := wf
    cases ho : σ₁.ops <;> cases ha : σ₁.args <;> try specialize h _ _ _ _ ho ha
    all_goals simp_all
termination_by σ₁.ops.length

theorem run?_some {σ₁ : ParseState} (hr : σ₁.run? = some σ₂) : Input.Wellformed σ₁ := by
  run?_cases hr
  next ops _ _ _ _ σ₂ h =>
    have := run?_some hr
    have := push?_args h
    have := push?_ops h
    simp_all
  · simp_all
termination_by σ₁.ops.length

end ParseState

-- Parses an expression based on the "shunting yard algorithm".
def parse? : Parser := fun inp =>
  match h : ParseState.run? inp with
  | none   => none
  | some σ => σ.output[0]'(by simp [ParseState.run?_output_singleton h])

theorem parse?_some_to_run?_some (h : parse? inp = some e) :
    ∃ σ, ParseState.run? inp = some σ ∧ σ.output = [e] := by
  rw [parse?] at h
  split at h
  · contradiction
  next σ hr =>
    simp_all only [Option.some.injEq, exists_eq_left']
    have hs := ParseState.run?_output_singleton hr
    exact h ▸ List.length_one_eq_getElem_zero hs

theorem parse?_some_iff : (∃ e, parse? inp = some e) ↔ inp.Wellformed where
  mp h := by
    have ⟨_, h, _⟩ := parse?_some_to_run?_some h.choose_spec
    exact ParseState.run?_some h
  mpr h := by
    have := @ParseState.run?_wf inp ⟨h, rfl⟩
    rw [parse?]
    split <;> simp_all

theorem parse?_lits_eq_args (h : parse? inp = some e) : e.lits = inp.args := by
  have ⟨_, h, _⟩ := parse?_some_to_run?_some h
  have := ParseState.run?_lits h
  simp_all [ParseState.lits, ParseState.lits.go]

theorem parse?_apps_eq_ops (h : parse? inp = some e) : e.apps = inp.ops := by
  have ⟨σ, h, ho⟩ := parse?_some_to_run?_some h
  sorry

theorem parse?_lawful (h : parse? inp = some e) : Lawful e := by
  have ⟨_, h, _⟩ := parse?_some_to_run?_some h
  have := ParseState.run?_lawful inp.lawful h
  grind [ParseState.Lawful, Expr.Lawful]

theorem parse?_some_equiv (h : parse? inp = some e) : e ≈ inp where
  ops    := parse?_apps_eq_ops h
  args   := parse?_lits_eq_args h
  lawful := parse?_lawful h

theorem parse?_correct : Parser.Correct parse? where
  success := Expr.parse?_some_iff
  equiv   := Expr.parse?_some_equiv

end Expr

def doAlgebra (ops : List Op) (args : List Nat) (h : Input.Wellformed { ops, args } := by decide) : Nat :=
  have parse?_isSome := Option.isSome_iff_exists.mpr <| Expr.parse?_some_iff.mpr h
  Expr.parse? { ops, args } |>.get parse?_isSome |>.eval

example : doAlgebra [.add, .mul, .sub] [2, 3, 4, 5] = 9  := by native_decide
example : doAlgebra [.pow, .mul, .add] [2, 3, 4, 5] = 37 := by native_decide
example : doAlgebra [.add, .mul, .sub] [2, 3, 4, 5] = 9  := by native_decide
example : doAlgebra [.div, .mul]       [7, 3, 4]    = 8  := by native_decide

/-!
## Prompt

```python3

def do_algebra(operator, operand):
    """
    Given two lists operator, and operand. The first list has basic algebra operations, and
    the second list is a list of integers. Use the two given lists to build the algebric
    expression and return the evaluation of this expression.

    The basic algebra operations:
    Addition ( + )
    Subtraction ( - )
    Multiplication ( * )
    Floor division ( // )
    Exponentiation ( ** )

    Example:
    operator['+', '*', '-']
    array = [2, 3, 4, 5]
    result = 2 + 3 * 4 - 5
    => result = 9

    Note:
        The length of operator list is equal to the length of operand list minus one.
        Operand is a list of of non-negative integers.
        Operator list has at least one operator, and operand list has at least two operands.

    """
```

## Canonical solution

```python3
    expression = str(operand[0])
    for oprt, oprn in zip(operator, operand[1:]):
        expression+= oprt + str(oprn)
    return eval(expression)
```

## Tests

```python3
def check(candidate):

    # Check some simple cases
    assert candidate(['**', '*', '+'], [2, 3, 4, 5]) == 37
    assert candidate(['+', '*', '-'], [2, 3, 4, 5]) == 9
    assert candidate(['//', '*'], [7, 3, 4]) == 8, "This prints if this assert fails 1 (good for debugging!)"

    # Check some edge cases that are easy to work out by hand.
    assert True, "This prints if this assert fails 2 (also good for debugging!)"

```
-/
