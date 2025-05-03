inductive Op where
  | add
  | sub
  | mul
  | div
  | pow

namespace Op

instance : ToString Op where
  toString
    | add => "+"
    | sub => "-"
    | mul => "*"
    | div => "/"
    | pow => "^"

def prio : Op → Nat
  | add | sub => 1
  | mul | div => 2
  | pow       => 3

def leftAssoc : Op → Bool
  | add | sub => true
  | mul | div => true
  | pow       => false

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
  deriving Inhabited

namespace Expr

instance : ToString Expr where
  toString :=
    let rec go
      | .lit n            => s!"{n}"
      | .app op arg₁ arg₂ => s!"({go arg₁} {op} {go arg₂})"
    go

def eval : Expr → Nat
  | lit n            => n
  | app op arg₁ arg₂ => op.interpret arg₁.eval arg₂.eval

structure ParseState where
  ops    : List Op   := []
  args   : List Nat  := []
  hold   : List Op   := []
  output : List Expr := []
  deriving Inhabited

namespace ParseState

def pushArg (σ : ParseState) (arg : Nat) : ParseState :=
  { σ with output := (lit arg) :: σ.output }

@[simp]
theorem pushArg_ops (σ : ParseState) : (σ.pushArg arg).ops = σ.ops := rfl

def pushOp (σ : ParseState) (op : Op) : ParseState :=
  match σ.hold with
  | [] => { σ with hold := [op] }
  | top :: hold =>
    match compare top.prio op.prio, top.leftAssoc with
    | .lt, _ | .eq, false => { σ with hold := op :: top :: hold }
    | .gt, _ | .eq, true =>
      match σ.output with
      | arg₂ :: arg₁ :: out => { σ with hold := op :: hold, output := .app top arg₁ arg₂ :: out }
      | _                   => σ -- Trash value chosen to easily satisfy `pushOp_ops`.

@[simp]
theorem pushOp_ops (σ : ParseState) : (σ.pushOp op).ops = σ.ops := by
  rw [pushOp]
  repeat (split <;> try rfl)

def finalize (σ : ParseState) : ParseState :=
  match _ : σ.hold, σ.output with
  | op :: hold, arg₂ :: arg₁ :: out => finalize { σ with hold, output := .app op arg₁ arg₂ :: out }
  | _, _                            => σ
  termination_by σ.hold
  decreasing_by simp_all +arith

end ParseState

-- Parses an expression based on the "shunting yard algorithm".
def parse! (ops : List Op) (args : List Nat) : Expr :=
  go { ops, args } |>.output[0]!
where
  go (σ : ParseState) : ParseState :=
    match _ : σ.ops, σ.args with
    | op :: ops, arg :: args => { σ with ops, args }  |>.pushArg arg |>.pushOp op |> go
    | [],        [arg]       => { σ with args := [] } |>.pushArg arg |>.finalize
    | _,         _           => panic! "Invalid parse state"
  termination_by σ.ops
  decreasing_by simp_all +arith

end Expr

def doAlgebra (ops : List Op) (args : List Nat) : Nat :=
  Expr.parse! ops args |>.eval

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
