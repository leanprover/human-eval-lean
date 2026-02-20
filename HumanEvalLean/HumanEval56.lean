module

import HumanEvalLean.Common.Brackets
meta import HumanEvalLean.Common.Brackets

def correctBracketing (s : String) : Bool :=
  isBalanced '<' '>' s

example : correctBracketing "<>" = true := by native_decide
example : correctBracketing "<<><>>" = true := by native_decide
example : correctBracketing "<><><<><>><>" = true := by native_decide
example : correctBracketing "<><><<<><><>><>><<><><<>>>" = true := by native_decide
example : correctBracketing "<<<><>>>>" = false := by native_decide
example : correctBracketing "><<>" = false := by native_decide
example : correctBracketing "<" = false := by native_decide
example : correctBracketing "<<<<" = false := by native_decide
example : correctBracketing ">" = false := by native_decide
example : correctBracketing "<<>" = false := by native_decide
example : correctBracketing "<><><<><>><>>" = false := by native_decide
example : correctBracketing "<><><<><>><>>><>" = false := by native_decide

theorem correctBracketing_eq_true_iff {s : String} :
    correctBracketing s = true ↔ IsBalanced (parens '<' '>' s) := by
  rw [correctBracketing, isBalanced_eq_true_iff (by simp)]

/-!
## Prompt

```python3


def correct_bracketing(brackets: str):
    """ brackets is a string of "<" and ">".
    return True if every opening bracket has a corresponding closing bracket.

    >>> correct_bracketing("<")
    False
    >>> correct_bracketing("<>")
    True
    >>> correct_bracketing("<<><>>")
    True
    >>> correct_bracketing("><<>")
    False
    """
```

## Canonical solution

```python3
    depth = 0
    for b in brackets:
        if b == "<":
            depth += 1
        else:
            depth -= 1
        if depth < 0:
            return False
    return depth == 0
```

## Tests

```python3


METADATA = {}


def check(candidate):
    assert candidate("<>")
    assert candidate("<<><>>")
    assert candidate("<><><<><>><>")
    assert candidate("<><><<<><><>><>><<><><<>>>")
    assert not candidate("<<<><>>>>")
    assert not candidate("><<>")
    assert not candidate("<")
    assert not candidate("<<<<")
    assert not candidate(">")
    assert not candidate("<<>")
    assert not candidate("<><><<><>><>><<>")
    assert not candidate("<><><<><>><>>><>")

```
-/
