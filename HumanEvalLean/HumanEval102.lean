module

def Nat.isEven (n : Nat) : Bool :=
  n % 2 = 0

def chooseNum (lo hi : Nat) : Int :=
  match compare lo hi, hi.isEven with
  | .lt, true | .eq, true => hi
  | .lt, false            => hi - 1
  | _, _                  => -1

example : chooseNum 12 15 = 14       := rfl
example : chooseNum 13 12 = -1       := rfl
example : chooseNum 12 15 = 14       := rfl
example : chooseNum 13 12 = -1       := rfl
example : chooseNum 33 12354 = 12354 := rfl
example : chooseNum 5234 5233 = -1   := rfl
example : chooseNum 6 29 = 28        := rfl
example : chooseNum 27 10 = -1       := rfl
example : chooseNum 7 7 = -1         := rfl
example : chooseNum 546 546 = 546    := rfl

macro "chooseNum_cases" lo:ident hi:ident : tactic => `(tactic|(
  cases _ : compare $lo $hi <;> cases _ : $(hi).isEven <;> simp only [chooseNum, *] at *
))

macro "chooseNum_trivial" : tactic => `(tactic|(
  simp only [(· ∈ ·), Nat.isEven, Nat.compare_eq_eq, Nat.compare_eq_lt, Nat.compare_eq_gt,
             decide_eq_false_iff_not, decide_eq_true_eq] at *
  omega
))

namespace Std.Legacy.Range

-- A specification for `m` being the even maximum of range `r`.
structure EvenMax (r : Range) (m : Nat) : Prop where
  mem      : m ∈ r                     := by chooseNum_trivial
  even     : m.isEven                  := by chooseNum_trivial
  max_even : ∀ n ∈ r, n.isEven → n ≤ m := by chooseNum_trivial

namespace EvenMax

theorem unique (h₁ : [lo:hi].EvenMax m₁) (h₂ : [lo:hi].EvenMax m₂) : m₁ = m₂ :=
  Nat.le_antisymm (h₂.max_even _ h₁.mem h₁.even) (h₁.max_even _ h₂.mem h₂.even)

theorem to_chooseNum (h : [lo:hi + 1].EvenMax m) : chooseNum lo hi = m := by
  have ⟨_, _, _⟩ := h
  chooseNum_cases lo hi <;> try chooseNum_trivial
  · have : [lo:hi + 1].EvenMax (hi - 1) := { }
    simp only [h.unique this, Nat.isEven, decide_eq_true_eq, decide_eq_false_iff_not] at *
    omega
  · rw [h.unique { : [lo:hi + 1].EvenMax hi }]

-- A given number `m` is the even maximum of the range `{lo, ..., hi}` iff `chooseNum` says so.
theorem iff_chooseNum : [lo:hi + 1].EvenMax m ↔ chooseNum lo hi = m where
  mp    := EvenMax.to_chooseNum
  mpr h := by constructor <;> chooseNum_cases lo hi <;> chooseNum_trivial

-- There does not exist an even maximum of the range `{lo, ..., hi}` iff `chooseNum` returns `-1`.
theorem not_iff_chooseNum : ¬(∃ m, [lo:hi + 1].EvenMax m) ↔ (chooseNum lo hi = -1) where
  mpr h := fun ⟨_, ⟨_, _, _⟩⟩ => by chooseNum_cases lo hi <;> chooseNum_trivial
  mp h  := by
    chooseNum_cases lo hi <;> exfalso
    · exact h ⟨hi - 1, {}⟩
    · exact h ⟨hi, {}⟩
    · exact h ⟨hi, {}⟩

end Std.Legacy.Range.EvenMax

/-!
## Prompt

```python3

def choose_num(x, y):
    """This function takes two positive numbers x and y and returns the
    biggest even integer number that is in the range [x, y] inclusive. If
    there's no such number, then the function should return -1.

    For example:
    choose_num(12, 15) = 14
    choose_num(13, 12) = -1
    """
```

## Canonical solution

```python3
    if x > y:
        return -1
    if y % 2 == 0:
        return y
    if x == y:
        return -1
    return y - 1
```

## Tests

```python3
def check(candidate):

    # Check some simple cases
    assert candidate(12, 15) == 14
    assert candidate(13, 12) == -1
    assert candidate(33, 12354) == 12354
    assert candidate(5234, 5233) == -1
    assert candidate(6, 29) == 28
    assert candidate(27, 10) == -1

    # Check some edge cases that are easy to work out by hand.
    assert candidate(7, 7) == -1
    assert candidate(546, 546) == 546

```
-/
