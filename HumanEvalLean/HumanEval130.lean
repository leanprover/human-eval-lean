import Std
import Lean.LibrarySuggestions.Default
open Std Std.Do

set_option mvcgen.warning false

/-!
## Implementation
-/

def tri (n : Nat) : List Nat := Id.run do
  let mut xs : Array Nat := #[]
  let mut lastₑ := 1
  let mut lastₒ := 0
  for i in 0...=n do
    if i % 2 == 0 then
      lastₑ := i / 2 + 1
      xs := xs.push lastₑ
    else
      lastₒ := (lastₑ + lastₒ + (i + 3) / 2)
      xs := xs.push lastₒ
  return xs.toList

/-!
## Tests
-/

example : tri 3 = [1, 3, 2, 8] := by native_decide
example : tri 4 = [1, 3, 2, 8, 3] := by native_decide
example : tri 5 = [1, 3, 2, 8, 3, 15] := by native_decide
example : tri 6 = [1, 3, 2, 8, 3, 15, 4] := by native_decide
example : tri 7 = [1, 3, 2, 8, 3, 15, 4, 24] := by native_decide
example : tri 8 = [1, 3, 2, 8, 3, 15, 4, 24, 5] := by native_decide
example : tri 9 = [1, 3, 2, 8, 3, 15, 4, 24, 5, 35] := by native_decide
example : tri 20 = [1, 3, 2, 8, 3, 15, 4, 24, 5, 35, 6, 48, 7, 63, 8, 80, 9, 99, 10, 120, 11] := by native_decide
example : tri 0 = [1] := by native_decide
example : tri 1 = [1, 3] := by native_decide

/-!
## Verification
-/

def Inv₁ (cur : (0...=n).toList.Cursor) (xs : Array Nat) : Prop :=
  xs.size = cur.pos

def Inv₂ (lastₑ lastₒ : Nat) (xs : Array Nat) : Prop :=
  xs.size < 2 → (lastₑ, lastₒ) = (1, 0)

def Inv₃ (lastₑ lastₒ : Nat) (xs : Array Nat) : Prop :=
  ∀ (_ : 2 ≤ xs.size) (i : Nat) (_ : i = xs.size - 2 ∨ i = xs.size - 1),
    if i % 2 = 0 then lastₑ = xs[i] else lastₒ = xs[i]

def Inv₄ (xs : Array Nat) : Prop :=
  ((_ : 0 < xs.size) → xs[0] = 1) ∧ ((_ : 1 < xs.size) → xs[1] = 3)

def Inv₅ (xs : Array Nat) : Prop :=
  ∀ (i : Nat) (_ : i + 2 < xs.size),
    if i % 2 = 0 then xs[i + 2] = 1 + (i + 2) / 2 else xs[i + 2] = xs[i] + xs[i + 1] + (i + 5) / 2

-- theorem inv₁ (h₁ : inv₁ )

theorem Nat.eq_add_of_toList_rcc_eq_append_cons {a b : Nat} {pref cur suff}
    (h : (a...=b).toList = pref ++ cur :: suff) :
    cur = a + pref.length := by
  have := Rcc.eq_succMany?_of_toList_eq_append_cons h
  grind [PRange.Nat.succMany?_eq]

@[simp, grind =]
theorem length_tri : (tri n).length = n + 1 := by
  generalize hwp : tri n = wp
  apply Id.of_wp_run_eq hwp
  mvcgen
  invariants
  · ⇓⟨cur, lastₑ, lastₒ, xs⟩ => ⌜xs.size = cur.pos⌝
  with grind [Nat.length_toList_rcc]

theorem bla {n i} {h : i ≤ n} :
    (tri n)[i]! =
      if i = 0 then
        1
      else if i = 1 then
        3
      else if i % 2 = 0 then
        1 + i / 2
      else
        (tri n)[i - 2]! + (tri n)[i - 1]! + (i + 3) / 2 := by
  let wp := tri n
  have hwp : tri n = wp := rfl
  simp only [hwp]
  clear_value wp
  apply Id.of_wp_run_eq hwp
  mvcgen
  invariants
  · ⇓⟨cur, lastₑ, lastₒ, xs⟩ =>
      ⌜Inv₁ cur xs ∧ Inv₂ lastₑ lastₒ xs ∧ Inv₃ lastₑ lastₒ xs ∧ Inv₄ xs ∧ Inv₅ xs⌝
  case vc1 pref cur suff h_append_cons args lastₑ args₂ lastₒ' xs hmod lastₑ' xs' hinv =>
    obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hinv
    have hcur := Nat.eq_add_of_toList_rcc_eq_append_cons h_append_cons
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · grind [Inv₁]
    · grind [Inv₁, Inv₂]
    · simp only [Inv₃] at h₃ ⊢
      intro hge i hi
      by_cases xs.size < 2
      · grind [Inv₁]
      · by_cases i = xs.size
        · grind [Inv₁]
        · specialize h₃ (by grind) i (by grind)
          grind [Inv₁]
    · grind [Inv₁, Inv₄]
    · grind [Inv₁, Inv₅]
  case vc2 pref cur suff h_append_cons args lastₑ args₂ lastₒ xs hmod lastₒ' xs' hinv =>
    obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hinv
    have hcur := Nat.eq_add_of_toList_rcc_eq_append_cons h_append_cons
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · grind [Inv₁]
    · grind [Inv₁, Inv₂]
    · simp only [Inv₃] at h₃ ⊢
      intro hge i hi
      by_cases xs.size < 2
      · grind [Inv₂, Inv₄]
      · by_cases i = xs.size
        · grind [Inv₁]
        · specialize h₃ (by grind) i (by grind)
          grind [Inv₁]
    · grind [Inv₁, Inv₂, Inv₄]
    · simp only [Inv₅] at h₅ ⊢
      intro i hi
      by_cases i + 2 = xs.size
      · have : xs'[i + 2] = lastₒ' := by grind
        simp only [this, lastₒ']
        have : i % 2 = 1 := by grind [Inv₁]
        rw [if_neg (by grind [Inv₁])]
        have : cur = i + 2 := by grind [Inv₁]
        simp only [Inv₃] at h₃
        have h₃₁ := h₃ (by grind) (i + 1) (by grind)
        have h₃₂ := h₃ (by grind) i (by grind)
        grind
      · grind
  case vc3 => grind [Inv₁, Inv₂, Inv₃, Inv₄, Inv₅]
  case vc4 args hinv =>
    obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hinv
    have : args.2.2.size = n + 1 := by grind [Inv₁, Nat.length_toList_rcc]
    split
    · grind [Inv₄]
    · split
      · grind [Inv₄]
      · simp only [Inv₅] at h₅
        specialize h₅ (i - 2) (by grind)
        grind

/--
The zero-th value is `1`. This would also follow from `tri_of_even`.
-/
theorem tri_zero :
    (tri n)[0] = 1 := by
  have := bla (n := n) (i := 0) (h := by grind)
  grind

/--
The first value is `3`.
-/
theorem tri_one (h : 1 ≤ n) :
    (tri n)[1]'(by grind) = 3 := by
  have := bla (n := n) (i := 1) (h := h)
  grind

/--
The value at even position `i` is `1 + (i / 2)`.
-/
theorem tri_of_even (h : i ≤ n) (hi : i % 2 = 0) :
    (tri n)[i]'(by grind) = 1 + (i / 2) := by
  have := bla (n := n) (i := i) (h := h)
  grind

/--
The value at even position `i ≥ 2` is the sum of its two predecessors plus `(i + 3) / 2`.
-/
theorem tri_of_odd₁ (h : i ≤ n) (hge : 2 ≤ i) (hi : i % 2 = 1) :
    (tri n)[i]'(by grind) = (tri n)[i - 2]'(by grind) + (tri n)[i - 1]'(by grind) + (i + 3) / 2 := by
  have := bla (n := n) (i := i) (h := h)
  grind

/--
This is the property specified for the value at even positions:
The value at even position `i ≥ 2` is the sum of its two predecessors and its immediate successor.
-/
theorem tri_of_odd₂ (h : i + 1 ≤ n) (hge : 2 ≤ i) (hi : i % 2 = 1) :
    (tri n)[i]'(by grind) = (tri n)[i - 2]'(by grind) + (tri n)[i - 1]'(by grind) + (tri n)[i + 1]'(by grind) := by
  grind [tri_of_odd₁, tri_of_even]

theorem prefix_tri_of_le (h : m ≤ n) :
    tri m <+: tri n := by
  simp only [List.IsPrefix]
  refine ⟨(tri n).drop (m + 1), ?_⟩
  apply List.ext_getElem
  · grind
  · intro i _ _
    by_cases i ≤ m
    · rw [List.getElem_append_left (by grind)]
      induction i using Nat.strongRecOn with | ind i ih
      grind [tri_of_even, tri_of_odd₁, tri_one]
    · grind

/-!
## Prompt

```python3

def tri(n):
    """Everyone knows Fibonacci sequence, it was studied deeply by mathematicians in
    the last couple centuries. However, what people don't know is Tribonacci sequence.
    Tribonacci sequence is defined by the recurrence:
    tri(1) = 3
    tri(n) = 1 + n / 2, if n is even.
    tri(n) =  tri(n - 1) + tri(n - 2) + tri(n + 1), if n is odd.
    For example:
    tri(2) = 1 + (2 / 2) = 2
    tri(4) = 3
    tri(3) = tri(2) + tri(1) + tri(4)
           = 2 + 3 + 3 = 8
    You are given a non-negative integer number n, you have to a return a list of the
    first n + 1 numbers of the Tribonacci sequence.
    Examples:
    tri(3) = [1, 3, 2, 8]
    """
```

## Canonical solution

```python3
    if n == 0:
        return [1]
    my_tri = [1, 3]
    for i in range(2, n + 1):
        if i % 2 == 0:
            my_tri.append(i / 2 + 1)
        else:
            my_tri.append(my_tri[i - 1] + my_tri[i - 2] + (i + 3) / 2)
    return my_tri
```

## Tests

```python3
def check(candidate):

    # Check some simple cases

    assert candidate(3) == [1, 3, 2.0, 8.0]
    assert candidate(4) == [1, 3, 2.0, 8.0, 3.0]
    assert candidate(5) == [1, 3, 2.0, 8.0, 3.0, 15.0]
    assert candidate(6) == [1, 3, 2.0, 8.0, 3.0, 15.0, 4.0]
    assert candidate(7) == [1, 3, 2.0, 8.0, 3.0, 15.0, 4.0, 24.0]
    assert candidate(8) == [1, 3, 2.0, 8.0, 3.0, 15.0, 4.0, 24.0, 5.0]
    assert candidate(9) == [1, 3, 2.0, 8.0, 3.0, 15.0, 4.0, 24.0, 5.0, 35.0]
    assert candidate(20) == [1, 3, 2.0, 8.0, 3.0, 15.0, 4.0, 24.0, 5.0, 35.0, 6.0, 48.0, 7.0, 63.0, 8.0, 80.0, 9.0, 99.0, 10.0, 120.0, 11.0]

    # Check some edge cases that are easy to work out by hand.
    assert candidate(0) == [1]
    assert candidate(1) == [1, 3]
```
-/
