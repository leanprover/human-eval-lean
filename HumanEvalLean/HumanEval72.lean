module

/-!
## Missing API
-/

@[specialize P]
def decideBallLTImpl (Q : Nat → Prop) (n : Nat) (h : ∀ k, k < n → Q k) (P : ∀ k : Nat, Q k → Bool) : Bool :=
  match n with
  | 0 => true
  | n' + 1 => P n' (h n' (Nat.lt_add_one _)) && decideBallLTImpl Q n' (fun _ h' => h _ (Nat.lt_add_right 1 h')) P

theorem decidableBallLTImpl_iff :
    decideBallLTImpl Q n h P ↔ ∀ (k : Nat) (hk : k < n), P k (h k hk) := by
  induction n
  · simp [decideBallLTImpl]
  · rename_i n ih
    simp [decideBallLTImpl, ih]
    constructor
    · intro h k hk
      by_cases hkn : k = n
      · exact hkn ▸ h.1
      · apply h.2
        omega
    · intro h
      constructor
      · apply h
        exact Nat.lt_add_one _
      · intro k hk
        apply h k
        exact Nat.lt_add_right 1 hk

theorem decideBallLTImpl_eq_false_iff :
    decideBallLTImpl Q n h P = false ↔ ∃ (k : Nat) (hk : k < n), ¬ P k (h k hk) := by
  rw [← Bool.not_eq_true, decidableBallLTImpl_iff]
  simp

instance decidableBallLTImpl (n : Nat) (P : ∀ k, k < n → Prop) [∀ n h, Decidable (P n h)] :
    Decidable (∀ n h, P n h) :=
  match h : decideBallLTImpl _ n (fun _ => id) (P · ·) with
  | false => isFalse (by simpa [decideBallLTImpl_eq_false_iff] using h)
  | true => isTrue (by simpa [decidableBallLTImpl_iff] using h)

attribute [- instance] Nat.decidableBallLT

/-!
## Implementation
-/

/--
Efficient, short-circuiting
-/
def willItFly (q : List Nat) (w : Nat) : Bool :=
  q.sum ≤ w ∧ ∀ (i : Nat) (hi : i < q.length / 2), q[i] = q[q.length - 1 - i]

/-!
## Tests
-/

set_option cbv.warning false

example : willItFly [3, 2, 3] 9 = true := by cbv
example : willItFly [1, 2] 5 = false := by cbv
example : willItFly [3] 5 = true := by cbv
example : willItFly [3, 2, 3] 1 = false := by cbv
example : willItFly [1, 2, 3] 6 = false := by cbv
example : willItFly [5] 5 = true := by cbv

/-!
## Verification
-/

theorem willItFly_iff_le_and_forall :
    willItFly q w ↔ q.sum ≤ w ∧ ∀ (i : Nat) (hi : i < q.length), q[i] = q[q.length - 1 - i] := by
  grind [willItFly]

theorem willItFly_iff_le_and_reverse_eq_self :
    willItFly q w ↔ q.sum ≤ w ∧ q.reverse = q := by
  rw [List.ext_getElem_iff]
  grind [willItFly]

/-!
## Prompt

```python3

def will_it_fly(q,w):
    '''
    Write a function that returns True if the object q will fly, and False otherwise.
    The object q will fly if it's balanced (it is a palindromic list) and the sum of its elements is less than or equal the maximum possible weight w.

    Example:
    will_it_fly([1, 2], 5) ➞ False
    # 1+2 is less than the maximum possible weight, but it's unbalanced.

    will_it_fly([3, 2, 3], 1) ➞ False
    # it's balanced, but 3+2+3 is more than the maximum possible weight.

    will_it_fly([3, 2, 3], 9) ➞ True
    # 3+2+3 is less than the maximum possible weight, and it's balanced.

    will_it_fly([3], 5) ➞ True
    # 3 is less than the maximum possible weight, and it's balanced.
    '''
```

## Canonical solution

```python3
    if sum(q) > w:
        return False

    i, j = 0, len(q)-1
    while i<j:
        if q[i] != q[j]:
            return False
        i+=1
        j-=1
    return True
```

## Tests

```python3
def check(candidate):

    # Check some simple cases
    assert candidate([3, 2, 3], 9) is True
    assert candidate([1, 2], 5) is False
    assert candidate([3], 5) is True
    assert candidate([3, 2, 3], 1) is False


    # Check some edge cases that are easy to work out by hand.
    assert candidate([1, 2, 3], 6) is False
    assert candidate([5], 5) is True

```
-/
