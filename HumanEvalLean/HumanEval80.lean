module
import Std.Tactic.Do
import Std
import all Init.Data.Range.Polymorphic.UpwardEnumerable -- UpwardEnumerable.least not exposed

open Std Std.Do

def isHappy (s : String) : Bool := Id.run do
  if s.length < 3 then
    return false

  let a := s.toList.toArray
  for h : i in *...a.size - 2 do
    if a[i] = a[i + 1] ∨ a[i + 1] = a[i + 2] ∨ a[i] = a[i + 2] then
      return false

  return true

theorem Nat.eq_add_of_toList_rio_eq_append_cons {a : Nat} {pref cur suff}
    (h : (*...a).toList = pref ++ cur :: suff) :
    cur = pref.length := by
  have := Rio.eq_succMany?_of_toList_eq_append_cons h
  simpa [PRange.UpwardEnumerable.least, PRange.least?] using this

set_option mvcgen.warning false in
theorem isHappy_iff {s : String} :
    isHappy s = true ↔ 3 ≤ s.length ∧ (∀ (a b c : Char), [a, b, c] <:+: s.toList → a ≠ b ∧ b ≠ c ∧ a ≠ c) := by
  generalize hwp : isHappy s = wp
  apply Id.of_wp_run_eq hwp
  mvcgen
  invariants
  · .withEarlyReturn
      (fun cur _ => ⌜∀ a b c : Char, [a, b, c] <:+: s.toList.take (cur.pos + 2) → a ≠ b ∧ b ≠ c ∧ a ≠ c⌝)
      (fun r _ => ⌜r = false ∧ ∃ a b c : Char, [a, b, c] <:+: s.toList ∧ (a = b ∨ b = c ∨ a = c)⌝)
  next => grind
  next hsl a pref cur suff h b heq ih =>
    subst a
    obtain rfl := Nat.eq_add_of_toList_rio_eq_append_cons h
    have := congrArg List.length h
    simp only [List.size_toArray, String.length_toList, Rio.length_toList, Nat.size_rio,
      List.length_append, List.length_cons, reduceCtorEq, List.Cursor.pos_mk, ne_eq, false_and,
      Option.some.injEq, Bool.false_eq, true_and, and_self_left, exists_eq_left, false_or] at this ⊢
    refine ⟨_, _, _, ?_, heq⟩
    simp only [List.getElem_toArray]
    rw [List.infix_iff_getElem?]
    refine ⟨pref.length, ?_⟩
    simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, String.length_toList]
    exact ⟨by grind, by rintro (_|_|_|i) hi <;> grind⟩
  next hsl a pref cur suff h b heq ih =>
    subst a
    obtain rfl := Nat.eq_add_of_toList_rio_eq_append_cons h
    have := congrArg List.length h
    simp only [List.size_toArray, String.length_toList, Std.Rio.length_toList, Nat.size_rio,
      List.length_append, List.length_cons, List.Cursor.pos_mk, ne_eq, reduceCtorEq, false_and,
      and_false, exists_const, or_false, List.length_nil, Nat.zero_add, true_and] at this ih ⊢
    intro a b c
    rw [List.take_add_one, getElem?_pos _ _ (by simp; omega), Option.toList_some,
      List.infix_concat_iff, or_imp]
    refine ⟨?_, ih.2 a b c⟩
    simp only [List.take_add_one, List.append_assoc]
    repeat rw [getElem?_pos _ _ (by simp; omega), Option.toList_some]
    rw [← List.nil_append [a, b, c], List.suffix_append_inj_of_length_eq (by simp)]
    grind
  next h a =>
    simp
    intro a b c hs
    have := hs.length_le
    grind
  next h a r h₁ h₂ =>
    subst a
    simp [h₁] at ⊢ h₂
    refine ⟨by omega, ?_⟩
    rwa [Nat.sub_add_cancel (by omega), ← String.length_toList, List.take_length] at h₂
  next => grind

/-!
## Prompt

```python3

def is_happy(s):
    """You are given a string s.
    Your task is to check if the string is happy or not.
    A string is happy if its length is at least 3 and every 3 consecutive letters are distinct
    For example:
    is_happy(a) => False
    is_happy(aa) => False
    is_happy(abcd) => True
    is_happy(aabb) => False
    is_happy(adb) => True
    is_happy(xyy) => False
    """
```

## Canonical solution

```python3
    if len(s) < 3:
      return False

    for i in range(len(s) - 2):

      if s[i] == s[i+1] or s[i+1] == s[i+2] or s[i] == s[i+2]:
        return False
    return True
```

## Tests

```python3
def check(candidate):

    # Check some simple cases
    assert candidate("a") == False , "a"
    assert candidate("aa") == False , "aa"
    assert candidate("abcd") == True , "abcd"
    assert candidate("aabb") == False , "aabb"
    assert candidate("adb") == True , "adb"
    assert candidate("xyy") == False , "xyy"
    assert candidate("iopaxpoi") == True , "iopaxpoi"
    assert candidate("iopaxioi") == False , "iopaxioi"
```
-/
