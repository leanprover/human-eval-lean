module

def Char.shiftByFour (c : Char) : Char :=
  Char.ofNat ((c.toNat - 'a'.toNat + 4) % 26 + 'a'.toNat)

def encrypt (s : String) : String :=
  s.map Char.shiftByFour

example : encrypt "hi" = "lm" := by native_decide
example : encrypt "asdfghjkl" = "ewhjklnop" := by native_decide
example : encrypt "gf" = "kj" := by native_decide
example : encrypt "et" = "ix" := by native_decide
example : encrypt "a" = "e" := by native_decide
example : encrypt "faewfawefaewg" = "jeiajeaijeiak" := by native_decide
example : encrypt "hellomyfriend" = "lippsqcjvmirh" := by native_decide
example : encrypt "dxzdlmnilfuhmilufhlihufnmlimnufhlimnufhfucufh" = "hbdhpqrmpjylqmpyjlpmlyjrqpmqryjlpmqryjljygyjl" := by native_decide

def Char.unshiftByFour (c : Char) : Char :=
  Char.ofNat ((c.toNat - 'a'.toNat + 22) % 26 + 'a'.toNat)

def decrypt (s : String) : String :=
  s.map Char.unshiftByFour

theorem Char.toNat_ofNat_of_isValidChar {n : Nat} (h : n.isValidChar) : (Char.ofNat n).toNat = n := by
  simp [ofNat, h, ofNatAux]

@[simp]
theorem Char.unshiftByFour_shiftByFour {c : Char} (hc : c.isLower) : c.shiftByFour.unshiftByFour = c := by
  simp [Char.isLower, Char.shiftByFour, Char.unshiftByFour, UInt32.le_iff_toNat_le,
    ← Char.toNat_inj] at *
  grind [toNat_ofNat_of_isValidChar]

theorem List.map_eq_self {f : α → α} {l : List α} (hf : ∀ a ∈ l, f a = a) : l.map f = l := by
  induction l <;> grind

theorem decryptShift_encryptShift (s : String) (hs : ∀ c ∈ s.toList, c.isLower) :
    decrypt (encrypt s) = s := by
  simpa [← String.toList_inj, decrypt, encrypt] using
    List.map_eq_self (by grind [Char.unshiftByFour_shiftByFour])

/-!
## Prompt

```python3

def encrypt(s):
    """Create a function encrypt that takes a string as an argument and
    returns a string encrypted with the alphabet being rotated.
    The alphabet should be rotated in a manner such that the letters
    shift down by two multiplied to two places.
    For example:
    encrypt('hi') returns 'lm'
    encrypt('asdfghjkl') returns 'ewhjklnop'
    encrypt('gf') returns 'kj'
    encrypt('et') returns 'ix'
    """
```

## Canonical solution

```python3
    d = 'abcdefghijklmnopqrstuvwxyz'
    out = ''
    for c in s:
        if c in d:
            out += d[(d.index(c)+2*2) % 26]
        else:
            out += c
    return out
```

## Tests

```python3
def check(candidate):

    # Check some simple cases
    assert candidate('hi') == 'lm', "This prints if this assert fails 1 (good for debugging!)"
    assert candidate('asdfghjkl') == 'ewhjklnop', "This prints if this assert fails 1 (good for debugging!)"
    assert candidate('gf') == 'kj', "This prints if this assert fails 1 (good for debugging!)"
    assert candidate('et') == 'ix', "This prints if this assert fails 1 (good for debugging!)"

    assert candidate('faewfawefaewg')=='jeiajeaijeiak', "This prints if this assert fails 1 (good for debugging!)"
    assert candidate('hellomyfriend')=='lippsqcjvmirh', "This prints if this assert fails 2 (good for debugging!)"
    assert candidate('dxzdlmnilfuhmilufhlihufnmlimnufhlimnufhfucufh')=='hbdhpqrmpjylqmpyjlpmlyjrqpmqryjlpmqryjljygyjl', "This prints if this assert fails 3 (good for debugging!)"

    # Check some edge cases that are easy to work out by hand.
    assert candidate('a')=='e', "This prints if this assert fails 2 (also good for debugging!)"

```
-/
