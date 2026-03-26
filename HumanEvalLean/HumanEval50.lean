module

def Char.shiftByFive (c : Char) : Char :=
  Char.ofNat ((c.toNat - 'a'.toNat + 5) % 26 + 'a'.toNat)

def Char.unshiftByFive (c : Char) : Char :=
  Char.ofNat ((c.toNat - 'a'.toNat + 21) % 26 + 'a'.toNat)

def encodeShift (s : String) : String :=
  s.map Char.shiftByFive

def decodeShift (s : String) : String :=
  s.map Char.unshiftByFive

theorem Char.toNat_ofNat_of_isValidChar {n : Nat} (h : n.isValidChar) : (Char.ofNat n).toNat = n := by
  simp [ofNat, h, ofNatAux]

@[simp]
theorem Char.unshiftByFive_shiftByFive {c : Char} (hc : c.isLower) : c.shiftByFive.unshiftByFive = c := by
  simp [Char.isLower, Char.shiftByFive, Char.unshiftByFive, UInt32.le_iff_toNat_le,
    ← Char.toNat_inj] at *
  grind [toNat_ofNat_of_isValidChar]

theorem List.map_eq_self {f : α → α} {l : List α} (hf : ∀ a ∈ l, f a = a) : l.map f = l := by
  induction l <;> grind

theorem decodeShift_encodeShift (s : String) (hs : ∀ c ∈ s.toList, c.isLower) :
    decodeShift (encodeShift s) = s := by
  simpa [← String.toList_inj, decodeShift, encodeShift] using
    List.map_eq_self (by grind [Char.unshiftByFive_shiftByFive])

/-!
## Prompt

```python3


def encode_shift(s: str):
    """
    returns encoded string by shifting every character by 5 in the alphabet.
    """
    return "".join([chr(((ord(ch) + 5 - ord("a")) % 26) + ord("a")) for ch in s])


def decode_shift(s: str):
    """
    takes as input string encoded with encode_shift function. Returns decoded string.
    """
```

## Canonical solution

```python3
    return "".join([chr(((ord(ch) - 5 - ord("a")) % 26) + ord("a")) for ch in s])
```

## Tests

```python3


METADATA = {}


def check(candidate):
    from random import randint, choice
    import copy
    import string

    letters = string.ascii_lowercase
    for _ in range(100):
        str = ''.join(choice(letters) for i in range(randint(10, 20)))
        encoded_str = encode_shift(str)
        assert candidate(copy.deepcopy(encoded_str)) == str

```
-/
