module
import Std.Tactic.Do
import Std
import all Init.Data.Range.Polymorphic.UpwardEnumerable -- UpwardEnumerable.least not exposed

open Std Std.Do

def encodeVector {n : Nat} (arr : Vector α n) : Vector α n := Id.run do
  let mut vec : Vector α n := arr

  for h : i in (*...n / 3) do
    let tmp := vec[3 * i]
    vec := vec.set (3 * i) vec[3 * i + 1]
    vec := vec.set (3 * i + 1) vec[3 * i + 2]
    vec := vec.set (3 * i + 2) tmp

  return vec

def encodeArray (arr : Array α) : Array α :=
  (encodeVector arr.toVector).toArray

def encodeCyclic (s : String) : String :=
  String.ofList (encodeArray s.toList.toArray).toList

def decodeCyclic (s : String) : String :=
  String.ofList (encodeArray (encodeArray s.toList.toArray)).toList

theorem List.Cursor.length_prefix_le {l : List α} (c : l.Cursor) : c.prefix.length ≤ l.length := by
  have := congrArg List.length c.property
  simp at this
  omega

theorem Nat.eq_add_of_toList_rio_eq_append_cons {a : Nat} {pref cur suff}
    (h : (*...a).toList = pref ++ cur :: suff) :
    cur = pref.length := by
  have := Rio.eq_succMany?_of_toList_eq_append_cons h
  simpa [PRange.UpwardEnumerable.least, PRange.least?] using this

set_option mvcgen.warning false in
theorem getElem_encodeVector {arr : Vector α n} {i : Nat} {hi} :
    (encodeVector arr)[i]'hi =
      if h : i < 3 * (arr.size / 3) then
        if hmod : i % 3 = 2 then
          arr[i - 2]
        else
          arr[i + 1]
      else
        arr[i]'(by simp_all) := by
  generalize hwp : encodeVector arr = wp
  apply Id.of_wp_run_eq hwp
  mvcgen invariants
  · ⇓⟨xs, vec⟩ =>
    ⌜∀ (i : Nat) (hi : i < n), vec[i] =
      have : xs.prefix.length ≤ n / 3 := by simpa using xs.length_prefix_le
      if h : i < 3 * xs.prefix.length then
        if hmod : i % 3 = 2 then
          arr[i - 2]
        else
          arr[i + 1]
      else
        arr[i]'(by simp_all)⌝
  with
    grind [Nat.eq_add_of_toList_rio_eq_append_cons, Rio.length_toList, Nat.size_rio]

@[simp]
theorem encodeVector_encodeVector_encodeVector {arr : Vector α n} :
    encodeVector (encodeVector (encodeVector arr)) = arr := by
  grind [getElem_encodeVector]

@[simp]
theorem encodeArray_encodeArray_encodeArray {arr : Array α} :
    encodeArray (encodeArray (encodeArray arr)) = arr := by
  ext
  · simp [encodeArray]
  · simp only [encodeArray, Vector.getElem_toArray, getElem_encodeVector, Vector.size_toArray,
      Vector.getElem_mk, Nat.reduceSubDiff]
    grind

theorem decodeCyclic_encodeCyclic {s : String} : decodeCyclic (encodeCyclic s) = s := by
  simp [decodeCyclic, encodeCyclic]

/-!
## Prompt

```python3


def encode_cyclic(s: str):
    """
    returns encoded string by cycling groups of three characters.
    """
    # split string to groups. Each of length 3.
    groups = [s[(3 * i):min((3 * i + 3), len(s))] for i in range((len(s) + 2) // 3)]
    # cycle elements in each group. Unless group has fewer elements than 3.
    groups = [(group[1:] + group[0]) if len(group) == 3 else group for group in groups]
    return "".join(groups)


def decode_cyclic(s: str):
    """
    takes as input string encoded with encode_cyclic function. Returns decoded string.
    """
```

## Canonical solution

```python3
    return encode_cyclic(encode_cyclic(s))
```

## Tests

```python3


METADATA = {}


def check(candidate):
    from random import randint, choice
    import string

    letters = string.ascii_lowercase
    for _ in range(100):
        str = ''.join(choice(letters) for i in range(randint(10, 20)))
        encoded_str = encode_cyclic(str)
        assert candidate(encoded_str) == str

```
-/
