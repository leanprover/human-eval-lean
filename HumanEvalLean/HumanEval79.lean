module

def decimalToBinary (n : Nat) : String :=
  "db" ++ String.ofList (Nat.toDigits 2 n) ++ "db"

example : decimalToBinary 0 = "db0db" := by native_decide
example : decimalToBinary 15 = "db1111db" := by native_decide
example : decimalToBinary 32 = "db100000db" := by native_decide
example : decimalToBinary 103 = "db1100111db" := by native_decide

section

open String.Slice.Pattern

@[simp]
theorem String.dropPrefix?_eq_none_iff {ρ : Type} {pat : ρ} [ForwardPattern pat] [LawfulForwardPattern pat]
    {s : String} : s.dropPrefix? pat = none ↔ s.startsWith pat = false := by
  simp [dropPrefix?_eq_dropPrefix?_toSlice, startsWith_eq_startsWith_toSlice]

public instance {pat : String.Slice} : LawfulForwardPattern pat := sorry
public instance {pat : String} : LawfulForwardPattern pat := sorry


end

theorem toNat?_decimalToBinary {n : Nat} :
    ((decimalToBinary n).dropPrefix? "db").any
      (fun withoutPrefix => (withoutPrefix.dropSuffix? "db").any
          (fun withoutSuffix => Nat.ofDigitChars b withoutSuffix.copy.toList 0 == n)) := by
  simp [decimalToBinary, Option.any_eq_true]
  match h : ("db" ++ String.ofList (Nat.toDigits 2 n) ++ "db").dropPrefix? "db" with
  | none => simp at h
  | some y =>
    simp
    have := String.eq_append_of_dropPrefix?_string_eq_some h
    match h' : y.dropSuffix? "db" with
    | none => simp at h'
    | some y' => sorry




/-!
## Prompt

```python3

def decimal_to_binary(decimal):
    """You will be given a number in decimal form and your task is to convert it to
    binary format. The function should return a string, with each character representing a binary
    number. Each character in the string will be '0' or '1'.

    There will be an extra couple of characters 'db' at the beginning and at the end of the string.
    The extra characters are there to help with the format.

    Examples:
    decimal_to_binary(15)   # returns "db1111db"
    decimal_to_binary(32)   # returns "db100000db"
    """
```

## Canonical solution

```python3
    return "db" + bin(decimal)[2:] + "db"
```

## Tests

```python3
def check(candidate):

    # Check some simple cases
    assert candidate(0) == "db0db"
    assert candidate(32) == "db100000db"
    assert candidate(103) == "db1100111db"
    assert candidate(15) == "db1111db", "This prints if this assert fails 1 (good for debugging!)"

    # Check some edge cases that are easy to work out by hand.
    assert True, "This prints if this assert fails 2 (also good for debugging!)"

```
-/
