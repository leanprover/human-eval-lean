module

def digitSum (s : String) : Nat :=
  s.chars.filter Char.isUpper
    |>.map Char.toNat
    |>.fold (init := 0) (· + ·)

example : digitSum "" = 0 := by cbv
example : digitSum "abAB" = 131 := by cbv
example : digitSum "abcCd" = 67 := by cbv
example : digitSum "helloE" = 69 := by cbv
example : digitSum "woArBld" = 131 := by cbv
example : digitSum "aAaaaXa" = 153 := by cbv

theorem digitSum_eq {s : String} :
    digitSum s = ((s.toList.filter Char.isUpper).map Char.toNat).sum := by
  simp [digitSum, ← Std.Iter.foldl_toList, List.sum_eq_foldl]

theorem digitSum_empty : digitSum "" = 0 := by simp [digitSum_eq]

theorem digitSum_push_of_isUpper {s : String} {c : Char} (h : c.isUpper = true) :
    digitSum (s.push c) = digitSum s + c.toNat := by
  simp [digitSum_eq, List.filter_cons_of_pos h]

theorem digitSum_push_of_isUpper_eq_false {s : String} {c : Char} (h : c.isUpper = false) :
    digitSum (s.push c) = digitSum s := by
  simp [digitSum_eq, List.filter_cons_of_neg (Bool.not_eq_true _ ▸ h)]

/-!
## Prompt

```python3

def digitSum(s):
    """Task
    Write a function that takes a string as input and returns the sum of the upper characters only'
    ASCII codes.

    Examples:
        digitSum("") => 0
        digitSum("abAB") => 131
        digitSum("abcCd") => 67
        digitSum("helloE") => 69
        digitSum("woArBld") => 131
        digitSum("aAaaaXa") => 153
    """
```

## Canonical solution

```python3
    if s == "": return 0
    return sum(ord(char) if char.isupper() else 0 for char in s)
```

## Tests

```python3
def check(candidate):

    # Check some simple cases
    assert True, "This prints if this assert fails 1 (good for debugging!)"
    assert candidate("") == 0, "Error"
    assert candidate("abAB") == 131, "Error"
    assert candidate("abcCd") == 67, "Error"
    assert candidate("helloE") == 69, "Error"
    assert candidate("woArBld") == 131, "Error"
    assert candidate("aAaaaXa") == 153, "Error"

    # Check some edge cases that are easy to work out by hand.
    assert True, "This prints if this assert fails 2 (also good for debugging!)"
    assert candidate(" How are yOu?") == 151, "Error"
    assert candidate("You arE Very Smart") == 327, "Error"

```
-/
