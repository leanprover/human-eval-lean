module

def reverseString (s : String) : String :=
  s.revChars.fold (init := "") fun sofar c => sofar.push c

def swapCase (c : Char) : Char :=
  if c.isUpper then
    c.toLower
  else if c.isLower then
    c.toUpper
  else
    c

def solve (s : String) : String :=
  if s.contains Char.isAlpha then
    s.map swapCase
  else
    reverseString s

example : solve "AsDf" = "aSdF" := by native_decide
example : solve "1234" = "4321" := by native_decide
example : solve "ab" = "AB" := by native_decide
example : solve "#a@C" = "#A@c" := by native_decide
example : solve "#AsdfW^45" = "#aSDFw^45" := by native_decide
example : solve "#6@2" = "2@6#" := by native_decide
example : solve "#$a^D" = "#$A^d" := by native_decide
example : solve "#ccc" = "#CCC" := by native_decide

@[simp]
theorem toList_reverseString {s : String} : (reverseString s).toList = s.toList.reverse := by
  simp only [reverseString, ne_eq, ← Std.Iter.foldl_toList, String.toList_revChars,
    List.foldl_reverse]
  induction s.toList <;> simp_all

@[simp]
theorem String.contains_bool {s : String} {p : Char → Bool} :
    s.contains p = s.toList.any p := sorry

theorem toList_solve {s : String} : (solve s).toList =
    if s.toList.any Char.isAlpha then
      s.toList.map swapCase
    else
      s.toList.reverse := by
  simp only [solve, String.contains_bool, List.any_eq_true]
  rw [apply_ite String.toList, toList_reverseString, String.toList_map]

/-!
## Prompt

```python3

def solve(s):
    """You are given a string s.
    if s[i] is a letter, reverse its case from lower to upper or vise versa,
    otherwise keep it as it is.
    If the string contains no letters, reverse the string.
    The function should return the resulted string.
    Examples
    solve("1234") = "4321"
    solve("ab") = "AB"
    solve("#a@C") = "#A@c"
    """
```

## Canonical solution

```python3
    flg = 0
    idx = 0
    new_str = list(s)
    for i in s:
        if i.isalpha():
            new_str[idx] = i.swapcase()
            flg = 1
        idx += 1
    s = ""
    for i in new_str:
        s += i
    if flg == 0:
        return s[len(s)::-1]
    return s
```

## Tests

```python3
def check(candidate):

    # Check some simple cases
    assert candidate("AsDf") == "aSdF"
    assert candidate("1234") == "4321"
    assert candidate("ab") == "AB"
    assert candidate("#a@C") == "#A@c"
    assert candidate("#AsdfW^45") == "#aSDFw^45"
    assert candidate("#6@2") == "2@6#"

    # Check some edge cases that are easy to work out by hand.
    assert candidate("#$a^D") == "#$A^d"
    assert candidate("#ccc") == "#CCC"

    # Don't remove this line:
```
-/
