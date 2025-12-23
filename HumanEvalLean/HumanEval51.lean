def IsSubseq (s₁ : String) (s₂ : String) : Prop :=
  List.Sublist s₁.toList s₂.toList

def vowels : List Char := ['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U']

def NoVowels (s : String) : Prop :=
  List.all s.toList (· ∉ vowels)

def MaximalFor [LE α] (P : ι → Prop) (f : ι → α) (x : ι) : Prop :=
  -- Same as MaximalFor in Mathlib
  P x ∧ ∀ y : ι, P y → f x ≤ f y → f y ≤ f x

def RemoveVowelsIff (solution : String → String) : Prop :=
    (s x : String) → (solution s = x) → MaximalFor (fun i => NoVowels i ∧ IsSubseq i s) (String.length) x

def removeVowels (s : String) : String :=
    String.ofList (s.toList.filter (· ∉ vowels))

example : removeVowels "abcdef" = "bcdf" := by native_decide
example : removeVowels "abcdef\nghijklm" = "bcdf\nghjklm" := by native_decide
example : removeVowels "aaaaa" = "" := by native_decide
example : removeVowels "aaBAA" = "B" := by native_decide
example : removeVowels "zbcd" = "zbcd" := by native_decide

theorem IsSubseq.length_le {s t : String} (hst : IsSubseq s t) :
    s.length ≤ t.length :=
  List.Sublist.length_le hst

theorem IsSubseq.removeVowels {s t : String} (hst : IsSubseq s t) :
    IsSubseq (removeVowels s) (removeVowels t) := by
  simpa [IsSubseq, _root_.removeVowels] using hst.filter _

theorem removeVowels_eq_self {s : String} :
    removeVowels s = s ↔ NoVowels s := by
  simp [String.ext_iff, NoVowels, removeVowels]

theorem removeVowels_correct : RemoveVowelsIff removeVowels := by
  simp [RemoveVowelsIff]
  intro s
  constructor
  · simp [NoVowels, removeVowels, IsSubseq]
  · simp only [and_imp]
    intro y hnv hss hle
    rw [← removeVowels_eq_self.2 hnv]
    exact IsSubseq.length_le (IsSubseq.removeVowels hss)

/-!
## Prompt

```python3


def remove_vowels(text):
    """
    remove_vowels is a function that takes string and returns string without vowels.
    >>> remove_vowels('')
    ''
    >>> remove_vowels("abcdef\nghijklm")
    'bcdf\nghjklm'
    >>> remove_vowels('abcdef')
    'bcdf'
    >>> remove_vowels('aaaaa')
    ''
    >>> remove_vowels('aaBAA')
    'B'
    >>> remove_vowels('zbcd')
    'zbcd'
    """
```

## Canonical solution

```python3
    return "".join([s for s in text if s.lower() not in ["a", "e", "i", "o", "u"]])
```

## Tests

```python3


METADATA = {}


def check(candidate):
    assert candidate('') == ''
    assert candidate("abcdef\nghijklm") == 'bcdf\nghjklm'
    assert candidate('fedcba') == 'fdcb'
    assert candidate('eeeee') == ''
    assert candidate('acBAA') == 'cB'
    assert candidate('EcBOO') == 'cB'
    assert candidate('ybcd') == 'ybcd'

```
-/
