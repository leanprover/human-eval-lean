module
import Std.Data.String.ToNat

def fruitDistribution (s : String) (n : Nat) : Nat :=
  n - ((s.split ' ').filterMap String.Slice.toNat?).fold (init := 0) (· + ·)

example : fruitDistribution "5 apples and 6 oranges" 19 = 8 := by native_decide
example : fruitDistribution "5 apples and 6 oranges" 21= 10 := by native_decide
example : fruitDistribution "0 apples and 1 oranges" 3 = 2 := by native_decide
example : fruitDistribution "1 apples and 0 oranges" 3 = 2 := by native_decide
example : fruitDistribution "2 apples and 3 oranges" 100 = 95 := by native_decide
example : fruitDistribution "2 apples and 3 oranges" 5 = 0 := by native_decide
example : fruitDistribution "1 apples and 100 oranges" 120 = 19 := by native_decide

inductive Word
  | number : Nat → Word
  | nonNumber : (s : String) →
      (hs : s.isNat = false := by simp [← Bool.not_eq_true, String.isNat_iff]) →
      (hs' : ' ' ∉ s.toList := by simp) → Word

def Word.toNat? : Word → Option Nat
  | .number n => some n
  | .nonNumber .. => none

def Word.toString : Word → String
  | .number n => ToString.toString n
  | .nonNumber s _ _ => s

@[simp]
theorem Word.toNat?_comp_toString : String.toNat? ∘ Word.toString = Word.toNat? := by
  ext1 w
  match w with
  | .number n => simp [Word.toNat?, Word.toString]
  | .nonNumber s hs hs' => simp [Word.toNat?, Word.toString, hs]

@[simp]
theorem Word.space_notin_toList_toString {w : Word} : ' ' ∉ w.toString.toList := by
  match w with
  | .number n =>
    simp only [toString, Nat.toString_eq_repr, Nat.toList_repr, ↓Char.isValue]
    intro h
    simpa using Nat.isDigit_of_mem_toDigits (by decide) (by decide) h
  | .nonNumber _ _ hs' => exact hs'

@[simp]
theorem String.isNat_empty : "".isNat = false := by
  simp [← Bool.not_eq_true, isNat_iff]

@[simp]
theorem String.toNat?_empty : "".toNat? = none := by
  simp

theorem fruitDistribution_intercalate_toString (l : List Word) (n : Nat) :
    fruitDistribution (" ".intercalate (l.map Word.toString)) n = n - (l.filterMap Word.toNat?).sum := by
  rw [fruitDistribution]
  simp +instances only [String.reduceToSingleton]
  rw [← Std.Iter.foldl_toList, Std.Iter.toList_filterMap, ← String.Slice.toNat?_comp_copy,
    ← List.filterMap_map, String.toList_split_intercalate (by simp), ← List.sum_eq_foldl]
  simp only [List.map_eq_nil_iff]
  split <;> simp_all

theorem fruitDistribution_sentence {n₁ n₂ n : Nat} :
    fruitDistribution (toString n₁ ++ " apples and " ++ toString n₂ ++ " oranges") n = n - n₁ - n₂ := by
  have := fruitDistribution_intercalate_toString [.number n₁, .nonNumber "apples", .nonNumber "and", .number n₂, .nonNumber "oranges"] n
  simp only [List.map_cons, Word.toString, Nat.toString_eq_repr, List.map_nil,
    String.intercalate_cons_cons, String.reduceAppend, String.intercalate_singleton, Word.toNat?,
    Option.some.injEq, List.filterMap_cons_some, List.filterMap_cons_none, List.filterMap_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero, ← Nat.sub_sub] at this
  rw [← this]
  congr 1
  simp [← String.toList_inj]

/-!
## Prompt

```python3

def fruit_distribution(s,n):
    """
    In this task, you will be given a string that represents a number of apples and oranges
    that are distributed in a basket of fruit this basket contains
    apples, oranges, and mango fruits. Given the string that represents the total number of
    the oranges and apples and an integer that represent the total number of the fruits
    in the basket return the number of the mango fruits in the basket.
    for examble:
    fruit_distribution("5 apples and 6 oranges", 19) ->19 - 5 - 6 = 8
    fruit_distribution("0 apples and 1 oranges",3) -> 3 - 0 - 1 = 2
    fruit_distribution("2 apples and 3 oranges", 100) -> 100 - 2 - 3 = 95
    fruit_distribution("100 apples and 1 oranges",120) -> 120 - 100 - 1 = 19
    """
```

## Canonical solution

```python3
    lis = list()
    for i in s.split(' '):
        if i.isdigit():
            lis.append(int(i))
    return n - sum(lis)
```

## Tests

```python3
def check(candidate):

    # Check some simple cases
    assert candidate("5 apples and 6 oranges",19) == 8
    assert candidate("5 apples and 6 oranges",21) == 10
    assert candidate("0 apples and 1 oranges",3) == 2
    assert candidate("1 apples and 0 oranges",3) == 2
    assert candidate("2 apples and 3 oranges",100) == 95
    assert candidate("2 apples and 3 oranges",5) == 0
    assert candidate("1 apples and 100 oranges",120) == 19
```
-/
