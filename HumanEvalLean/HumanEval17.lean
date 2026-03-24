module

import Std.Data.HashMap.Lemmas

open Std

def parseMusic (musicString : String) : List Nat :=
  let noteMap : HashMap String.Slice Nat := .ofList [("o", 4), ("o|", 2), (".|", 1)]
  (musicString.split ' ').filterMap (noteMap[·]?) |>.toList

example : parseMusic "" = [] := by native_decide
example : parseMusic "o o o o" = [4, 4, 4, 4] := by native_decide
example : parseMusic ".| .| .| .|" = [1, 1, 1, 1] := by native_decide
example : parseMusic "o| o| .| .| o o o o" = [2, 2, 1, 1, 4, 4, 4, 4] := by native_decide
example : parseMusic "o| .| o| .| o o| o o|" = [2, 1, 2, 1, 4, 2, 4, 2] := by native_decide

def noteForValue (value : Nat) (h : value = 1 ∨ value = 2 ∨ value = 4) : String :=
  match value with
  | 0 => False.elim (by simp at h)
  | 1 => ".|"
  | 2 => "o|"
  | 3 => False.elim (by simp at h)
  | 4 => "o"
  | _ + 5 => False.elim (by simp at h)

def formatMusic (l : List Nat) (hl : ∀ value ∈ l, value = 1 ∨ value = 2 ∨ value = 4) : String :=
  " ".intercalate ((l.attachWith _ hl).map (fun p => noteForValue p.1 p.2))

theorem List.filterMap_beq_congr [BEq α] {l l' : List α} {f : α → Option β}
    (hf : ∀ a a', a == a' → f a = f a') (hl : l == l') : l.filterMap f = l'.filterMap f := by
  induction l generalizing l' with
  | nil => simp_all
  | cons h₁ t₁ ih =>
    match l' with
    | [] => simp_all
    | h₂ :: t₂ =>
      simp at hl
      simp [List.filterMap_cons, ih hl.2, hf _ _ hl.1]

theorem parseMusic_formatMusic {l : List Nat} {hl} : parseMusic (formatMusic l hl) = l := by
  rw [parseMusic, formatMusic, Iter.toList_filterMap]
  simp +instances only [String.reduceToSingleton]
  rw [List.filterMap_beq_congr (fun _ _ => HashMap.getElem?_congr) (String.toList_split_intercalate_beq _)]
  · simp only [↓Char.isValue, String.reduceSingleton, List.map_attachWith, List.map_eq_nil_iff,
      List.attach_eq_nil_iff, List.map_map]
    by_cases hl : l = []
    · simp [hl]
    · simp [hl]
      clear hl
      induction l with
      | nil => simp
      | cons ht tl ih =>
        simp only [List.attach_cons]
        rw [List.filterMap_cons_some (b := ht)]
        · simp only [List.filterMap_map, List.cons.injEq, true_and]
          apply ih
          refine fun v hv => hl _ (by simp [hv])
        · simp
          obtain (rfl|rfl|rfl) := hl ht (by simp) <;>
            simp [noteForValue, HashMap.ofList_equiv_foldl.getElem_eq, HashMap.getElem_insert]
  · simp only [List.map_attachWith, List.mem_map, List.mem_attach, true_and, Subtype.exists,
      ↓Char.isValue, forall_exists_index]
    rintro _ val hval rfl
    obtain (rfl|rfl|rfl) := hl _ hval <;> simp [noteForValue]

/-!
## Prompt

```python3
from typing import List


def parse_music(music_string: str) -> List[int]:
    """ Input to this function is a string representing musical notes in a special ASCII format.
    Your task is to parse this string and return list of integers corresponding to how many beats does each
    not last.

    Here is a legend:
    'o' - whole note, lasts four beats
    'o|' - half note, lasts two beats
    '.|' - quater note, lasts one beat

    >>> parse_music('o o| .| o| o| .| .| .| .| o o')
    [4, 2, 1, 2, 2, 1, 1, 1, 1, 4, 4]
    """
```

## Canonical soluton

```python3
    note_map = {'o': 4, 'o|': 2, '.|': 1}
    return [note_map[x] for x in music_string.split(' ') if x]
```

## Tests

```python3


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    assert candidate('') == []
    assert candidate('o o o o') == [4, 4, 4, 4]
    assert candidate('.| .| .| .|') == [1, 1, 1, 1]
    assert candidate('o| o| .| .| o o o o') == [2, 2, 1, 1, 4, 4, 4, 4]
    assert candidate('o| .| o| .| o o| o o|') == [2, 1, 2, 1, 4, 2, 4, 2]
```
-/
