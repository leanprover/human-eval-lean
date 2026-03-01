module

public import Std
import all Init.Data.Range.Polymorphic.UpwardEnumerable -- UpwardEnumerable.least not exposed
open Std Std.Iterators Std.Iterators.Types Std.Do

set_option mvcgen.warning false

/-! ## Implementation -/

public section

-- TODO: use `Array.mergeSort` when available

def sortThird (xs : Array Int) : Array Int := Id.run do
  let sorted := xs.iter.stepSize 3 |>.toList.mergeSort.toArray
  -- Prove the size of `sorted` so that we can access `sorted[i]` without a runtime bounds check
  have : sorted.size = (xs.size + 2) / 3 := by simp [sorted, Iter.length_stepSize]
  let mut vec := xs.toVector
  for h : i in *...((xs.size + 2) / 3) do
    vec := vec.set (i * 3) sorted[i]
  return vec.toArray

/-! ## Tests -/

example : sortThird #[1, 2, 3] = #[1, 2, 3] := by native_decide
example : sortThird #[5, 3, -5, 2, -3, 3, 9, 0, 123, 1, -10] =
    #[1, 3, -5, 2, -3, 3, 5, 0, 123, 9, -10] := by native_decide
example : sortThird #[5, 8, -12, 4, 23, 2, 3, 11, 12, -10] =
    #[-10, 8, -12, 3, 23, 2, 4, 11, 12, 5] := by native_decide
example : sortThird #[5, 6, 3, 4, 8, 9, 2] = #[2, 6, 3, 4, 8, 9, 5] := by native_decide
example : sortThird #[5, 8, 3, 4, 6, 9, 2] = #[2, 8, 3, 4, 6, 9, 5] := by native_decide
example : sortThird #[5, 6, 9, 4, 8, 3, 2] = #[2, 6, 9, 4, 8, 3, 5] := by native_decide
example : sortThird #[5, 6, 3, 4, 8, 9, 2, 1] = #[2, 6, 3, 4, 8, 9, 5, 1] := by native_decide

/-! ## Missing API -/

theorem Nat.eq_add_of_toList_rco_eq_append_cons {a b : Nat} {pref cur suff}
    (h : (a...b).toList = pref ++ cur :: suff) :
    cur = a + pref.length := by
  have := Rco.eq_succMany?_of_toList_eq_append_cons h
  simpa [PRange.UpwardEnumerable.least, PRange.least?] using this

/-! ## Verification -/

theorem getElem?_sortThird_of_mod_ne_zero {xs : Array Int} {i : Nat} (h : i % 3 ≠ 0) :
    (sortThird xs)[i]? = xs[i]? := by
  generalize hwp : sortThird xs = wp
  apply Id.of_wp_run_eq hwp
  mvcgen
  invariants
  · ⇓⟨cur, vec⟩ => ⌜∀ i : Nat, i % 3 ≠ 0 → vec[i]? = xs[i]?⌝
  with grind [Vector.getElem?_mk]

theorem getElem?_sortThird_mul_three {xs : Array Int} {i : Nat} :
    (sortThird xs)[i * 3]? = (xs.iter.stepSize 3).toList.mergeSort[i]? := by
  generalize hwp : sortThird xs = wp
  apply Id.of_wp_run_eq hwp
  mvcgen
  invariants
  · ⇓⟨cur, vec⟩ => ⌜∀ i < cur.pos, vec[i * 3]? = (xs.iter.stepSize 3).toList.mergeSort[i]?⌝
  case vc1 =>
    have := Nat.eq_add_of_toList_rco_eq_append_cons ‹_›
    grind
  case vc2 => grind
  case vc3 => grind [Nat.length_toList_rio]

/-!
### Size properties

The following two properties also follow from the two theorems above, but we provide them for
good measure.
-/

theorem size_sortThird {xs : Array Int} :
    (sortThird xs).size = xs.size := by
  grind [sortThird]

theorem length_stepSize {xs : Array Int} :
    (xs.iter.stepSize 3).length = (xs.size + 2) / 3 := by
  grind [Iter.length_stepSize]

/-!
### Correctness of used library functions

For completeness, we point to library lemmas that prove the correctness of the `stepSize` and
`List.mergeSort`, the library functions on which relied to state our formal lemmas.
-/

/--
`(xs.iter.stepSize 3).toList` contains every element of `xs` at indices divisible by three,
and no more elements than these.
-/
theorem getElem?_toList_stepSize {xs : Array Int} :
    (xs.iter.stepSize 3).toList[i]? = xs[i * 3]? := by
  grind [Iter.getElem?_toList_stepSize]

/--
info: List.mergeSort_perm.{u_1} {α : Type u_1} (l : List α) (le : α → α → Bool) : (l.mergeSort le).Perm l
-/
#guard_msgs in
#check List.mergeSort_perm

/--
info: List.pairwise_mergeSort.{u_1} {α : Type u_1} {le : α → α → Bool}
  (trans : ∀ (a b c : α), le a b = true → le b c = true → le a c = true)
  (total : ∀ (a b : α), (le a b || le b a) = true) (l : List α) :
  List.Pairwise (fun a b => le a b = true) (l.mergeSort le)
-/
#guard_msgs in
#check List.pairwise_mergeSort

/-!
## Prompt

```python3


def sort_third(l: list):
    """This function takes a list l and returns a list l' such that
    l' is identical to l in the indicies that are not divisible by three, while its values at the indicies that are divisible by three are equal
    to the values of the corresponding indicies of l, but sorted.
    >>> sort_third([1, 2, 3])
    [1, 2, 3]
    >>> sort_third([5, 6, 3, 4, 8, 9, 2])
    [2, 6, 3, 4, 8, 9, 5]
    """
```

## Canonical solution

```python3
    l = list(l)
    l[::3] = sorted(l[::3])
    return l
```

## Tests

```python3


METADATA = {}


def check(candidate):
    assert tuple(candidate([1, 2, 3])) == tuple(sort_third([1, 2, 3]))
    assert tuple(candidate([5, 3, -5, 2, -3, 3, 9, 0, 123, 1, -10])) == tuple(sort_third([5, 3, -5, 2, -3, 3, 9, 0, 123, 1, -10]))
    assert tuple(candidate([5, 8, -12, 4, 23, 2, 3, 11, 12, -10])) == tuple(sort_third([5, 8, -12, 4, 23, 2, 3, 11, 12, -10]))
    assert tuple(candidate([5, 6, 3, 4, 8, 9, 2])) == tuple([2, 6, 3, 4, 8, 9, 5])
    assert tuple(candidate([5, 8, 3, 4, 6, 9, 2])) == tuple([2, 8, 3, 4, 6, 9, 5])
    assert tuple(candidate([5, 6, 9, 4, 8, 3, 2])) == tuple([2, 6, 9, 4, 8, 3, 5])
    assert tuple(candidate([5, 6, 3, 4, 8, 9, 2, 1])) == tuple([2, 6, 3, 4, 8, 9, 5, 1])

```
-/
