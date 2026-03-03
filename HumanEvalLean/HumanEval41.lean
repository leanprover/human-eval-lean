module

public import Std
open Std Std.Do

set_option mvcgen.warning false

/-! ## Implementation -/

def carRaceCollision (n : Nat) : Nat :=
  n ^ 2

/-! ## Tests -/

example : carRaceCollision 2 = 4 := by decide
example : carRaceCollision 3 = 9 := by decide
example : carRaceCollision 4 = 16 := by decide
example : carRaceCollision 8 = 64 := by decide
example : carRaceCollision 10 = 100 := by decide

/-! ## Missing API -/

theorem eq_getElem_append_cons {pref suff : List α} {cur : α} :
    (pref ++ cur :: suff)[pref.length]? = cur := by
  simp

grind_pattern eq_getElem_append_cons => pref ++ cur :: suff
attribute [grind =] Nat.getElem_toList_rco Nat.getElem_toList_roo Nat.getElem?_toList_rio
attribute [grind =] Nat.length_toList_rco Nat.length_toList_roo Nat.length_toList_rio

/-!
## Verification

We verify the solution by proving that it equals a slower reference implementation that is closer to
the problem description, even though there still remains a gap between the informal problem
statement and the formal reference implementation.

The verification merely ensures that the optimization, just squaring instead of actually counting,
is valid.
-/

/-- Reference implementation: count collisions by iterating over all pairs. -/
def carRaceCollisionSlow (n : Nat) : Nat := Id.run do
  let mut collisionCounter := 0
  for _leftCarIdx in *...n do
    for _rightCarIdx in *...n do
      -- every left car collides with every right car
      collisionCounter := collisionCounter + 1
  return collisionCounter

theorem carRaceCollisionSlow_eq_carRaceCollision {n : Nat} :
    carRaceCollisionSlow n = carRaceCollision n := by
  rw [carRaceCollision]
  generalize hwp : carRaceCollisionSlow n = wp
  apply Id.of_wp_run_eq hwp
  mvcgen
  invariants
  · ⇓⟨cur, counter⟩ => ⌜counter = cur.pos * n⌝
  · by
      rename_i pref curr suff _ _ _
      exact ⇓⟨cur, counter⟩ => ⌜counter = curr * n + cur.pos⌝
  with grind

/-!
## Prompt

```python3


def car_race_collision(n: int):
    """
    Imagine a road that's a perfectly straight infinitely long line.
    n cars are driving left to right;  simultaneously, a different set of n cars
    are driving right to left.   The two sets of cars start out being very far from
    each other.  All cars move in the same speed.  Two cars are said to collide
    when a car that's moving left to right hits a car that's moving right to left.
    However, the cars are infinitely sturdy and strong; as a result, they continue moving
    in their trajectory as if they did not collide.

    This function outputs the number of such collisions.
    """
```

## Canonical solution

```python3
    return n**2
```

## Tests

```python3


METADATA = {}


def check(candidate):
    assert candidate(2) == 4
    assert candidate(3) == 9
    assert candidate(4) == 16
    assert candidate(8) == 64
    assert candidate(10) == 100

```
-/
