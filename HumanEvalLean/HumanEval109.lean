variable {α : Type _}

section helper

theorem Nat.lt_two_iff {n : Nat} : n < 2 ↔ n = 0 ∨ n = 1 := by
  cases n with
  | zero => simp
  | succ m =>
    cases m with
    | zero => simp
    | succ o => simp

theorem List.sum_eq_zero {l : List Nat} : l.sum = 0 ↔
  ∀ (i : Nat) (hi : i < l.length), l[i]'hi = 0 := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp [ih]
    constructor
    · intro h i hi
      cases i with
      | zero => simp [h]
      | succ m =>
        simp
        apply And.right h
    · intro h
      constructor
      · apply h 0 (by simp)
      · intro i hi
        apply h (i + 1) (by omega)

theorem List.sum_eq_one_iff {l : List Nat} : l.sum = 1 ↔ ∃ (i : Nat) (hi : i < l.length),
    l[i] = 1 ∧ ∀ (j : Nat) (hj : j < l.length), i ≠ j → l[j] = 0 := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp [Nat.add_eq_one_iff]
    constructor
    · intro h
      cases h with
      | inl h =>
        rcases h with ⟨hl, hr⟩
        rw [ih] at hr
        rcases hr with ⟨i, hi, h⟩
        exists (i + 1)
        simp
        constructor
        · exists hi
          simp [h]
        · intro j hj hij
          cases j with
          | zero => simp[hl]
          | succ k =>
            simp
            apply (And.right h)
            simp at hij
            assumption
      | inr h =>
        exists 0
        simp [h]
        rw [sum_eq_zero] at h
        intro j hj hij
        cases j with
        | zero => simp at hij
        | succ k =>
          simp
          rcases h with ⟨_, h⟩
          apply h
    · intro h
      rcases h with ⟨i, hi, h⟩
      cases i with
      | zero =>
        right
        simp at hi
        simp [hi]
        rw [List.sum_eq_zero]
        intro x hx
        specialize h (x+1)
        simp at h
        apply h
        exact hx
      | succ k =>
        simp at hi
        left
        constructor
        · specialize h 0
          simp at h
          assumption
        · rw [ih]
          exists k
          rcases hi with ⟨hk, tlk⟩
          exists hk
          simp [tlk]
          intro j hj hkj
          specialize h (j + 1)
          simp at h
          apply h hj hkj

theorem List.sum_ge_two_iff {l : List Nat} (h : ∀ (i : Nat) (hi : i < l.length), l[i] ≤ 1) :
    l.sum ≥ 2 ↔ ∃ (i j : Nat) (hij : i ≠ j) (hi : i < l.length) (hj : j < l.length),
      l[i] = 1 ∧ l[j] = 1 := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp
    cases hd with
    | zero =>
      simp
      simp at ih
      rw [ih]
      · constructor
        · intro h
          rcases h with ⟨i, hi, j, hj⟩
          exists (i+1)
          simp [hi]
          exists (j + 1)
          simp [hj]
        · intro h
          rcases h with ⟨i, hi, j, hj⟩
          cases i with
          | zero => simp at hi
          | succ m =>
            exists m
            simp at hi
            simp [hi]
            cases j with
            | zero => simp at hj
            | succ n =>
              exists n
              simp at hj
              simp [hj]
      · intro i hi
        specialize h (i+1)
        simp at h
        exact h hi
    | succ k =>
      cases k with
      | zero =>
        have : 2 ≤ 1 + tl.sum ↔ 1 ≤ tl.sum := by omega
        simp [this, Nat.le_iff_lt_or_eq]
        constructor
        · intro h'
          cases h' with
          | inl h' =>
            simp [Nat.lt_iff_add_one_le] at h'
            simp at ih
            rw [ih] at h'
            · rcases h' with ⟨i, hi, j, hij, hj⟩
              exists (i+1)
              simp
              exists hi
              exists (j+1)
              simp [hij, hj]
            · intro i hi
              simp at h
              specialize h (i+1)
              simp at h
              exact h hi
          | inr h' =>
            exists 0
            simp
            rw [Eq.comm, sum_eq_one_iff] at h'
            rcases h' with ⟨j, hj, htl⟩
            exists (j+1)
            simp
            exists hj
            simp [htl]
        · intro h'
          by_cases hsum: 1 = tl.sum
          · simp [hsum]
          · simp [hsum, Nat.lt_iff_add_one_le]
            simp at ih
            rw [ih]
            · sorry
            · intro i hi
              specialize h (i+1)
              simp at h
              exact h hi
      | succ l =>
        specialize h 0
        simp at h

-- from mathlib
@[simp] theorem List.take_eq_self_iff (x : List α) {n : Nat} : x.take n = x ↔ x.length ≤ n :=
  ⟨fun h ↦ by rw [← h]; simp; omega, List.take_of_length_le⟩

end helper

def rightShift (l : List α) (n : Nat) :=
    l.drop (l.length - n) ++ l.take (l.length - n)

theorem rightShiftExample : rightShift [3,4,5,1,2] 2 = [1,2,3,4,5] := by native_decide

@[simp]
theorem rightShift_zero {l : List α} : rightShift l 0 = l := by
  simp [rightShift]

@[simp]
theorem length_rightShift {l : List α} {n : Nat} :
    (rightShift l n).length = l.length := by
  simp [rightShift]

def leftShift (l : List α) (n : Nat) :=
    l.drop n ++ l.take n

@[simp]
theorem length_leftShift {l : List α} {n : Nat} :
    (leftShift l n).length = l.length := by
  simp [leftShift]
  omega

theorem leftShiftExample1 : leftShift [3,4,5,1,2] 2 = [5,1,2,3,4] := by native_decide

theorem leftShiftExample2 : leftShift [3,4,5,1,2] 3 = [1,2,3,4,5] := by native_decide

theorem exists_rightShift_iff_exists_leftShift {l : List α} (p : List α → Prop) :
    (∃ (n : Nat), p (rightShift l n)) ↔ ∃ (n : Nat), p (leftShift l n) := by
  simp [leftShift, rightShift]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h
    exists (l.length - n)
  · intro h
    obtain ⟨n, hn⟩ := h
    by_cases n < l.length
    · exists (l.length - n)
      have : l.length - (l.length - n) = n := by omega
      simp [this]
      exact hn
    · exists 0
      simp
      rename_i h
      simp at h
      have := List.drop_eq_nil_iff (l := l) (i := n)
      simp [this.mpr h] at hn
      have := List.take_eq_self_iff l (n := n)
      simp [this.mpr h] at hn
      exact hn

def isBreakPoint (l : List Int) (pos : Nat) (h : pos < l.length) :=
  if h:pos + 1 < l.length
  then
    if l[pos] < l[pos + 1]
    then 0
    else 1
  else
    if l[0] > l[pos]
    then 0
    else 1

def countBreakPoints (l : List Int) : Nat :=
  if l.length < 2
  then 0
  else
    ((List.range l.length).attach.map (fun ⟨x,h⟩ =>
      isBreakPoint l x (by simp at h; assumption))).sum

theorem ne_nil_of_two_ge {l : List α} (h : 2 ≤ l.length) : l ≠ [] := by
  cases l with
  | nil => simp at h
  | cons hd tl => simp

theorem sorted_of_countBreakPoints_eq_zero {l : List Int} (h : countBreakPoints l = 0):
    ∀ (i : Nat) (hi : i + 1 < l.length), l[i] < l[i+1] := by
  simp [countBreakPoints] at h
  cases l with
  | nil => simp
  | cons hd tl =>
    cases tl with
    | nil => simp
    | cons hd' tl' =>
      simp[List.sum_eq_zero, isBreakPoint] at h
      simp
      intro i hi
      specialize h i (by omega)
      simp [hi] at h
      exact h

theorem pairwise_sorted_of_sorted {l : List Int} {i j : Nat}
    (hj: j > 0) (hij : i + j < l.length)
    (sorted : ∀ (i : Nat) (hi : i + 1 < l.length), l[i] < l[i+1]) :
    l[i]'(by omega) < l[i + j] := by
  induction l generalizing i j with
  | nil => simp at hij
  | cons hd tl ih =>
    cases i with
    | zero =>
      simp
      simp [Nat.lt_iff_add_one_le] at hj
      cases j with
      | zero => simp at hj
      | succ k =>
        cases k with
        | zero =>
          simp
          specialize sorted 0
          simp at sorted
          apply sorted
          simp at hij
          assumption
        | succ m =>
          simp
          have : m + 1 > 0 := by omega
          have ih' := ih (i:= 0) (j := m+1)
          specialize ih' this
          simp at ih'
          simp at hij
          specialize ih' hij
          apply Int.lt_trans (b := tl[0])
          · specialize sorted 0
            simp at sorted
            apply sorted
            apply Nat.lt_trans (m:= m + 1)
            · simp
            · exact hij
          · apply ih'
            intro i hi
            specialize sorted (i+1)
            simp at sorted
            apply sorted hi
    | succ n =>
      simp
      have : n + 1 + j = (n + j).succ := by omega
      simp [this]
      apply ih
      · exact hj
      · intro i hi
        specialize sorted (i+1)
        simp at sorted
        apply sorted hi

theorem countBreakPoints_eq_zero_iff {l : List Int} : countBreakPoints l = 0 ↔ l.length < 2 := by
  constructor
  · intro h
    have sorted := sorted_of_countBreakPoints_eq_zero h
    false_or_by_contra
    rename_i hl
    simp at hl
    cases l with
    | nil => simp at hl
    | cons hd tl =>
      cases tl with
      | nil => simp at hl
      | cons hd' tl' =>
        have h₁ : hd < (hd' :: tl')[tl'.length] := by
          have head_lt_getLast := pairwise_sorted_of_sorted (l := hd :: hd' :: tl') (i := 0)
              (j := tl'.length + 1) (by simp) (by simp) sorted
          simp at head_lt_getLast
          exact head_lt_getLast
        have h₂ : (hd' :: tl')[tl'.length] < hd := by
          simp [countBreakPoints, List.sum_eq_zero, isBreakPoint] at h
          specialize h (tl'.length + 1)
          simp at h
          apply h
          trivial
        have := Int.lt_trans h₁ h₂
        simp at this
  · intro h
    simp [countBreakPoints, h]


def move_one_ball (l : List Int) : Bool :=
  countBreakPoints l < 2

theorem testCase1 : move_one_ball [3,4,5,1,2] = True := by native_decide
theorem testCase2 : move_one_ball [3,5,10,1,2] = True := by native_decide
theorem testCase3 : move_one_ball [4,3,1,2] = False := by native_decide
theorem testCase4 : move_one_ball [3,5,4,1,2] = False := by native_decide
theorem testCase5 : move_one_ball [] = True := by native_decide

theorem move_one_ball_correct {l : List Int} :
    move_one_ball l = true ↔
    ∃ (n : Nat), ∀ (i : Nat) (hi : i + 1 < l.length),
      (rightShift l n)[i]'(by simp; omega) < (rightShift l n)[i +1]'(by simpa) := by
  by_cases hl : l.length < 2
  · simp [move_one_ball, hl, countBreakPoints]
    exists 0
    cases l with
    | nil => simp
    | cons hd tl =>
      cases tl with
      | nil => simp
      | cons hd' tl' =>
        simp at hl
        omega
  · simp [move_one_ball]
    constructor
    · intro h
      rw [Nat.lt_two_iff] at h
      cases h with
      | inl h =>
        rw [countBreakPoints_eq_zero_iff] at h
        contradiction
      | inr h =>
        simp [countBreakPoints, hl, List.sum_eq_one_iff] at h
        have := exists_rightShift_iff_exists_leftShift (l:= l) (p := fun (l : List Int) =>
          ∀ (i : Nat) (hi : i + 1 < l.length), l[i]'(by omega) < l[i + 1])
        simp at this
        rw [this]
        rcases h with ⟨i, hi1, hi2⟩
        exists (i + 1)
        rcases hi1 with ⟨hi, hi1⟩
        intro j hj
        simp [leftShift]
        simp [List.getElem_append]
        simp [isBreakPoint] at hi2
        split
        · split
          · specialize hi2 (i + 1 + j) (by omega)
            have : ¬ i = i + 1 + j := by omega
            simp [this] at hi2
            have :  i + 1 + j + 1 < l.length := by omega
            simp [this] at hi2
            apply hi2
          · specialize hi2 (i + 1 + j) (by omega)
            have : ¬ i = i + 1 + j := by omega
            simp [this] at hi2
            have : ¬ i + 1 + j + 1 < l.length := by omega
            simp [this] at hi2
            have : j + 1 - (l.length - (i + 1)) = 0 := by omega
            simp [this]
            exact hi2
        · split
          · specialize hi2 0 (by omega)
            have : ¬ i = 0 := by omega
            simp [this] at hi2
            have : 1 < l.length := by omega
            simp [this] at hi2
            omega
          · rename_i h₁ h₂
            specialize hi2 (j - (l.length - (i + 1))) (by omega) (by omega)
            have : j - (l.length - (i + 1)) + 1 < l.length := by omega
            simp [this] at hi2
            have : j - (l.length - (i + 1)) + 1 = j + 1 - (l.length - (i + 1)) := by omega
            simp [this] at hi2
            exact hi2
    · false_or_by_contra
      rename_i h h'
      sorry



/-!
## Prompt

```python3

def move_one_ball(arr):
    """We have an array 'arr' of N integers arr[1], arr[2], ..., arr[N].The
    numbers in the array will be randomly ordered. Your task is to determine if
    it is possible to get an array sorted in non-decreasing order by performing
    the following operation on the given array:
        You are allowed to perform right shift operation any number of times.

    One right shift operation means shifting all elements of the array by one
    position in the right direction. The last element of the array will be moved to
    the starting position in the array i.e. 0th index.

    If it is possible to obtain the sorted array by performing the above operation
    then return True else return False.
    If the given array is empty then return True.

    Note: The given list is guaranteed to have unique elements.

    For Example:

    move_one_ball([3, 4, 5, 1, 2])==>True
    Explanation: By performin 2 right shift operations, non-decreasing order can
                 be achieved for the given array.
    move_one_ball([3, 5, 4, 1, 2])==>False
    Explanation:It is not possible to get non-decreasing order for the given
                array by performing any number of right shift operations.

    """
```

## Canonical solution

```python3
    if len(arr)==0:
      return True
    sorted_array=sorted(arr)
    my_arr=[]

    min_value=min(arr)
    min_index=arr.index(min_value)
    my_arr=arr[min_index:]+arr[0:min_index]
    for i in range(len(arr)):
      if my_arr[i]!=sorted_array[i]:
        return False
    return True
```

## Tests

```python3
def check(candidate):

    # Check some simple cases
    assert candidate([3, 4, 5, 1, 2])==True, "This prints if this assert fails 1 (good for debugging!)"
    assert candidate([3, 5, 10, 1, 2])==True
    assert candidate([4, 3, 1, 2])==False
    # Check some edge cases that are easy to work out by hand.
    assert candidate([3, 5, 4, 1, 2])==False, "This prints if this assert fails 2 (also good for debugging!)"
    assert candidate([])==True
```
-/
