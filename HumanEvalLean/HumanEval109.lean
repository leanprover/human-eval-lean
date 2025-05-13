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
          simp
    · intro h
      rcases h with ⟨i, hi, h⟩
      cases i with
      | zero =>
        right
        simp at hi
        simp [hi]
        rw [List.sum_eq_zero]
        intro x hx
        rw [List.mem_iff_getElem] at hx
        rcases hx with ⟨k, hk, tlk⟩
        specialize h (k + 1)
        simp at h
        rw [← tlk]
        apply h hk
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

theorem leftShiftExample1 : leftShift [3,4,5,1,2] 2 = [5,1,2,3,4] := by native_decide

theorem leftShiftExample2 : leftShift [3,4,5,1,2] 3 = [1,2,3,4,5] := by native_decide

-- from mathlib
@[simp] theorem List.take_eq_self_iff (x : List α) {n : Nat} : x.take n = x ↔ x.length ≤ n :=
  ⟨fun h ↦ by rw [← h]; simp; omega, List.take_of_length_le⟩

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


theorem head_lt_getLast_of_sorted_of_ge_2 {l : List Int} (hl : l.length ≥ 2)
    (sorted : ∀ (i : Nat) (hi : i + 1 < l.length), l[i] < l[i+1]) :
    l[0]'(by omega) < l[l.length - 1] := by
  induction l with
  | nil => simp at hl
  | cons hd tl ih =>
    simp
    by_cases h : tl.length ≥ 2
    · specialize ih h
      have htl : tl ≠ [] := ne_nil_of_two_ge h
      have h₁ : hd < tl.head htl := by
        sorry
      have h₂ : tl.head htl < tl.getLast htl := by
        sorry
      have := Nat.lt_trans h₁ h₂



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
          have := head_lt_getLast_of_sorted_of_ge_2 (l := hd :: hd' :: tl')
          simp at this
          apply this trivial
          simp at sorted
          exact sorted
        have h₂ : (hd :: tl')[tl'.length] < hd := by
          simp [countBreakPoints, List.sum_eq_zero, isBreakPoint] at h
          specialize h (tl'.length + 1)
          simp at h





  · omega


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
            have : ¬ i + 1 + j + 1 < l.length := by sorry
            simp [this] at hi2
            have : j + 1 - (l.length - (i + 1)) = 0 := by sorry
            simp [this]
            exact hi2
        · split
          · specialize hi2 0 (by omega)
            have : ¬ i = 0 := by omega
            simp [this] at hi2
            have : 1 < l.length := by omega
            simp [this] at hi2
            omega
          · sorry
    · false_or_by_contra
      rename_i h h'


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
