variable {α : Type _}

def leftShift (l : List α) (n : Nat) : List α :=
  match n with
  | .zero => l
  | .succ m =>
    match l with
    | .nil => []
    | .cons hd tl => leftShift (tl ++ [hd]) m

@[simp]
theorem leftShift_zero {l : List α} :
    leftShift l 0 = l := rfl

@[simp]
theorem leftShift_nil {n : Nat} :
    leftShift ([] : List α) n = [] := by
  cases n <;> simp [leftShift]

@[simp]
theorem leftShift_cons_one {hd : α} {tl : List α} :
    leftShift (hd::tl) 1 = tl ++ [hd] := rfl

theorem leftShift_of_le_length {l : List α} {n : Nat} (h : n ≤ l.length) :
    leftShift l n = l.drop n ++ l.take n := by
  induction n generalizing l with
  | zero => simp
  | succ m ih =>
    have : m ≤ l.length := by
      apply Nat.le_of_succ_le h
    cases l with
    | nil => simp
    | cons hd tl =>
      simp only [leftShift, List.drop_succ_cons, List.take_succ_cons]
      rw [ih]
      · simp only [List.length_cons, Nat.add_le_add_iff_right] at h
        simp [List.drop_append_of_le_length h, List.take_append_of_le_length h]
      · simpa

theorem leftShift_add_one {l : List α} {n1 : Nat} :
    leftShift l (n1 + 1) = leftShift (leftShift l n1) 1 := by
  induction n1 generalizing l with
  | zero => simp
  | succ m ih =>
    cases l with
    | nil => simp
    | cons hd tl =>
      conv =>
        lhs
        unfold leftShift -- prevent multiple unfolding
        simp
      rw [ih]
      have : leftShift (hd :: tl) (m + 1) = leftShift (tl ++ [hd]) m := by
        conv =>
          lhs
          simp [leftShift]
      rw [this]

theorem leftShift_add {l : List α} {n1 n2 : Nat} :
    leftShift l (n1 + n2) = leftShift (leftShift l n1) n2 := by
  induction n2 with
  | zero => simp
  | succ m ih =>
    simp [← Nat.add_assoc, leftShift_add_one, ih]

theorem leftShift_mul_length_eq_self {l : List α} {k : Nat}:
    leftShift l (k * l.length) = l := by
  induction k with
  | zero => simp
  | succ m ih =>
    simp only [Nat.add_mul, Nat.one_mul, leftShift_add, ih]
    rw [leftShift_of_le_length (by omega)]
    simp

@[simp]
theorem isEmpty_leftShift_eq_isEmpty (l : List α) (n : Nat) :
    (leftShift l n).isEmpty = l.isEmpty := by
  induction n generalizing l with
  | zero => simp [leftShift]
  | succ m ih =>
    cases l with
    | nil => simp [leftShift]
    | cons hd tl =>
      simp [leftShift, ih]

theorem Nat.exists_eq_mul_mod (n m : Nat) :
    ∃ k, n = k * m + n % m := by
  exists (n - n % m)/m
  rw [← Nat.div_eq_sub_mod_div]
  rw [div_add_mod']

theorem leftShift_eq_leftShift_mod_length (l : List α) (n : Nat) :
    leftShift l n = leftShift l (n % l.length) := by
  have := Nat.exists_eq_mul_mod n l.length
  rcases this with ⟨k, hk⟩
  conv =>
    lhs
    rw [hk, leftShift_add, leftShift_mul_length_eq_self]

def isleftShiftOf (l l' : List α) : Prop := ∃ (n : Nat), l' = leftShift l n

theorem isleftShiftOf_iff_exists (l l' : List α) :
    isleftShiftOf l l' ↔ ∃ (u v : List α), l = u ++ v ∧ l' = v ++ u := by
  simp [isleftShiftOf]
  by_cases hl : l = []
  · simp [hl]
    constructor
    · intro h
      exists []
      exists []
    · intro h
      rcases h with ⟨u,v, huv, h⟩
      simp [h, huv]
  · constructor
    · intro h'
      rcases h' with ⟨n , h⟩
      rw [leftShift_eq_leftShift_mod_length] at h
      rw [leftShift_of_le_length] at h
      · exists (l.take (n % l.length))
        exists (l.drop (n % l.length))
        refine And.intro ?_ h
        exact Eq.symm (List.take_append_drop (n % l.length) l)
      · apply Nat.le_of_lt
        apply Nat.mod_lt
        exact List.length_pos_iff.mpr hl
    · intro h'
      rcases h' with ⟨u, v, h, h'⟩
      exists u.length
      simp [h, h', leftShift_of_le_length]

def countBreakPointsAndGetEnd (l : List Int) (hl : l ≠ []) : Nat × Int :=
  go l 0 hl where
  go (l : List Int) (curr : Nat) (hl : l ≠ []) : Nat × Int :=
  match l with
  | .nil => by simp at hl
  | .cons hd tl =>
    match tl with
    | .nil => (curr, hd)
    | .cons hd' tl' =>
      if hd < hd'
      then go (hd' :: tl') curr (by simp)
      else go (hd' :: tl') (curr + 1) (by simp)

theorem countBreakPointsAndGetEndGoIncreasing (l : List Int) (curr : Nat) (hl : l ≠ []) :
    (countBreakPointsAndGetEnd.go l curr hl).fst ≥ curr := by
  induction l generalizing curr with
  | nil => simp at hl
  | cons hd tl ih =>
    cases tl with
    | nil => simp [countBreakPointsAndGetEnd.go]
    | cons hd' tl' =>
      simp only [countBreakPointsAndGetEnd.go, ge_iff_le]
      split
      · apply ih
      · specialize ih (curr + 1) (by simp)
        apply Nat.le_trans ?_ ih
        simp

theorem countBreakPointsAndGetEnd_fst_eq_zero_iff_sorted (l : List Int) (hl : l ≠ []) :
    (countBreakPointsAndGetEnd l hl).fst = 0 ↔ List.Pairwise (fun (a b : Int) => a < b) l := by
  simp [countBreakPointsAndGetEnd]
  induction l with
  | nil => simp at hl
  | cons hd tl ih =>
    cases tl with
    | nil => simp [countBreakPointsAndGetEnd.go]
    | cons hd' tl' =>
      simp only [countBreakPointsAndGetEnd.go, Nat.zero_add, List.pairwise_cons, List.mem_cons,
        forall_eq_or_imp]
      simp only [ne_eq, reduceCtorEq, not_false_eq_true, List.pairwise_cons] at ih
      split
      · rename_i hhd
        rw [ih True.intro]
        simp only [hhd, true_and, iff_and_self, and_imp]
        intro h₁ _ x hx
        apply Int.lt_trans hhd (h₁ x hx)
      · rename_i hhd
        simp only [hhd, false_and, iff_false]
        intro h
        have := countBreakPointsAndGetEndGoIncreasing (hd' :: tl') 1 (by simp)
        simp [h] at this

def countGlobalBreakPoints (l : List Int) : Nat :=
  if h : l.length < 2
  then 0
  else
    have : l ≠ [] := by
      rw [List.ne_nil_iff_length_pos]
      simp at h
      exact Nat.zero_lt_of_lt h
    let (count, listEnd) := countBreakPointsAndGetEnd l this
    let start := l.head this

    if start < listEnd
    then count + 1
    else count

theorem countBreakPointsAndGetEnd_fst_eq_zero_of_countGlobalBreakPoints
    {l : List Int} (hl : l ≠ []) (h : countGlobalBreakPoints l = 0) :
    (countBreakPointsAndGetEnd l hl).fst = 0 := by
  cases l with
  | nil => simp at hl
  | cons hd tl =>
    cases tl with
    | nil => rfl
    | cons hd' tl' =>
      simp [countGlobalBreakPoints] at h
      specialize h True.intro
      split at h
      · simp at h
      · exact h

theorem countGlobalBreakPoints_of_countBreakPointsAndGetEnd {l : List Int} {hl : l ≠ []} {n : Nat}
    (h : (countBreakPointsAndGetEnd l hl).fst = n) :
    countGlobalBreakPoints l = n ∨ countGlobalBreakPoints l = n + 1 := by
  cases l with
  | nil => simp at hl
  | cons hd tl =>
    cases tl with
    | nil =>
      simp [countBreakPointsAndGetEnd, countBreakPointsAndGetEnd.go] at h
      simpa [countGlobalBreakPoints]
    | cons hd' tl' =>
      simp [countGlobalBreakPoints, h]
      split
      · rename_i htl
        false_or_by_contra
        revert htl
        simp
      · split <;> simp

theorem countGlobalBreakPoints_leftShift_eq (l : List Int) (hl : l ≠ []) (n : Nat) :
    countGlobalBreakPoints (leftShift l n) = countGlobalBreakPoints l := by
  induction n generalizing l with
  | zero => simp
  | succ m ih =>
    simp [leftShift]
    cases l with
    | nil => simp
    | cons hd tl =>
      simp
      rw [ih _ (by simp)]
      sorry

def move_one_ball (l : List Int) : Bool :=
  countGlobalBreakPoints l ≤ 1

theorem move_one_ball_correct_iff (l : List Int) :
    move_one_ball l = true ↔
    ∃ (l' : List Int), isleftShiftOf l l' ∧ List.Pairwise (fun (a b : Int) => a < b) l' := by
  simp [move_one_ball, Nat.le_succ_iff]
  by_cases hl: l.length < 2
  · simp [countGlobalBreakPoints, hl]
    exists l
    simp [isleftShiftOf]
    constructor
    · exists 0
    · cases l with
      | nil => simp
      | cons hd tl =>
        cases tl with
        | nil => simp
        | cons hd' tl' =>
          simp at hl
          omega
  · have hl' : l ≠ [] := by
      apply List.ne_nil_of_length_pos
      simp at hl
      exact Nat.zero_lt_of_lt hl
    constructor
    · intro h
      cases h with
      | inl h =>
        exists l
        simp [isleftShiftOf]
        have := countBreakPointsAndGetEnd_fst_eq_zero_of_countGlobalBreakPoints hl' h
        rw [countBreakPointsAndGetEnd_fst_eq_zero_iff_sorted] at this
        refine And.intro ?_ this
        exists 0
      | inr h =>
        simp [countGlobalBreakPoints, hl] at h
        split at h
        · simp at h
          exists l
          rw [countBreakPointsAndGetEnd_fst_eq_zero_iff_sorted] at h
          refine And.intro ?_ h
          simp [isleftShiftOf]
          exists 0
        · sorry
    · false_or_by_contra
      rename_i h h'
      simp at h'
      rcases h with ⟨l', hshift, hsort⟩
      simp [isleftShiftOf] at hshift
      rcases hshift with ⟨n, hshift⟩
      have leftShift_ne_nil : leftShift l n ≠ [] := by
        rw [ne_eq, ← List.isEmpty_iff]
        simpa
      rw [hshift, ← countBreakPointsAndGetEnd_fst_eq_zero_iff_sorted _ leftShift_ne_nil] at hsort
      simp [← countGlobalBreakPoints_leftShift_eq l hl' n] at h'
      have := countGlobalBreakPoints_of_countBreakPointsAndGetEnd hsort
      simp at this
      cases this with
      | inl this => simp [this] at h'
      | inr this => simp [this] at h'

theorem testCase1 : move_one_ball [3,4,5,1,2] = True := by native_decide
theorem testCase2 : move_one_ball [3,5,10,1,2] = True := by native_decide
theorem testCase3 : move_one_ball [4,3,1,2] = False := by native_decide
theorem testCase4 : move_one_ball [3,5,4,1,2] = False := by native_decide
theorem testCase5 : move_one_ball [] = True := by native_decide

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
