import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic.Linarith

variable (M : Matrix (Fin r) (Fin s) Rat)

abbrev rowListofMat := List.map List.ofFn (List.ofFn M)

lemma rowListLength_eq_numRow : (rowListofMat M).length = r := by simp

lemma rowListofMat_elt_length_eq_numCol : ∀ i, ((rowListofMat M).get i).length = s := by simp

lemma rowLengthEq : ∀ i j, (List.ofFn (M i)).length = (List.ofFn (M j)).length := by simp

abbrev colListofMat := List.map List.ofFn (List.ofFn M.transpose)

lemma colListLength_eq_numCol : (colListofMat M).length = s := by simp

/-Row-reduced form
1. The last nonzero entry of every row must be 1
2. Each column containing the first nonzero entry of a row must have all its other
   entries as 0
-/

def isRRFRow (ri : List Rat) : Prop×(Option Nat) :=
  if ri.all (fun x => x==0) then (True,none)
  else
    if ri.indexOf 1 = ri.length then (False,none)
    else
      if (ri.after (fun x => ((ri.indexOf x) == ri.length-1-((ri.reverse).indexOf 1)))).all (fun x => x==0)
      then (True,ri.length - 1 - ((ri.reverse).indexOf 1))
      else (False,none)

def isRRFCol (j : List Rat) : Prop :=
  let cj := List.erase j 1
  List.all cj (fun x => x==0)

--In a matrix that is in row-reduced form, the index of 1 in a row that isn't all zero is less than the length of the row
lemma nonzIndLe (rl : List Rat) (h : (isRRFRow rl).1 = True) (h' : ¬(rl.all (fun x => x==0))) :
  (((isRRFRow rl).2).getD 0) < rl.length := by
  unfold isRRFRow
  split_ifs with h1 h2
  · have : (isRRFRow rl).1 = False := by unfold isRRFRow; rw [if_neg h', if_pos h1]
    simp at h this; contradiction
  · show rl.length - 1 - List.indexOf 1 rl.reverse < rl.length
    rw [Nat.sub_sub]
    by_cases h5 : (1 + List.indexOf 1 rl.reverse) ≤ rl.length
    · apply Nat.sub_lt_self
      linarith; assumption
    · push_neg at h5
      rw [Nat.sub_eq_zero_iff_le.mpr (le_of_lt h5)]
      by_cases h6 : rl = []
      · rw [h6] at h'; contradiction
      · exact List.length_pos.mpr h6
  · have : (isRRFRow rl).1 = False := by
      unfold isRRFRow; rw [if_neg h', if_neg h1, if_neg h2]
    simp at h this; contradiction

def isRrfMatAux (rl : List (List Rat)) (cl : List (List Rat)) (h : ∀ i, (rl.get i).length = cl.length) : Bool :=
  match rl with
  | [] => True
  | a::as =>
    have h0 := (List.subset_cons a as)
    have h0' : ∀ i, as.get i ∈ as := by
      intro i; rw [as.mem_iff_get]; use i
    have h0'' : ∀ i, as.get i ∈ a::as := fun i => h0 (h0' i)
    have h0''' : ∀ i, (as.get i).length = ((a::as).get i.castSucc).length := by
      intro i
      obtain ⟨n,hn⟩ := ((a::as).mem_iff_get).mp (h0'' i)
      have l1 := h (Fin.castSucc i); have l2 := h n; rw [←l1, hn] at l2; exact l2
    if h1 : a.all (fun x => (x==0)) then isRrfMatAux as cl (by intro i; have := h (i.castSucc); rw [← (h0''' i)] at this; exact this)
    else
      if h2 : (isRRFRow a).1 = True then
        have h3 := nonzIndLe a h2 h1
        have h4 : (isRRFRow a).2.getD 0 < cl.length := by
          have := h ⟨0,Nat.zero_lt_succ as.length⟩;  simp at this; rw [this] at h3; exact h3
        if (isRRFCol (cl.get ⟨(((isRRFRow a).2).getD 0),h4⟩)) = False then False
        else isRrfMatAux as cl (by intro i; have := h (i.castSucc); rw [← (h0''' i)] at this; exact this)
      else False

--Checks whether matrix is in row-reduced form
def isRrfMat : Bool :=
  isRrfMatAux (rowListofMat M) (colListofMat M) (by rw [colListLength_eq_numCol]; exact (rowListofMat_elt_length_eq_numCol M))

/-
Row-reduced echelon form
1. The matrix must be row-reduced
2. All rows that have only 0s must occur before those that have a nonzero entry
3. If rows 1,...,r are the nonzero rows and the last nonzero entry for each of
these rows occurs in columns k₁,k₂,...,k_r, then  k₁>k₂>...>k_r
-/

--Gives list containing k₁,k₂,...,k_r
-- def nonzColIndices : List (List Rat) → List ℕ
--   | [] => []
--   | a::as =>
--       if (isRRFRow a).1 = True then [((isRRFRow a).2).getD 0] ++ (nonzColIndices as)
--       else []

def nonzColIndices : List (List Rat) → List ℕ                          -- Failed to show termination
  | [] => []
  | a::as =>
     let h := nonzColIndices as
      if (isRRFRow a).1 = True then
         [((isRRFRow a).2).getD 0] ++ h
      else []

abbrev isZeroMatrix : Prop := (rowListofMat M).all (fun x => (x.all (fun y => y==0 )))

--Checks whether matrix is in row-reduced echelon form
def isRrefMat (M : Matrix (Fin r) (Fin s) Rat) : Prop :=
  let rl := rowListofMat M
  -- if isZeroMatrix M then True
  -- else
    if (isRrfMat M) = False then False
    else
      if h : rl.findIdxs (fun x => (x.any (fun y => ¬(y==0)))) ≠ [] then
        let indOfLastNonzeroEntryOne := (rl.findIdxs (fun x => (x.any (fun y => ¬(y==0))))).getLast h
        let r0ws_ind := (List.unzip (rl.indexesValues (fun x => x.all (fun x => x==0)))).1
        if ([indOfLastNonzeroEntryOne]++r0ws_ind).Sorted (·≤·) then
          let L := List.filter (fun x => x.any (fun x => ¬x==0)) rl
          (nonzColIndices L).Sorted (·>·)
        else False
      else (nonzColIndices rl).Sorted (·>·)
