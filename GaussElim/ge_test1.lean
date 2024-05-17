import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basis

variable (M : Matrix (Fin m) (Fin n) Rat) (hm : m>0) (hn : n>0)

abbrev rowListofMat := List.map List.ofFn (List.ofFn M)

lemma rowListLength_eq_numRow : (rowListofMat M).length = m := by simp

lemma rowListofMat_elt_length_eq_numCol : ∀ i, ((rowListofMat M).get i).length = n := by simp

lemma rowLengthEq : ∀ i j, (List.ofFn (M i)).length = (List.ofFn (M j)).length := by simp

abbrev colListofMat := List.map List.ofFn (List.ofFn M.transpose)

lemma colListLength_eq_numCol : (colListofMat M).length = n := by simp

/-Row-reduced form
1. The first nonzero entry of every row must be 1
2. Each column containing the first nonzero entry of a row must have all its other
   entries as 0
-/

def row_allZerosBeforeFirstOne (row : List Rat) : Bool :=
  List.isPrefixOf (List.replicate (row.indexOf 1) 0) row

def isRowReduced_row (ri : List Rat) : Bool×(Option Nat) :=
  if ri.all (fun x => x==0) then (true,none)
  else
    if ri.indexOf 1 = ri.length then (false,none)
    else
      if row_allZerosBeforeFirstOne ri then (true,ri.indexOf 1)
      else (false,none)

def isRowReduced_col (cj : List Rat) : Bool := List.all (List.erase cj 1) (fun x => x==0)

--In a matrix that is in row-reduced form, the index of 1 in a row that isn't all zero is less than the length of the row
lemma indFirstOne_lt_rowLength (rl : List Rat) (h : (isRowReduced_row rl).1 = true) (h' : ¬(rl.all (fun x => x==0))) :
  (((isRowReduced_row rl).2).getD 0) < rl.length := by
  unfold isRowReduced_row
  split_ifs with h1 h2
  · have : (isRowReduced_row rl).1 == false := by unfold isRowReduced_row; rw [if_neg h', if_pos h1]; rfl
    simp at h this; rw [h] at this; contradiction
  · show rl.indexOf 1 < rl.length
    apply List.indexOf_lt_length.mpr
    rcases lt_or_gt_of_ne h1 with indlt|indgt
    exact List.indexOf_lt_length.mp indlt
    have l1 := rl.indexOf_le_length (a:=1)
    have nl1 := not_le_of_gt indgt
    contradiction
  · have : (isRowReduced_row rl).1 == false := by
      unfold isRowReduced_row; rw [if_neg h', if_neg h1, if_neg h2]; rfl
    simp at h this; rw [h] at this; contradiction

def list_allZero (l : List Rat) : Bool := l.all (fun x => (x==0))

def isRowReducedAux (rl : List (List Rat)) (cl : List (List Rat)) (h : ∀ i, (rl.get i).length = cl.length) : Bool :=
  match rl with
  | [] => true
  | a::as =>
    have h0 : ∀ i, as.get i ∈ as := by intro i; rw [as.mem_iff_get]; use i
    have h0' : ∀ i, (as.get i).length = ((a::as).get i.castSucc).length := by
      intro i
      obtain ⟨n,hn⟩ := ((a::as).mem_iff_get).mp ((List.subset_cons a as) (h0 i))
      have l1 := h (Fin.castSucc i); have l2 := h n; rw [←l1, hn] at l2; exact l2
    if h1 : list_allZero a then isRowReducedAux as cl (by intro i; have := h (i.castSucc); rw [← (h0' i)] at this; exact this)
    else
      if h2 : (isRowReduced_row a).1 then
       (isRowReduced_col (cl.get ⟨(((isRowReduced_row a).2).getD 0),((h ⟨0,Nat.zero_lt_succ as.length⟩) ▸ indFirstOne_lt_rowLength a h2 h1)⟩)) ∨
          isRowReducedAux as cl (by intro i; have := h (i.castSucc); rw [← (h0' i)] at this; exact this)
      else false

--Checks whether matrix is in row-reduced form
def isRowReduced : Bool :=
  isRowReducedAux (rowListofMat M) (colListofMat M) (by rw [colListLength_eq_numCol]; exact (rowListofMat_elt_length_eq_numCol M))

/-
Row-reduced echelon form
1. The matrix must be row-reduced
2. All rows that have only 0s must occur before those that have a nonzero entry
3. If rows 1,...,r are the nonzero rows and the first nonzero entry for each of
these rows occurs in columns k₁,k₂,...,k_r, then  k₁< k₂<...< k_r
-/

--Gives list containing k₁,k₂,...,k_r
def nonzColIndices : List (List Rat) → List ℕ
  | [] => []
  | a::as =>
      if ¬(isRowReduced_row a).1 then []
      else [((isRowReduced_row a).2).getD 0] ++ (nonzColIndices as)

def isZeroMatrix : Bool := (rowListofMat M).all (fun x => (x.all (fun y => y==0 )))

def zeroRowsLast : Bool :=
  let rl := rowListofMat M
  let indOfLastNonzeroRow := rl.length-1-((rl.reverse).findIdx (fun x => (x.any (fun y => ¬(y==0)))))
  let indsOfZeroRows := (List.unzip (rl.indexesValues (fun x => x.all (fun x => x==0)))).1
  ([indOfLastNonzeroRow]++indsOfZeroRows).Sorted (·≤·)

def isRowReducedEchelon : Bool :=
  (isZeroMatrix M) ∨
    (isRowReduced M) ∧
      (zeroRowsLast M) ∧
        (nonzColIndices (List.filter (fun x => x.any (fun x => ¬x==0)) (rowListofMat M))).Sorted (·<·)

------------------------------------------------------------------------------------------------------------

def I : Matrix (Fin m) (Fin m) Rat := Matrix.diagonal (fun _ => (1:Rat))

def eltScalarMul (c : Rat) (i : Fin m) : Matrix (Fin m) (Fin m) Rat :=
    1 + Matrix.stdBasisMatrix i i (c-1)

def eltRowSwap (i : Fin m) (j : Fin m) : Matrix (Fin m) (Fin m) Rat :=
    let newr := (I i)
    Matrix.updateRow (Matrix.updateRow I i (I j)) j newr

def eltRowAdd (i : Fin m) (j : Fin m) (c : Rat) : Matrix (Fin m) (Fin m) Rat :=
    1 + Matrix.stdBasisMatrix i j c

-- def ge_aux_findpivot : (fin m) → (fin m) → (fin n) → (matrix (fin m) (fin n) α) → (matrix (fin m) (fin n) α)
-- | ⟨0, h₁⟩        i₀ j₀ M := M
-- | ⟨(k + 1), h₁⟩ i₀ j₀ M :=
--         if k ≥ i₀.val then
--             if M ⟨k+1, h₁⟩ j₀ ≠ 0
--                 then matrix.mul (elementary.swap α ⟨k+1, h₁⟩ i₀).to_matrix M
--             else ge_aux_findpivot ⟨k, nat.lt_of_succ_lt h₁⟩ i₀ j₀ M
--         else M

example (x : Rat) (l : List Rat) (k : l.indexOf x < l.length) : x ∈ l := by
  exact List.indexOf_lt_length.mp k

#check List.findIdx_lt_length_of_exists

lemma findIdx_exists_of_lt_length (p : α → Bool) (l : List α) (h : l.findIdx p < l.length) : ∃ x∈l, p x
   := by
   have := List.findIdx_get (p:=p) (w:=h)
   use l.get ⟨List.findIdx p l, h⟩
   constructor
   · exact List.get_mem l (List.findIdx p l) h
   · exact this

lemma findIdx_notExists_of_eq_length (l : List α) (p : α → Bool) (hl : l.findIdx p = l.length) : ∀ x∈l, p x = false := by
  intro x xl
  by_cases h:p x
  have := List.findIdx_lt_length_of_exists ⟨x,xl,h⟩
  have := ne_of_lt this
  contradiction
  simpa using h

lemma findIdx_eq_length_of_notExists (l : List α) (p : α → Bool) (hl : ∀ x∈l, p x = false) : l.findIdx p = l.length := by
  contrapose hl
  push_neg at *; simp

lemma findIdx_le_length (l : List α) (p : α → Bool) : l.findIdx p ≤ l.length := by
  by_cases h : (∃ x∈l, p x)
  exact le_of_lt (List.findIdx_lt_length_of_exists h)
  push_neg at h; simp at h
  exact le_of_eq (findIdx_eq_length_of_notExists l p h)

def findNonzCol : ℕ := (colListofMat M).findIdx (fun col => ¬ list_allZero col)

#check List.indexOf_lt_length
#check List.extractP
#check List.findIdx_get
#check List.all_eq_true
#check List.findIdx_get
#check Bool.not_iff_not

lemma findNonzCol_le_numCol : (findNonzCol M) ≤ (colListofMat M).length := by
  unfold findNonzCol
  apply findIdx_le_length (colListofMat M) (fun col => ¬list_allZero col)

lemma nonzListHasNonz (h : ¬list_allZero l) : ∃ x∈l, x≠0 := by
  unfold list_allZero at h
  rw [List.all_eq_true] at h
  push_neg at h
  convert h; simp

lemma findNonzCol_get_HasNonz (h : findNonzCol M < (colListofMat M).length) :
  ∃ x ∈ (colListofMat M).get ⟨findNonzCol M,h⟩, x≠0 := by
  unfold findNonzCol at h
  have := List.findIdx_get (w:=h)
  simp only [Bool.not_eq_true, Bool.decide_eq_false] at this
  rw [Bool.not_iff_not] at this
  obtain ⟨x,hx,xn0⟩ := nonzListHasNonz this
  use x
  constructor
  unfold findNonzCol
  convert hx; simp
  assumption

def findPivot : Rat :=
    if h1 : findNonzCol M = (colListofMat M).length then 1
    else
      if h2 : findNonzCol M < (colListofMat M).length then
        let pcol := (colListofMat M).get ⟨findNonzCol M,h2⟩
        have h3 : pcol.findIdx (fun x => x≠0) < pcol.length := by
          have h4 := findNonzCol_get_HasNonz M h2
          unfold_let pcol
          apply List.findIdx_lt_length_of_exists
          convert h4; simp
        pcol.get ⟨pcol.findIdx (fun x => x≠0),h3⟩
      else
        have h4 := findNonzCol_le_numCol M
        have nh4 := not_le.mpr (lt_of_le_of_ne (not_lt.mp h2) (Ne.symm h1))
        absurd h4 nh4
