import Mathlib.Data.Matrix.Notation

variable (M : Matrix (Fin r) (Fin s) Rat)

def mat_rowlistAux : List (Fin r → Rat) → List (List Rat)
| [] => []
| a::as => [List.ofFn a] ++ (mat_rowlistAux as)

-- Creates a list out of the rows of the matrix
def mat_rowlist : List (List Rat) :=
  mat_rowlistAux (List.ofFn M)

--Creates a list out of the columns of a matrix
def mat_collist := mat_rowlistAux (List.ofFn M.transpose)

/-Row-reduced form
1. The last nonzero entry of every row must be 1
2. Each column containing the first nonzero entry of a row must have all its other
   entries as 0
-/

--Checks whether condition 1 is satisfied for a given row
def is_rrf_row (ri : List Rat) : Bool×Nat :=
  if ri.all (fun x => x==0) then (True,0) --If not handled separately, getLast! panics
  else
    let should_0 := ri.after (fun x => ((ri.indexOf x) == (ri.indexesOf 1).getLast!))
    if should_0.all (fun x => x==0) then (True,(ri.indexesOf 1).getLast!)
    else (False,0)

--Checks whether condition 2 is satisfied for a given column
def is_rrf_col (j : List Rat) : Bool :=
  let cj := (List.extractP (fun x => x==1) j).2
  if List.all cj (fun x => x==0) then True
  else False

def is_rrf_mat_aux (rl : List (List Rat)) (cl : List (List Rat)) : Bool :=
  match rl with
  | [] => True
  | a::as =>
    if a.all (fun x => (x==0)) then is_rrf_mat_aux as cl
    else
      if ¬((is_rrf_row a).1) then False
      else
        if ¬(is_rrf_col (cl.get! (is_rrf_row a).2)) then False
        else is_rrf_mat_aux as cl

--Checks whether matrix is in row-reduced form
def is_rrf_mat : Bool :=
  is_rrf_mat_aux (mat_rowlist M) (mat_collist M)

/-
Row-reduced echelon form
1. The matrix must be row-reduced
2. All rows that have only 0s must occur before those that have a nonzero entry
3. If rows 1,...,r are the nonzero rows and the last nonzero entry for each of
these rows occurs in columns k₁,k₂,...,k_r, then  k₁>k₂>...>k_r
-/

--Gives list containing k₁,k₂,...,k_r
def nonz_col_indices : List (List Rat) → List ℕ
  | [] => []
  | a::as =>
    if ¬(is_rrf_row a).1 then []
    else [(is_rrf_row a).2] ++ (nonz_col_indices as)

--Checks whether matrix is in row-reduced echelon form
def is_rref_mat (M : Matrix (Fin r) (Fin s) Rat) : Bool :=
  if (mat_rowlist M).all (fun x => (x.all (fun y => y==0 ))) then True
  else
  if ¬(is_rrf_mat M) then False
  else
    let rl := mat_rowlist M
    let last_nz := (rl.findIdxs (fun x => (x.any (fun y => ¬(y==0))))).getLast!
    let r0ws_ind := (List.unzip (rl.indexesValues (fun x => x.all (fun x => x==0)))).1
    if ([last_nz]++r0ws_ind).Sorted (·≤·) then
      let L := List.filter (fun x => x.any (fun x => ¬x==0)) rl
      if (nonz_col_indices L).Sorted (·>·) then True
      else False
    else False

#eval is_rref_mat !![(1:Rat)/2,0,-3,1,0;2,1,0,0,0]
#eval is_rref_mat !![0,0;0,0]
#eval is_rref_mat !![1,2,3;4,5,6;7,8,9]

def C := !![-1,0,1;2,1,0;0,0,(0:Rat)]
#eval is_rref_mat C
