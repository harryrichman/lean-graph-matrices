import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-- Work through parts of matrix-tree theorem for one specific graph,
i.e. finding its Laplacian and spanning trees etc. -/

example : Bool := True

/-- Define simple graph -/

example : Bool := True

-- edge set of house graph
inductive HGE : (Fin 5) → (Fin 5) → Prop
  | e01 : HGE 0 1
  | e12 : HGE 1 2
  | e23 : HGE 2 3
  | e34 : HGE 3 4
  | e40 : HGE 4 0
  | e14 : HGE 1 4
  -- reverse edges
  | e04 : HGE 0 4
  | e10 : HGE 1 0
  | e21 : HGE 2 1
  | e32 : HGE 3 2
  | e43 : HGE 4 3
  | e41 : HGE 4 1

#check HGE

def HouseGraph : SimpleGraph (Fin 5) where
  Adj := HGE
  symm := by {-- unfold Symmetric
    intros v w edge
    rcases edge
    repeat constructor
  }
  loopless := by {-- unfold Irreflexive
    intros v loop
    rcases loop
  }

#check HouseGraph.edgeSet

-- seems to be required by lapMatrix
variable [DecidableRel HouseGraph.Adj]

/-- Laplacian matrix of a graph -/

def L' : Matrix (Fin 5) (Fin 5) ℤ :=
  !![2, -1,  0,  0, -1;
    -1,  3, -1,  0, -1;
     0, -1,  2, -1,  0;
     0,  0, -1,  2, -1;
    -1, -1,  0, -1,  3]

def L := HouseGraph.lapMatrix ℤ

#check L
#eval L

#check Matrix.det L

-- #eval Matrix.det L'
#eval L'.det

/-- Reduced Laplacian matrix -/

-- The embedding f : Fin 4 ↪ Fin 5 maps 0 to 0 and 1 to 1, etc.
-- This is the standard embedding of Fin 4 into Fin 5.
-- We can use Fin.castLEEmb for this (requires proof 4 <= 5)
def inc₄₅ : Fin 4 ↪ Fin 5 := Fin.castLEEmb (by decide : 4 ≤ 5)

def L0' : Matrix (Fin 4) (Fin 4) ℤ :=
  L'.submatrix inc₄₅ inc₄₅

#check L0'
#eval L0'

#eval L0'.det
