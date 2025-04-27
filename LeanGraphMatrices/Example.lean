import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-- Work through parts of matrix-tree theorem for one specific graph,
i.e. finding its Laplacian and spanning trees etc. -/

example : Bool := True

/-- Define simple graph -/

example : Bool := True

-- edge set of house graph
def hge : (Fin 5) → (Fin 5) → Bool
  | 0, 1 => true
  | 1, 2 => true
  | 2, 3 => true
  | 3, 4 => true
  | 4, 0 => true
  | 1, 4 => true
  | _, _ => false

#check hge
#eval hge 0 1
#eval hge 0 2

def houseGraph : SimpleGraph (Fin 5) where
  Adj v w := hge v w || hge w v
  symm := by {
    dsimp [Symmetric]
    decide
  }
  loopless := by {
    dsimp [Irreflexive]
    decide
  }

-- seems to be required to `#eval` number of edges
instance : DecidableRel houseGraph.Adj :=
  fun a b => inferInstanceAs <| Decidable (hge a b || hge b a)

#check houseGraph.edgeSet
#check houseGraph.edgeFinset

def num_edges := houseGraph.edgeFinset.card
#eval num_edges -- 6

/-- Laplacian matrix of a graph -/

def L := houseGraph.lapMatrix ℤ

#check L
#eval L

def L' : Matrix (Fin 5) (Fin 5) ℤ :=
  !![2, -1,  0,  0, -1;
    -1,  3, -1,  0, -1;
     0, -1,  2, -1,  0;
     0,  0, -1,  2, -1;
    -1, -1,  0, -1,  3]
#eval L == L'

#check L.det
#eval L.det -- 0


/-- Reduced Laplacian matrix -/

-- The embedding f : Fin 4 ↪ Fin 5 maps 0 to 0 and 1 to 1, etc.
-- This is the standard embedding of Fin 4 into Fin 5.
-- We can use Fin.castLEEmb for this (requires proof 4 <= 5)
def inc₄₅ : Fin 4 ↪ Fin 5 := Fin.castLEEmb (by decide : 4 ≤ 5)

def L0 : Matrix (Fin 4) (Fin 4) ℤ :=
  L.submatrix inc₄₅ inc₄₅

#check L0
#eval L0

#eval L0.det -- 11


/-- Set of spanning trees of G -/
