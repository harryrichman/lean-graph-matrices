import Mathlib.Combinatorics.SimpleGraph.IncMatrix
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

variable (R : Type) --

variable {V : Type} [DecidableEq V] (G : SimpleGraph V)
variable [G.LocallyFinite]

/-- incidence matrix; copied from mathlib version without `noncomputable` -/
def incMatrix' (G : SimpleGraph V) [G.LocallyFinite] : Matrix V (Sym2 V) ℤ :=
  fun a b => if b ∈ (G.incidenceFinset a) then 1 else 0
  -- Set.indicator (G.incidenceFinset a) 1

#check G.neighborSet
#check G.incidenceSet
#check G.incidenceFinset
#check G.LocallyFinite


-- edge set of house graph
def hge : (Fin 5) → (Fin 5) → Bool
  | 0, 1 => true
  | 1, 2 => true
  | 2, 3 => true
  | 3, 4 => true
  | 4, 0 => true
  | 1, 4 => true
  | _, _ => false

def hG : SimpleGraph (Fin 5) where
  Adj v w := hge v w || hge w v
  symm := by
    dsimp [Symmetric]; decide
  loopless := by
    dsimp [Irreflexive]; decide

-- seems to be required to `#eval` number of edges
instance : DecidableRel hG.Adj :=
  fun a b => inferInstanceAs <| Decidable (hge a b || hge b a)

noncomputable def B := hG.incMatrix ℤ
def B' := incMatrix' hG

#check B
-- #eval B
#check B * B.transpose

#check incMatrix' hG
#eval incMatrix' hG 0 s(0, 4)
#eval (B' * B'.transpose)
#eval (B' * B'.transpose).det

noncomputable def Bprod := B * B.transpose

#check Bprod
