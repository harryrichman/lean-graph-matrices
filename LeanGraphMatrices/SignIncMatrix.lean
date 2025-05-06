import Mathlib.Combinatorics.SimpleGraph.IncMatrix

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

#check B
-- #eval B
#check B * B.transpose

noncomputable def Bprod := B * B.transpose

#check Bprod
