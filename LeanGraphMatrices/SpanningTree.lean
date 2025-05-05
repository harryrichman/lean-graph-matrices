import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finite.Card
-- import Mathlib.Data.Finset.Sym2

universe u

variable {V : Type} [Fintype V] [DecidableEq V]
instance (G : SimpleGraph V) : Decidable G.Connected := by
  sorry

-- show that G.IsTree is decidable
noncomputable instance (G : SimpleGraph V) [Fintype G.edgeSet] : Decidable G.IsTree := by
  -- For connected graphs with (n-1) edges:
  have h : _ := G.isTree_iff_connected_and_card
  -- have hcard : Nat.card V = Fintype.card V := by
  --   apply Nat.card_eq V
  apply decidable_of_iff (G.Connected ∧ Nat.card G.edgeSet + 1 = Nat.card V) (iff_comm.2 h)

#check decidable_of_iff
#check SimpleGraph.isTree_iff_connected_and_card
#check Nat.card_eq
#check Finite V

/-- Define set of spanning trees of a SimpleGraph -/
def spanningTreeFinset {V : Type u} [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableEq G.edgeSet] : Finset (Finset (Sym2 V)) :=
  -- take an arbitrary edge e of G
  -- take e plus a spanning tree of (G / e)
  -- take a spanning tree of (G \ e)
  let edge_sets := Finset.powersetCard ((Fintype.card V) - 1) G.edgeFinset
  {A ∈ edge_sets | (SimpleGraph.fromEdgeSet A.toSet).IsTree}
#eval (Finset.univ : Finset (Fin 4)).card - 1
#eval (Fintype.card (Fin 4)) - 1


/-- Problem: should we implement a spanning tree as a subgraph, or a Finset of edges? Is it easy to convert between the two? -/

-- A spanning tree of a SimpleGraph is a subset of edges
structure SimpleGraph.SpanningTree {V : Type u} (G : SimpleGraph V) where -- : Type u
  /-- edges of the tree -/
  edges : Set G.edgeSet
  is_tree : (SimpleGraph.fromEdgeSet edges).IsTree
    H = SimpleGraph -- TODO: edges must form a tree


-- edge set of house graph
def hge : (Fin 5) → (Fin 5) → Bool
  | 0, 1 => true
  | 1, 2 => true
  | 2, 3 => true
  | 3, 4 => true
  | 4, 0 => true
  | 1, 4 => true
  | _, _ => false

def houseGraph : SimpleGraph (Fin 5) where
  Adj v w := hge v w || hge w v
  symm := by
    dsimp [Symmetric]
    decide
  loopless := by
    dsimp [Irreflexive]
    decide

-- seems to be required to `#eval` number of edges
instance : DecidableRel houseGraph.Adj :=
  fun a b => inferInstanceAs <| Decidable (hge a b || hge b a)

example : Prop := houseGraph.IsTree
example : houseGraph.IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  constructor
  · -- show graph is connected
    sorry
  · -- show graph has correct number of edges
    simp
    sorry

#check houseGraph.Connected
example : houseGraph.Connected := by
  sorry

#check houseGraph.IsAcyclic
example : houseGraph.IsAcyclic := by
  rw [SimpleGraph.isAcyclic_iff_forall_edge_isBridge]
  intro e
  sorry

#eval (spanningTreeFinset houseGraph)
