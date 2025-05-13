import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finite.Card

set_option diagnostics true

universe u

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Problem: should we implement a spanning tree as a subgraph, or a Finset of edges? Is it easy to convert between the two? -/

-- Spanning tree type of a SimpleGraph
structure SpanningTree (G : SimpleGraph V) where
  Tree : SimpleGraph V
  subG : Tree ≤ G
  isTree : Tree.IsTree

def SpanningTree' {V : Type u} (G : SimpleGraph V) :=
  {T : SimpleGraph V // T ≤ G ∧ T.IsTree}

instance (G : SimpleGraph V) : Decidable G.Connected := by
  -- apply decidable_of_iff _ (SimpleGraph.connected_iff_exists_forall_reachable G)
  sorry

-- show that G.IsTree is decidable
noncomputable instance (G : SimpleGraph V) : Decidable G.IsTree := by
  -- For connected graphs with (n-1) edges:
  have h : _ := G.isTree_iff_connected_and_card
  -- have hcard : Nat.card V = Fintype.card V := by
  --   apply Nat.card_eq V
  apply decidable_of_iff (G.Connected ∧ Nat.card G.edgeSet + 1 = Nat.card V) (iff_comm.2 h)

instance (G : SimpleGraph V) [Fintype G.edgeSet] : Fintype (SpanningTree G) where
  -- elems := {T : SimpleGraph V | T ≤ G ∧ T.IsTree}
  elems :=
    let tree_set := Finset.filter (fun x => x.IsTree) (Finset.univ : Finset (SimpleGraph V))
    tree_set.map (fun t => SpanningTree.mk t (by sorry) (by sorry))
  complete := by
    sorry

-- by
--   -- show that there are finitely many simple graphs on V, assuming V is finite
--   let x : Finset (SimpleGraph V) := Finset.univ
--   -- show that {spanning trees} are a subset of all simple graphs on V
--   -- have h : _ := SimpleGraph.iff
--   -- let y : Finset ({T : SimpleGraph V // T ≤ G}) := Finset.univ
--   -- apply Finite.of_injective SimpleGraph.Adj
--   -- apply SimpleGraph.ext
--   sorry -- infer_instance

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
  -- {A ∈ edge_sets | (SimpleGraph.fromEdgeSet A.toSet).IsTree}
  edge_sets


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

instance : DecidableRel houseGraph.Adj :=
  fun a b => inferInstanceAs <| Decidable (hge a b || hge b a)

example : Prop := houseGraph.IsTree
example : ¬houseGraph.IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  simp only [Nat.card_eq_fintype_card, Fintype.card_ofFinset, Fintype.card_fin, Nat.reduceEqDiff,
    not_and]
  intro _
  decide -- houseGraph has 6 edges, not 4


example : houseGraph.Connected := by
  sorry

example : ¬houseGraph.IsAcyclic := by
  -- a graph is acyclic iff every edge is a bridge
  rw [SimpleGraph.isAcyclic_iff_forall_edge_isBridge]
  simp only [not_forall]
  simp only [exists_prop]
  -- show that edge (0, 1) is not a bridge
  use s(0, 1)
  -- split two claims
  constructor
  · -- show s(0, 1) is an edge
    decide
  · -- show s(0, 1) is not a bridge
    by_contra hbridge
    -- e is bridge means every cycle does not contain e
    rw [SimpleGraph.isBridge_iff_mem_and_forall_cycle_not_mem] at hbridge
    rcases hbridge with ⟨hedge, hnocycle⟩
    -- for contradiction, contruct a cycle that *does* contain s(0, 1)
    -- first, construct walk 0 - 1 - 4 - 0
    let nil : houseGraph.Walk 0 0 := SimpleGraph.Walk.nil
    let walk01 : houseGraph.Walk 1 0 := SimpleGraph.Walk.cons' 1 0 0 (by decide) nil
    let walk04 : houseGraph.Walk 4 0 := SimpleGraph.Walk.cons' 4 1 0 (by decide) walk01
    let walk00 : houseGraph.Walk 0 0 := SimpleGraph.Walk.cons' 0 4 0 (by decide) walk04
    specialize hnocycle walk00
    -- check that constructed walk is a cycle
    have h00cycle: walk00.IsCycle := by
      rw [SimpleGraph.Walk.isCycle_def]
      rw [SimpleGraph.Walk.isTrail_def]
      decide
    apply hnocycle h00cycle
    decide

#check SimpleGraph.IsBridge
#check houseGraph.Walk 0 0

-- #eval (spanningTreeFinset houseGraph)
#check ({T : SimpleGraph V // True})
#check (Set.univ : Set (SpanningTree houseGraph))
-- #eval (Finset.univ : Finset (SpanningTree houseGraph))
