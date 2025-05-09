import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Combinatorics.SimpleGraph.IncMatrix
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import LeanGraphMatrices.CauchyBinet

universe u v

variable {V : Type} [Fintype V] [LinearOrder V] [DecidableEq V]

/-- placeholder for set of spanning trees of a graph -/
-- here we take all edge-subsets of size N - 1, where N = number of vertices
def spanningTreeFinset (G : SimpleGraph V) [Fintype G.edgeSet]: Finset (Finset (Sym2 V)) :=
  Finset.powersetCard ((Fintype.card V) - 1) G.edgeFinset

/-- placeholder for reduced Laplacian matrix of a graph -/
def redLapMatrix [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] [AddGroupWithOne ℤ] (q : V) : Matrix V V ℤ :=
  let char_q : V → ℤ := fun (x : V) => if x = q then 1 else 0
  ((G.lapMatrix ℤ).updateRow q char_q).updateCol q char_q

/-- placeholder for signed incidence matrix of a graph -/
noncomputable def signIncMatrix (G : SimpleGraph V) : Matrix V (Sym2 V) ℤ :=
  G.incMatrix ℤ

noncomputable def redSignIncMatrix (G : SimpleGraph V) (q : V) : Matrix V (Sym2 V) ℤ :=
  G.incMatrix ℤ


/-- Laplacian matrix is equal to self-product of (signed) incidence matrix -/
lemma lapMatrix_incMatrix_prod (G : SimpleGraph V) [DecidableRel G.Adj] :
  G.lapMatrix ℤ = (signIncMatrix G) * ((signIncMatrix G).transpose) := by
  sorry

-- TODO: use reduced incidence matrix here
lemma redLapMatrix_incMatrix_prod (G : SimpleGraph V) [DecidableRel G.Adj] (q : V) :
  (redLapMatrix G q) = (redSignIncMatrix G q) * ((redSignIncMatrix G q).transpose) := by
  sorry

/-- determinant of spanning-tree minor of incidence matrix: if S ⊆ E(G), then
      - B₀[S].det is equal to ±1 if S forms a spanning tree
      - B₀[S].det is equal to 0 otherwise -/
-- TODO: image of S should contain edges of G; domain of S should be {v : V // v ≠ q}
lemma incMatrix_submatrix_det (G : SimpleGraph V) [Fintype G.edgeSet] (S : V → Sym2 V) : ((signIncMatrix G).submatrix id S).det ∈ ({1, -1, 0} : Finset ℤ) :=
  sorry

-- TODO: similar to above
lemma incMatrix_submatrix_det_hasCycle (G : SimpleGraph V) [Fintype G.edgeSet] (S : V → Sym2 V) : ¬(SimpleGraph.IsAcyclic (SimpleGraph.fromEdgeSet (Set.image S Set.univ))) → ((signIncMatrix G).submatrix id S).det = 0 :=
  sorry

-- TODO: similar to above
lemma incMatrix_submatrix_det_tree (G : SimpleGraph V) [Fintype G.edgeSet] (S : V → Sym2 V) : SimpleGraph.IsTree (SimpleGraph.fromEdgeSet (Set.image S Set.univ)) → ((signIncMatrix G).submatrix id S).det ∈ ({1, -1} : Finset ℤ) := by
  sorry

/-- statement of Matrix-Tree Theorem -/
theorem matrix_tree_theorem [LinearOrder (Sym2 V)] (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj] : ∀ q : V, (redLapMatrix G q).det = (spanningTreeFinset G).card := by
  intro q
  -- expand reduced Laplacian matrix as self-product of reduced incidence matrix
  rw [redLapMatrix_incMatrix_prod]
  -- apply Cauchy-Binet
  rw [Matrix.det_mul']
  -- simplify matrix expression
  simp_rw [← Matrix.transpose_submatrix]
  simp_rw [Matrix.det_transpose]
  -- apply the incidence-matrix-minor lemmas
  sorry



/-- the number of spanning trees satsifies the deletion-contraction relation;
      #(spanning trees of G) = #(spanning trees of G\e) + #(spanning trees of G/e)  -/
example : Prop := ⊤

/-- the determinant of the reduced Laplacian L₀ satisifies the deletion-contraction relation:
      L₀(G).det = L₀(G\e).det + L₀(G/e)
    if edge e is not a bridge -/
example : Prop := ⊤
