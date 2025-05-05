import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Combinatorics.SimpleGraph.IncMatrix
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

universe u v

/-- placeholder for set of spanning trees of a graph -/
-- here we take all edge-subsets of size N - 1, where N = number of vertices
def spanningTreeFinset {V : Type} [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet]: Finset (Finset (Sym2 V)) :=
  Finset.powersetCard ((Fintype.card V) - 1) G.edgeFinset

#eval (Fintype.card (Fin 4)) - 1

/-- placeholder for reduced Laplacian matrix of a graph -/
def redLapMatrix {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] [AddGroupWithOne ℤ] (q : V) : Matrix V V ℤ :=
  let char_q : V → ℤ := fun (x : V) => if x = q then 1 else 0
  ((G.lapMatrix ℤ).updateRow q char_q).updateCol q char_q

/-- placeholder for signed incidence matrix of a graph -/
noncomputable def signIncMatrix {V : Type} (G : SimpleGraph V) : Matrix V (Sym2 V) ℤ :=
  G.incMatrix ℤ

/-- statement of Matrix-Tree Theorem -/
theorem matrix_tree_theorem {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj] : ∀ q : V, (redLapMatrix G q).det = (spanningTreeFinset G).card := by
  sorry


/-- Laplacian matrix is equal to self-product of (signed) incidence matrix -/
lemma lapMatrix_incidenceMatrix_prod {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj] :
  G.lapMatrix ℤ = (signIncMatrix G : Matrix V (Sym2 V) ℤ) * ((signIncMatrix G : Matrix V (Sym2 V) ℤ).transpose) := by
  sorry

/-- Cauchy-Binet for determinant of product -/
example : Prop := ⊤

/-- determinant of spanning-tree minor of incidence matrix: if S ⊆ E(G), then
      - B₀[S].det is equal to ±1 if S forms a spanning tree
      - B₀[S].det is equal to 0 otherwise -/
lemma indcidenceMatrix_submatrix_det {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [Fintype G.edgeSet] (S : V → Sym2 V) : ((signIncMatrix G).submatrix id S).det ∈ ({1, -1, 0} : Finset ℤ) :=
  sorry


/-- the number of spanning trees satsifies the deletion-contraction relation;
      #(spanning trees of G) = #(spanning trees of G\e) + #(spanning trees of G/e)  -/
example : Prop := ⊤

/-- the determinant of the reduced Laplacian L₀ satisifies the deletion-contraction relation:
      L₀(G).det = L₀(G\e).det + L₀(G/e)
    if edge e is not a bridge -/
example : Prop := ⊤
