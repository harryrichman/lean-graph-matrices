# lean-graph-matrices

Formalize a statement and proof of the [matrix tree theorem](https://en.wikipedia.org/wiki/Kirchhoff%27s_theorem) in Lean:

> If $G$ is a simple graph with Laplacian matrix $L$, then for any vertex $q$ we have
> $\qquad \det L |_q = \\#(\text{spanning trees of }G)$,  
> where $L |_q$ denotes the matrix with $q$-indexed row and column removed.

## Pieces of theorem statement

- Laplacian matrix, mathlib: [SimpleGraph.lapMatrix](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/LapMatrix.html#SimpleGraph.lapMatrix)
- subgraph, mathlib: [SimpleGraph.Subgraph](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/Subgraph.html#SimpleGraph.Subgraph)
  - spanning tree, mathlib: [SimpleGraph.IsTree](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/Acyclic.html#SimpleGraph.IsTree)
- determinant, mathlib: [Matrix.det](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.html#Matrix.det)
- submatrix, mathlib: [Matrix.submatrix](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Matrix/Defs.html#Matrix.submatrix)
  - subsets, mathlib: [Finset.powersetCard](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Powerset.html#Finset.powersetCard)
  - inclusion maps, mathlib: [OrderEmbedding](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Hom/Basic.html#OrderEmbedding)

Other references:

- [Formalization](https://github.com/leanprover-community/mathlib4/blob/5fd096bd429d4dc16bfe66021dc227578aae3b6f/Archive/Wiedijk100Theorems/Konigsberg.lean#L78-L84) of the Königsberg bridges problem by Kyle Miller, on working with an explicit graph

- [SimpleGraph.fromEdgeSet](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/Basic.html#SimpleGraph.fromEdgeSet), define a graph from its edge set

- [Finset.erase](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Erase.html#Finset.erase), erase an element from a finite set

- [SimpleGraph.incMatrix](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/IncMatrix.html), the *unsigned* incidence matrix of a graph

- [Finset.sum_const_nat](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/BigOperators/Group/Finset/Basic.html#Finset.sum_const_nat)

- [Fin.sum_const](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/BigOperators/Fin.html#Fin.sum_const)

## Using Lean

Search tools:

- human language
  - [Lean search](https://leansearch.net/)
  - [Zulip chat](https://leanprover.zulipchat.com)
  - Moogle
- Lean code
  - [Loogle](https://loogle.lean-lang.org/)