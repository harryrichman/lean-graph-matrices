# lean-graph-matrices

Formalize a statement and proof of the [matrix tree theorem](https://en.wikipedia.org/wiki/Kirchhoff%27s_theorem) in Lean:

> If $G$ is a simple graph with Laplacian matrix $L$, then for any vertex $q$ we have
> $$
> \det L |_q = \#(\text{spanning trees of }G),
> $$
> where $L |_q$ denotes the matrix with $q$-indexes row and column removed.

## Pieces of theorem statement

- Laplacian matrix, mathlib: [SimpleGraph.lapMatrix](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/LapMatrix.html#SimpleGraph.lapMatrix)
- subgraph, mathlib: [SimpleGraph.Subgraph](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/Subgraph.html#SimpleGraph.Subgraph)
  - spanning tree
- determinant, mathlib: [Matrix.det](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.html#Matrix.det)
- submatrix, mathlib: [Matrix.submatrix](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Matrix/Defs.html#Matrix.submatrix)
  - subsets, mathlib: [Finset.powersetCard](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Powerset.html#Finset.powersetCard)
  - inclusion maps, mathlib: [OrderEmbedding](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Hom/Basic.html#OrderEmbedding)




## Using Lean

Search tools:

- human language
  - [Lean search](https://leansearch.net/)
  - [Zulip chat](https://leanprover.zulipchat.com)
  - Moogle
- Lean code
  - [Loogle](https://loogle.lean-lang.org/)