import Mathlib
import LeanGraphMatrices.ForMathlib

open scoped Matrix

-- #synth Ring ℕ

#synth Ring ℤ

variable {R : Type* } { m n : ℕ } [CommRing R]

#eval Finset.powersetCard 2 {"hello", "wo", "rld"}

#eval !![1, 2, 3; 4, 5, 6].submatrix id (Fin.succ)

theorem foo (x : ℕ) : x + x = x := by
  plausible

/-- Cauchy-Binet, https://en.wikipedia.org/wiki/Cauchy%E2%80%93Binet_formula -/

theorem Matrix.det_mul' (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin n) (Fin m) R) :
  det (A * B) = ∑ f : Fin m ↪o Fin n, det (A.submatrix id f) * det (B.submatrix f id) := by
-- real proof starts here
  sorry

example : True := by
  have := Matrix.det_mul' !![1, 2, (3 : ℤ)] !![1; 2; 3]
  simp [Fin.sum_univ_succ] at this

/-- `List.sublistsLen`, but using `List.Vector`. -/
def List.subvectorsLen {α} (l : List α) (n : ℕ) : List (List.Vector α n) :=
  l.sublistsLen n |>.attach.map fun x => ⟨x.1, by have := x.prop; aesop⟩

#eval List.subvectorsLen ["A", "B", "C"] 2


/-- A version of Cauchy-Binet stated using lists and `Fin n`. -/
theorem Matrix.det_mul_fin (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin n) (Fin m) R) :
    det (A * B) =
      ((List.finRange n |>.subvectorsLen m).map fun l =>
        det (A.submatrix id l.get) * det (B.submatrix l.get id)).sum := by
  -- From wikipedia: it suffices to consider matrices with a single `1` in each row / column.
  -- This should work with any formulation of the statement.
  suffices ∀ iA iB : Fin m → Fin n,
      let A := Matrix.of (fun i j => Pi.single (iA i) (1 : R) j)
      let B := (Matrix.of (fun i j => Pi.single (iB i) (1 : R) j))ᵀ
      det (A * B) =
        ((List.finRange n |>.subvectorsLen m).map fun l =>
          det (A.submatrix id l.get) * det (B.submatrix l.get id)).sum by
    -- The LHS is multilinear
    let lhs : MultilinearMap R (fun _ : Fin m ⊕ Fin m => Fin n → R) R := by
      sorry
    have lhs_eq (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin n) (Fin m) R) :
        det (A * B) = lhs (A ⊕ᵥ Bᵀ) := by
      sorry -- this will be `rfl` if the above sorry is filled correctly
    -- The RHS is multilinear
    let rhs :  MultilinearMap R (fun _ : Fin m ⊕ Fin m => Fin n → R) R :=
      sorry
    have rhs_eq (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin n) (Fin m) R) :
        ((List.finRange n |>.subvectorsLen m).map fun l =>
          det (A.submatrix id l.get) * det (B.submatrix l.get id)).sum = rhs (A ⊕ᵥ Bᵀ) := by
      sorry -- this will be `rfl` if the above sorry is filled correctly
    suffices lhs = rhs by rw [lhs_eq, rhs_eq, this]
    -- it suffices to consider A with a `1` in each row and B with a `1` in each column
    ext i -- the index of the `1` entry in each column
    revert i
    rw [Equiv.sumArrowEquivProdArrow _ _ _ |>.symm.surjective.forall]
    intro ⟨iA, iB⟩
    simp [lhs_eq, rhs_eq, Equiv.sumArrowEquivProdArrow] at this ⊢
    convert this iA iB using 2 <;> ext (i | i) j <;> simp
  intro iA iB
  simp [Matrix.submatrix]
  sorry
