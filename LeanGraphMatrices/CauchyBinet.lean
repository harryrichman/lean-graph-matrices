import Mathlib
import LeanGraphMatrices.ForMathlib

open scoped Matrix

variable {R : Type* } { m n : ℕ } [CommRing R]
variable {M N : Type} [Fintype M] [Fintype N] [DecidableEq M] [DecidableEq N] [LinearOrder M] [LinearOrder N]

/-- Cauchy-Binet, https://en.wikipedia.org/wiki/Cauchy%E2%80%93Binet_formula -/

theorem Matrix.det_mul' (A : Matrix M N R) (B : Matrix N M R) :
  det (A * B) = ∑ f : M ↪o N, det (A.submatrix id f) * det (B.submatrix f id) := by
  -- expand determinant in matrix entries as sum over permutations, on LHS
  rw [Matrix.det_apply (A * B)]
  -- simp_rw [Matrix.mul_apply, Finset.prod_sum, Finset.prod_mul_distrib]
  -- expand entries of matrix product A*B
  simp_rw [Matrix.mul_apply]
  -- interchange product (over Fin m) and sum (over Fin n)
  simp_rw [Finset.prod_sum]
  simp only [Finset.univ_pi_univ, Finset.prod_attach_univ]
  -- rewrite (prod_i a_i*b_i) as (prod_i a_i) * (prod_i b_i)
  simp_rw [Finset.prod_mul_distrib]
  -- simp_all only [Finset.univ_pi_univ, Finset.prod_attach_univ]
  -- expand determinats on RHS
  simp_rw [Matrix.det_apply]
  simp_all only [submatrix_apply, id_eq]
  -- exchange order of summation
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]

  -- calc
  --   ∑ x, Equiv.Perm.sign x • ∑ x_1, (∏ x_2, A (x x_2) (x_1 x_2 ⟨x_2, Finset.mem_univ x_2⟩.property)) * ∏ x, B (x_1 x ⟨x, Finset.mem_univ x⟩.property) x = ∑ x_1, ∑ σ, Equiv.Perm.sign σ • (∏ x_2, A (σ x_2) (x_1 x_2 ⟨x_2, Finset.mem_univ x_2⟩.property)) * ∏ x, B (x_1 x ⟨x, Finset.mem_univ x⟩.property) x := by rfl -- by simp?
  --   _ = 0 := by simp?
  --   _ = ∑ x, (∑ x_1, Equiv.Perm.sign x_1 • ∏ x_2, A (x_1 x_2) (x x_2)) * ∑ x_1, Equiv.Perm.sign x_1 • ∏ x_2, B (x (x_1 x_2)) x_2 := by rfl
  sorry

example {n m : ℕ} {f : (Fin m) → (Fin n) → ℤ} {c : ℤ} : ∑ (i : Fin m), c • (∑ (j : Fin n), f i j) = ∑ (i : Fin m), ∑ (j : Fin n), c • f i j := by
  simp_rw [Finset.smul_sum]

example {n m : ℕ} {f : (Fin m) → (Fin n) → ℤ} {c : ℤ} : ∑ (i : Fin m), (∑ (j : Fin n), f i j) • c = ∑ (i : Fin m), ∑ (j : Fin n), ((f i j) • c) := by
  simp_rw [Finset.sum_smul]

#check Finset.sum_smul
#check Finset.smul_sum


example : True := by
  have := Matrix.det_mul' !![1, 2, 3] (!![1; 2; 3] : Matrix _ _ ℤ)
  simp [Fin.sum_univ_succ] at this
  itauto

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
