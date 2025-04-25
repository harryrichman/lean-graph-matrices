import Mathlib

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
