import RectangleCLTCompanion.SplitV4.SymmetricNuclearNorm

open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4

noncomputable section

/-- A quadratic bound on an arbitrary coefficient matrix controls its
trace pairing with a real symmetric matrix by the actual nuclear norm.
The coefficient itself need not be symmetric. -/
theorem abs_trace_mul_le_nuclear_of_quadratic {r : ℕ}
    (B M : Matrix (Fin r) (Fin r) ℝ) (hM : M.IsHermitian) {b : ℝ}
    (hb : ∀ z, |matrixQuadratic B z| ≤ b * vectorNormSq z) :
    |Matrix.trace (B * M)| ≤ b * symmetricNuclearNorm M := by
  let Q : Matrix (Fin r) (Fin r) ℝ := hM.eigenvectorUnitary
  obtain ⟨hQQ, hQtQ, hspec⟩ := spectral_orthogonal_identities M hM
  change Q.transpose * Q = 1 at hQtQ
  change M = Q * Matrix.diagonal hM.eigenvalues * Q.transpose at hspec
  have hcol (i : Fin r) : vectorNormSq (Q.transpose i) = 1 :=
    orthogonal_row_sq_sum Q.transpose (by simpa only [Matrix.transpose_transpose] using hQtQ) i
  conv_lhs => arg 1; rhs; rw [hspec]
  rw [trace_mul_orthogonal_diagonal_eq, symmetricNuclearNorm_eq_sum_abs_eigenvalues M hM,
    Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  have hbi := hb (Q.transpose i)
  rw [hcol, mul_one] at hbi
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_left hbi (abs_nonneg _)).trans_eq (mul_comm _ _)

end

end RectangleCLT.Companion.SplitV4
