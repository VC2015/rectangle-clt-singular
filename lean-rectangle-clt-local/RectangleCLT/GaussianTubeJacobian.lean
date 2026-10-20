import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.Ring

/-! Exact finite-dimensional Jacobian determinant for the augmented Gaussian
normal map. The identity holds also for degenerate normal families. -/

open scoped BigOperators

namespace RectangleCLT

noncomputable section

/-- The derivative matrix in ambient coordinates followed by face coordinates. -/
def gaussianTubeJacobian {p q : ℕ}
    (N : Matrix (Fin p) (Fin q) ℝ) (d : Fin q → ℝ) :
    Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℝ :=
  Matrix.fromBlocks 1 N ((Matrix.diagonal d) * N.transpose) 0

/-- Schur complementation produces exactly the Gram determinant, with one
face-coordinate scaling factor per active face. -/
theorem gaussianTubeJacobian_det {p q : ℕ}
    (N : Matrix (Fin p) (Fin q) ℝ) (d : Fin q → ℝ) :
    (gaussianTubeJacobian N d).det =
      (-1 : ℝ) ^ q * (∏ i, d i) * (N.transpose * N).det := by
  unfold gaussianTubeJacobian
  rw [Matrix.det_fromBlocks_one₁₁, zero_sub, Matrix.det_neg,
    Matrix.mul_assoc, Matrix.det_mul, Matrix.det_diagonal]
  simp only [Fintype.card_fin]
  ring

/-- Absolute Jacobian for nonnegative face scalings and nonnegative Gram
determinant. No nonsingularity is required by this algebraic formula. -/
theorem gaussianTubeJacobian_abs_det {p q : ℕ}
    (N : Matrix (Fin p) (Fin q) ℝ) (d : Fin q → ℝ)
    (hd : ∀ i, 0 ≤ d i) (hgram : 0 ≤ (N.transpose * N).det) :
    |(gaussianTubeJacobian N d).det| =
      (∏ i, d i) * (N.transpose * N).det := by
  rw [gaussianTubeJacobian_det, abs_mul, abs_mul, abs_pow, abs_neg,
    abs_one, one_pow, one_mul,
    abs_of_nonneg (Finset.prod_nonneg (fun i _ => hd i)), abs_of_nonneg hgram]

/-- Exponential face coordinates have the expected positive Jacobian factor. -/
theorem gaussianTubeJacobian_abs_det_exp {p q : ℕ}
    (N : Matrix (Fin p) (Fin q) ℝ) (E : Fin q → ℝ) (h : ℝ)
    (hE : ∀ i, 0 ≤ E i) (hh : 0 < h)
    (hgram : 0 ≤ (N.transpose * N).det) :
    |(gaussianTubeJacobian N (fun i => E i / h)).det| =
      ((∏ i, E i) / h ^ q) * (N.transpose * N).det := by
  rw [gaussianTubeJacobian_abs_det N _ (fun i => div_nonneg (hE i) hh.le) hgram,
    Finset.prod_div_distrib]
  simp

end

end RectangleCLT
