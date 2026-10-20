import RectangleCLT.LocalStatement
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-! A rational covariance matrix separating the companion's positive-gap
scope from the local four-coordinate nondegeneracy of the completed CLT.
All statements concern explicit matrices; no probability model is assumed. -/

open scoped BigOperators Matrix ComplexOrder

namespace RectangleCLT.Companion.Examples

noncomputable section

/-- Three unit rows in a two-dimensional coordinate plane. -/
def gapFactor : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![1, 0, 0], ![0, 1, 0], ![3 / 5, 4 / 5, 0]]

/-- This correlation matrix has pair gap one fifth and a three-coordinate
null vector. In particular its local order-three and order-four minima vanish. -/
def gapMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![1, 0, 3 / 5], ![0, 1, 4 / 5], ![3 / 5, 4 / 5, 1]]

theorem gapFactor_gram : gapFactor * gapFactor.transpose = gapMatrix := by
  ext j k
  fin_cases j <;> fin_cases k <;>
    norm_num [gapFactor, gapMatrix, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ]

theorem gapMatrix_posSemidef : gapMatrix.PosSemidef := by
  rw [← gapFactor_gram]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_self_mul_conjTranspose gapFactor

theorem gapMatrix_unit_diagonal (j : Fin 3) : gapMatrix j j = 1 := by
  fin_cases j <;> norm_num [gapMatrix]

theorem gapMatrix_maxOffDiagonal : maxOffDiagonal gapMatrix = 4 / 5 := by
  apply le_antisymm
  · unfold maxOffDiagonal
    apply (Finset.fold_max_le _).mpr
    refine ⟨by norm_num, ?_⟩
    rintro ⟨j, k⟩ _
    fin_cases j <;> fin_cases k <;> norm_num [gapMatrix] <;>
      norm_num [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 5),
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4 / 5)]
  · unfold maxOffDiagonal
    apply (Finset.le_fold_max _).mpr
    refine Or.inr ⟨(1, 2), Finset.mem_univ _, ?_⟩
    rw [if_neg (by decide : (1 : Fin 3) ≠ 2)]
    change (4 / 5 : ℝ) ≤ |(4 / 5 : ℝ)|
    exact le_abs_self _

theorem gapMatrix_pairGap : pairGap gapMatrix = 1 / 5 := by
  unfold pairGap
  rw [gapMatrix_maxOffDiagonal]
  norm_num

theorem gapMatrix_pairGap_pos : 0 < pairGap gapMatrix := by
  rw [gapMatrix_pairGap]
  norm_num

def nullVector : Fin 3 → ℝ := ![-(3 / 5), -(4 / 5), 1]

theorem nullVector_ne_zero : nullVector ≠ 0 := by
  intro h
  have hh := congrFun h 2
  change (1 : ℝ) = 0 at hh
  norm_num at hh

theorem gapMatrix_nullVector : gapMatrix.mulVec nullVector = 0 := by
  funext j
  fin_cases j <;>
    norm_num [Matrix.mulVec, dotProduct, gapMatrix, nullVector, Fin.sum_univ_succ]

theorem nullVector_normSq : vectorNormSq nullVector = 2 := by
  norm_num [vectorNormSq, nullVector, Fin.sum_univ_succ]

theorem nullVector_quadratic : matrixQuadratic gapMatrix nullVector = 0 := by
  norm_num [matrixQuadratic, gapMatrix, nullVector, Fin.sum_univ_succ]

theorem nullVector_support_card_le_three : (coordinateSupport nullVector).card ≤ 3 := by
  simpa only [Fintype.card_fin] using Finset.card_le_univ (coordinateSupport nullVector)

/-- Any local Rayleigh family allowing all three coordinates sees this
nonzero null vector. Its infimum is exactly zero, rather than just nonpositive. -/
theorem gapMatrix_localEigenvalue_eq_zero (r : ℕ) (hr : 3 ≤ r) :
    localEigenvalue gapMatrix r = 0 := by
  have hquad := matrixQuadratic_nonneg_of_posSemidef gapMatrix_posSemidef
  have hnonneg := localEigenvalue_nonneg (by decide : 0 < 3) (by omega : 0 < r) hquad
  have hlower := localEigenvalue_lower hquad nullVector
    (nullVector_support_card_le_three.trans hr)
  rw [nullVector_normSq, nullVector_quadratic] at hlower
  linarith

theorem gapMatrix_a3 : a3 gapMatrix = 0 := gapMatrix_localEigenvalue_eq_zero 3 (by decide)

theorem gapMatrix_a4 : a4 gapMatrix = 0 := gapMatrix_localEigenvalue_eq_zero 4 (by decide)

/-- The existing local-covariance main theorem cannot be instantiated on this
matrix, although the companion's positive pair-gap requirement is satisfied. -/
theorem gapMatrix_not_localCovarianceHypotheses : ¬LocalCovarianceHypotheses gapMatrix := by
  intro h
  have hh := h.a4_pos
  rw [gapMatrix_a4] at hh
  exact (lt_irrefl 0) hh

/-- A fully explicit witness that a positive pairwise correlation gap does
not imply the local nondegeneracy required by the existing sharp CLT. -/
theorem positive_pairGap_not_local_nondegeneracy :
    ∃ Q : Matrix (Fin 3) (Fin 3) ℝ,
      Q.PosSemidef ∧ (∀ j, Q j j = 1) ∧ 0 < pairGap Q ∧
      a3 Q = 0 ∧ a4 Q = 0 ∧ ¬LocalCovarianceHypotheses Q :=
  ⟨gapMatrix, gapMatrix_posSemidef, gapMatrix_unit_diagonal, gapMatrix_pairGap_pos,
    gapMatrix_a3, gapMatrix_a4, gapMatrix_not_localCovarianceHypotheses⟩

end
end RectangleCLT.Companion.Examples
