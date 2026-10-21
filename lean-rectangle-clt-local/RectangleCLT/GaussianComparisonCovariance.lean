import RectangleCLT.ProxyCovariance
import RectangleCLT.LocalCovariance
import Mathlib.Tactic.Positivity

/-!
# Covariance geometry for local Gaussian comparison

These elementary facts concern the actual interpolation of two covariance
matrices. In particular, the small discrepancy condition is imposed only
relative to the gap of the comparison covariance.
-/

open scoped BigOperators

namespace RectangleCLT

/-- The covariance along the two-Gaussian interpolation. -/
def gaussianComparisonCovariance {p : ℕ}
    (S T : Matrix (Fin p) (Fin p) ℝ) (t : ℝ) :
    Matrix (Fin p) (Fin p) ℝ :=
  (1 - t) • S + t • T

theorem gaussianComparisonCovariance_apply {p : ℕ}
    (S T : Matrix (Fin p) (Fin p) ℝ) (t : ℝ) (j k : Fin p) :
    gaussianComparisonCovariance S T t j k = (1 - t) * S j k + t * T j k := rfl

theorem gaussianComparisonCovariance_zero {p : ℕ}
    (S T : Matrix (Fin p) (Fin p) ℝ) :
    gaussianComparisonCovariance S T 0 = S := by
  funext j k
  rw [gaussianComparisonCovariance_apply]
  ring

theorem gaussianComparisonCovariance_one {p : ℕ}
    (S T : Matrix (Fin p) (Fin p) ℝ) :
    gaussianComparisonCovariance S T 1 = T := by
  funext j k
  rw [gaussianComparisonCovariance_apply]
  ring

theorem gaussianComparisonCovariance_unit_diagonal {p : ℕ}
    (S T : Matrix (Fin p) (Fin p) ℝ)
    (hS : ∀ j, S j j = 1) (hT : ∀ j, T j j = 1) (t : ℝ) :
    ∀ j, gaussianComparisonCovariance S T t j j = 1 := by
  intro j
  exact proxy_interpolated_unit_diagonal S T hS hT t j

/-- Each entry of the path stays within the endpoint discrepancy from the
comparison matrix. -/
theorem gaussianComparisonCovariance_entry_sub_le {p : ℕ}
    (S T : Matrix (Fin p) (Fin p) ℝ) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (j k : Fin p) :
    |gaussianComparisonCovariance S T t j k - T j k| ≤
      proxyCovarianceDiscrepancy S T := by
  have hfactor : gaussianComparisonCovariance S T t j k - T j k =
      (1 - t) * (S j k - T j k) := by
    rw [gaussianComparisonCovariance_apply]
    ring
  rw [hfactor, abs_mul, abs_of_nonneg (sub_nonneg.mpr ht1)]
  calc
    (1 - t) * |S j k - T j k| ≤ 1 * |S j k - T j k| :=
      mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    _ ≤ proxyCovarianceDiscrepancy S T := by
      simpa only [one_mul] using abs_entry_sub_le_proxyCovarianceDiscrepancy S T j k

/-- The whole covariance path loses at most the original entrywise
discrepancy from the comparison matrix's pairwise gap. -/
theorem gaussianComparisonCovariance_pair_bound {p : ℕ}
    (S T : Matrix (Fin p) (Fin p) ℝ) (c : ℝ)
    (hT : ∀ j k, j ≠ k → |T j k| ≤ 1 - c)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∀ j k, j ≠ k → |gaussianComparisonCovariance S T t j k| ≤
      1 - (c - proxyCovarianceDiscrepancy S T) := by
  intro j k hjk
  calc
    |gaussianComparisonCovariance S T t j k| =
        |(gaussianComparisonCovariance S T t j k - T j k) + T j k| := by
      congr 1 <;> ring
    _ ≤ |gaussianComparisonCovariance S T t j k - T j k| + |T j k| := abs_add _ _
    _ ≤ proxyCovarianceDiscrepancy S T + (1 - c) :=
      add_le_add (gaussianComparisonCovariance_entry_sub_le S T ht0 ht1 j k)
        (hT j k hjk)
    _ = 1 - (c - proxyCovarianceDiscrepancy S T) := by ring

theorem gaussianComparisonCovariance_pair_bound_half {p : ℕ}
    (S T : Matrix (Fin p) (Fin p) ℝ) (c : ℝ)
    (hT : ∀ j k, j ≠ k → |T j k| ≤ 1 - c)
    (hsmall : proxyCovarianceDiscrepancy S T ≤ c / 2)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∀ j k, j ≠ k → |gaussianComparisonCovariance S T t j k| ≤ 1 - c / 2 := by
  intro j k hjk
  have h := gaussianComparisonCovariance_pair_bound S T c hT ht0 ht1 j k hjk
  linarith

/-- A pointwise off-diagonal bound controls the actual finite-maximum gap. -/
theorem gaussianComparison_pairGap_lower {p : ℕ}
    (Q : Matrix (Fin p) (Fin p) ℝ) {c : ℝ} (hc1 : c ≤ 1)
    (hQ : ∀ j k, j ≠ k → |Q j k| ≤ 1 - c) :
    c ≤ pairGap Q := by
  have hmax : maxOffDiagonal Q ≤ 1 - c := by
    apply (Finset.fold_max_le _).mpr
    refine ⟨by linarith, ?_⟩
    intro jk _
    by_cases hjk : jk.1 = jk.2
    · simp only [hjk, ↓reduceIte]
      linarith
    · simpa only [hjk, ↓reduceIte] using hQ jk.1 jk.2 hjk
  unfold pairGap
  linarith

/-- The perturbation bound in terms of the genuine covariance parameter. -/
theorem gaussianComparisonCovariance_pairGap_ge {p : ℕ}
    (S T : Matrix (Fin p) (Fin p) ℝ) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    pairGap T - proxyCovarianceDiscrepancy S T ≤
      pairGap (gaussianComparisonCovariance S T t) := by
  apply gaussianComparison_pairGap_lower
  · linarith [pairGap_le_one T, proxyCovarianceDiscrepancy_nonneg S T]
  · exact gaussianComparisonCovariance_pair_bound S T (pairGap T)
      (abs_offDiagonal_le T) ht0 ht1

theorem gaussianComparisonCovariance_pairGap_ge_half {p : ℕ}
    (S T : Matrix (Fin p) (Fin p) ℝ)
    (hsmall : proxyCovarianceDiscrepancy S T ≤ pairGap T / 2)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    pairGap T / 2 ≤ pairGap (gaussianComparisonCovariance S T t) := by
  have h := gaussianComparisonCovariance_pairGap_ge S T ht0 ht1
  linarith

theorem gaussianComparisonCovariance_posSemidef {p : ℕ}
    {S T : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosSemidef) (hT : T.PosSemidef)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (gaussianComparisonCovariance S T t).PosSemidef := by
  constructor
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    ext j k
    simp only [Matrix.transpose_apply, gaussianComparisonCovariance_apply]
    rw [matrix_symmetric_of_posSemidef hS k j, matrix_symmetric_of_posSemidef hT k j]
  · intro v
    have heq : matrixQuadratic (gaussianComparisonCovariance S T t) v =
        (1 - t) * matrixQuadratic S v + t * matrixQuadratic T v := by
      simp only [matrixQuadratic, gaussianComparisonCovariance_apply,
        mul_add, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;>
        apply Finset.sum_congr rfl <;> intro k _ <;> ring
    have hh : 0 ≤ matrixQuadratic (gaussianComparisonCovariance S T t) v := by
      rw [heq]
      exact add_nonneg
        (mul_nonneg (sub_nonneg.mpr ht1) (matrixQuadratic_nonneg_of_posSemidef hS v))
        (mul_nonneg ht0 (matrixQuadratic_nonneg_of_posSemidef hT v))
    simpa [matrixQuadratic, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc] using hh

theorem gaussianComparison_factor_exists {p : ℕ}
    {Q : Matrix (Fin p) (Fin p) ℝ} (hQ : Q.PosSemidef) :
    ∃ A : Matrix (Fin p) (Fin p) ℝ, A * A.transpose = Q := by
  refine ⟨hQ.sqrt, ?_⟩
  have hsymmetric : hQ.sqrt.transpose = hQ.sqrt := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hQ.posSemidef_sqrt.isHermitian
  rw [hsymmetric]
  exact hQ.sqrt_mul_self

end RectangleCLT
