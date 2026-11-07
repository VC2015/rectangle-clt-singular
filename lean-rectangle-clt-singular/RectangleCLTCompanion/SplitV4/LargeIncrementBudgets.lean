import RectangleCLTCompanion.SplitV4.PairedTailBudgets

/-! Actual coefficient budgets used by the large-increment comparison.
The matrix expectation retains its fluctuation and truncation bias, and
the drift budget retains the expected norm of the sum of large increments. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace RectangleCLT.Companion.SplitV4
noncomputable section

set_option autoImplicit false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {p n : ℕ} {h D : ℝ}

theorem matrixMaxEntryNorm_sub_le (M N S : Matrix (Fin p) (Fin p) ℝ) :
    matrixMaxEntryNorm (M - S) ≤ matrixMaxEntryNorm (M - N) + matrixMaxEntryNorm (N - S) := by
  change ‖(fun j k => M j k - S j k)‖ ≤
    ‖(fun j k => M j k - N j k)‖ + ‖(fun j k => N j k - S j k)‖
  have he : (fun j k => M j k - S j k) =
      (fun j k => M j k - N j k) + (fun j k => N j k - S j k) := by
    ext j k
    simp only [Pi.add_apply]
    ring
  rw [he]
  exact norm_add_le _ _

/-- The actual conditional covariance coefficient is controlled by the
independent matrix fluctuation and the exact discarded variance bias. -/
theorem expected_copyArrayTruncatedCovariance_sub_covariance_le
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (hind : iIndepFun ξ μ) (hp : 1 ≤ p) (hh : 0 < h) (hD : 0 ≤ D)
    (hi4 : ∀ i j, Integrable (fun ω => ξ i ω j ^ 4) μ)
    (hfourth : ∀ j, (∑ i, ∫ ω, ξ i ω j ^ 4 ∂μ) ≤ D)
    (hL2 : ∀ i j, MemLp (fun ω => ξ i ω j) (2 : ℝ≥0∞) μ)
    (hcenter : ∀ i j, (∫ ω, ξ i ω j ∂μ) = 0) :
    (∫ x, matrixMaxEntryNorm
      (copyArrayTruncatedCovariance μ ξ x h - covariance μ (sumVector ξ)) ∂μ) ≤
      (2 * matrixFluctuationConstant) *
        (Real.sqrt (D * dimensionLog p) + h ^ 2 * dimensionLog p) +
          pairedTailVariance μ ξ h / 2 := by
  have hfl := expected_copyArrayTruncatedCovariance_fluctuation_le
    ξ hξ hind hp hh hD hi4 hfourth
  have hb := meanTruncatedCovariance_bias_norm_le μ ξ hξ hind hL2 hcenter hh.le
  have hi := integrable_matrixMaxEntryNorm_copyArrayTruncatedCovariance_sub_const
    ξ hξ hind hh.le (covariance μ (sumVector ξ))
  have hif := integrable_matrixMaxEntryNorm_copyArrayTruncatedCovariance_sub_const
    ξ hξ hind hh.le (meanTruncatedCovariance μ ξ h)
  have hle := integral_mono hi (hif.add (integrable_const
      (matrixMaxEntryNorm (meanTruncatedCovariance μ ξ h - covariance μ (sumVector ξ)))))
    (fun x => matrixMaxEntryNorm_sub_le (copyArrayTruncatedCovariance μ ξ x h)
      (meanTruncatedCovariance μ ξ h) (covariance μ (sumVector ξ)))
  simp only [Pi.add_apply] at hle
  rw [integral_add hif (integrable_const _), integral_const] at hle
  simp only [measureReal_univ_eq_one, one_smul] at hle
  have hfl' : (∫ x, matrixMaxEntryNorm
      (copyArrayTruncatedCovariance μ ξ x h - meanTruncatedCovariance μ ξ h) ∂μ) ≤
      (2 * matrixFluctuationConstant) *
        (Real.sqrt (D * dimensionLog p) + h ^ 2 * dimensionLog p) := by
    simpa only [matrixMaxEntryNorm, Matrix.sub_apply, meanTruncatedCovariance] using hfl
  exact hle.trans (add_le_add hfl' hb)

end
end RectangleCLT.Companion.SplitV4
