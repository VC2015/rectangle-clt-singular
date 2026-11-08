import RectangleCLTCompanion.SplitV4.LogisticMatrixPaper
import RectangleCLTCompanion.SplitV4.Printed.MatrixSectorRegularized

/-! The printed B.4 matrix estimate with its analytic threshold input
supplied by the separately checked full-sector and radial-tail route.
Earlier endpoints and their proof values remain unchanged. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section
open SignedSurface

theorem sector_logistic_matrix_estimate_nonneg_scale {m r : ℕ} (hm : 1 ≤ m)
    (μ : Measure (Vector r)) [IsProbabilityMeasure μ]
    (u : Fin m → Vector r) (a : Vector m) (hu : ∀ j, vectorNormSq (u j) = 1)
    (opposite : Fin m → Fin m) (hopp : ∀ j, u (opposite j) = -u j)
    {C δ L h σ : ℝ} (hC : 0 < C) (hδ : 0 ≤ δ) (hh : 0 < h) (hδh : δ ≤ h)
    (hσ : 0 ≤ σ) (hL : dimensionLog m ≤ 2 * L) (hscale : δ * Real.sqrt L ≤ σ)
    (hc : PolyhedralBaseConcentration μ u C δ L) (k : ℕ) (hk : 1 ≤ k) :
    (∫ x, ∑ α : Fin k → Fin m,
      symmetricNuclearNorm (logisticGaussianScore u a h σ α x) ∂μ) ≤
        sectorLogisticMatrixConstant ^ (k + 1) * C * (h * L * Real.sqrt L) := by
  rcases hσ.eq_or_lt with hσ | hσ
  · subst σ
    simp only [logisticGaussianScore_zero_scale, symmetricNuclearNorm_zero,
      Finset.sum_const_zero, integral_zero]
    have hLp : 0 ≤ L := by
      have hmL : 1 ≤ dimensionLog m := log_exp_mul_nat_ge_one hm
      linarith only [hmL, hL]
    exact mul_nonneg (mul_nonneg (pow_nonneg sectorLogisticMatrixConstant_pos.le _) hC.le)
      (mul_nonneg (mul_nonneg hh.le hLp) (Real.sqrt_nonneg L))
  · exact sector_logistic_matrix_estimate_full_first hm μ u a hu opposite hopp hC hδ hh hδh hσ hL hscale hc k hk

theorem sectorLogisticMatrixConstant_ge_one : 1 ≤ sectorLogisticMatrixConstant := by
  unfold sectorLogisticMatrixConstant
  linarith [Real.exp_pos (13 / 2 : ℝ), sectorAveragedThresholdPaperConstant_pos]

theorem sector_logistic_concentration_constant_absorption {C : ℝ} (hC : 0 ≤ C) (k : ℕ) :
    sectorLogisticMatrixConstant ^ (k + 1) * C ≤
      (sectorLogisticMatrixConstant * max 1 C) ^ (k + 1) := by
  have hM : (1 : ℝ) ≤ max 1 C := le_max_left _ _
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_left
    ((le_max_right (1 : ℝ) C).trans (by
      simpa only [pow_one] using pow_le_pow_right₀ hM (by omega : 1 ≤ k + 1)))
    (pow_nonneg sectorLogisticMatrixConstant_pos.le _)

/-- The fixed concentration constant is absorbed before all dimensions,
laws, face systems, thresholds and orders are quantified. -/
theorem sector_exists_logistic_matrix_paper_constant (C₀ : ℝ) (hC₀ : 0 < C₀) :
    ∃ C₁ : ℝ, 1 ≤ C₁ ∧ ∀ (m r p : ℕ), 1 ≤ m → 1 ≤ p → m ≤ 2 * p →
      ∀ (μ : Measure (Vector r)) [IsProbabilityMeasure μ]
        (u : Fin m → Vector r) (a : Vector m),
      (∀ j, vectorNormSq (u j) = 1) →
      ∀ (opposite : Fin m → Fin m), (∀ j, u (opposite j) = -u j) →
      ∀ (δ h σ : ℝ), 0 ≤ δ → 0 < h → δ ≤ h → 0 ≤ σ →
      δ * Real.sqrt (dimensionLog p) ≤ σ →
      PolyhedralBaseConcentration μ u C₀ δ (dimensionLog p) →
      ∀ (k : ℕ), 1 ≤ k →
      (∫ x, ∑ α : Fin k → Fin m,
        symmetricNuclearNorm (logisticGaussianScore u a h σ α x) ∂μ) ≤
          C₁ ^ (k + 1) * (h * dimensionLog p * Real.sqrt (dimensionLog p)) := by
  refine ⟨sectorLogisticMatrixConstant * max 1 C₀, ?_, ?_⟩
  · exact one_le_mul_of_one_le_of_one_le sectorLogisticMatrixConstant_ge_one (le_max_left _ _)
  · intro m r p hm hp hmp μ _ u a hu opposite hopp δ h σ hδ hh hδh hσ hscale hc k hk
    have hn := sector_logistic_matrix_estimate_nonneg_scale hm μ u a hu opposite hopp hC₀ hδ hh hδh hσ
      (threshold_dimensionLog_faces_le hm hp hmp) hscale hc k hk
    exact hn.trans (mul_le_mul_of_nonneg_right (sector_logistic_concentration_constant_absorption hC₀.le k)
      (mul_nonneg (mul_nonneg hh.le (zero_le_one.trans (log_exp_mul_nat_ge_one hp))) (Real.sqrt_nonneg _)))


end
end RectangleCLT.Companion.SplitV4.Printed
