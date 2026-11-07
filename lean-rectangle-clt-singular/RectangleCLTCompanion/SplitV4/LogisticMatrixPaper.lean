import RectangleCLTCompanion.SplitV4.LogisticMatrixRegularizedBound

open MeasureTheory Set
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4

noncomputable section

theorem weightedScore_standardGaussian_const (r : ℕ) (c : ℝ) :
    weightedScore (standardGaussian r) id (fun _ => c) = 0 := by
  ext j l
  change (∫ g : Vector r, (g j * g l - if j = l then 1 else 0) * c ∂standardGaussian r) = 0
  rw [integral_mul_const,
    integral_sub (standardGaussian_integrable_coordinate_product r j l) (integrable_const _),
    standardGaussian_integral_coordinate_product]
  simp

theorem logisticGaussianScore_zero_scale {m r k : ℕ} (u : Fin m → Vector r)
    (a : Vector m) (h : ℝ) (α : Fin k → Fin m) (x : Vector r) :
    logisticGaussianScore u a h 0 α x = 0 := by
  simp only [logisticGaussianScore, zero_smul, add_zero]
  exact weightedScore_standardGaussian_const r _

/-- The zero-scale edge is included. When the Gaussian scale vanishes,
the genuine centered Gaussian score is zero. -/
theorem logistic_matrix_estimate_nonneg_scale {m r : ℕ} (hm : 1 ≤ m)
    (μ : Measure (Vector r)) [IsProbabilityMeasure μ]
    (u : Fin m → Vector r) (a : Vector m) (hu : ∀ j, vectorNormSq (u j) = 1)
    (opposite : Fin m → Fin m) (hopp : ∀ j, u (opposite j) = -u j)
    {C δ L h σ : ℝ} (hC : 0 < C) (hδ : 0 ≤ δ) (hh : 0 < h) (hδh : δ ≤ h)
    (hσ : 0 ≤ σ) (hL : dimensionLog m ≤ 2 * L) (hscale : δ * Real.sqrt L ≤ σ)
    (hc : PolyhedralBaseConcentration μ u C δ L) (k : ℕ) (hk : 1 ≤ k) :
    (∫ x, ∑ α : Fin k → Fin m,
      symmetricNuclearNorm (logisticGaussianScore u a h σ α x) ∂μ) ≤
        logisticMatrixConstant ^ (k + 1) * C * (h * L * Real.sqrt L) := by
  rcases hσ.eq_or_lt with hσ | hσ
  · subst σ
    simp only [logisticGaussianScore_zero_scale, symmetricNuclearNorm_zero,
      Finset.sum_const_zero, integral_zero]
    have hLp : 0 ≤ L := by
      have hmL : 1 ≤ dimensionLog m := log_exp_mul_nat_ge_one hm
      linarith only [hmL, hL]
    exact mul_nonneg (mul_nonneg (pow_nonneg logisticMatrixConstant_pos.le _) hC.le)
      (mul_nonneg (mul_nonneg hh.le hLp) (Real.sqrt_nonneg L))
  · exact logistic_matrix_estimate hm μ u a hu opposite hopp hC hδ hh hδh hσ hL hscale hc k hk

theorem logisticMatrixConstant_ge_one : 1 ≤ logisticMatrixConstant := by
  unfold logisticMatrixConstant
  linarith [Real.exp_pos (13 / 2 : ℝ), averagedThresholdPaperConstant_pos]

theorem logistic_concentration_constant_absorption {C : ℝ} (hC : 0 ≤ C) (k : ℕ) :
    logisticMatrixConstant ^ (k + 1) * C ≤
      (logisticMatrixConstant * max 1 C) ^ (k + 1) := by
  have hM : (1 : ℝ) ≤ max 1 C := le_max_left _ _
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_left
    ((le_max_right (1 : ℝ) C).trans (by
      simpa only [pow_one] using pow_le_pow_right₀ hM (by omega : 1 ≤ k + 1)))
    (pow_nonneg logisticMatrixConstant_pos.le _)

/-- The fixed concentration constant is absorbed before all dimensions,
laws, face systems, thresholds and orders are quantified. -/
theorem exists_logistic_matrix_paper_constant (C₀ : ℝ) (hC₀ : 0 < C₀) :
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
  refine ⟨logisticMatrixConstant * max 1 C₀, ?_, ?_⟩
  · exact one_le_mul_of_one_le_of_one_le logisticMatrixConstant_ge_one (le_max_left _ _)
  · intro m r p hm hp hmp μ _ u a hu opposite hopp δ h σ hδ hh hδh hσ hscale hc k hk
    have hn := logistic_matrix_estimate_nonneg_scale hm μ u a hu opposite hopp hC₀ hδ hh hδh hσ
      (threshold_dimensionLog_faces_le hm hp hmp) hscale hc k hk
    exact hn.trans (mul_le_mul_of_nonneg_right (logistic_concentration_constant_absorption hC₀.le k)
      (mul_nonneg (mul_nonneg hh.le (zero_le_one.trans (log_exp_mul_nat_ge_one hp))) (Real.sqrt_nonneg _)))

end

end RectangleCLT.Companion.SplitV4
