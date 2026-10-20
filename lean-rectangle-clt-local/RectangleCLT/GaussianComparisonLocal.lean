import RectangleCLT.GaussianComparisonCovariance
import RectangleCLT.GaussianComparisonInterpolation
import RectangleCLT.GaussianComparisonLaw
import RectangleCLT.GaussianComparisonHessian
import RectangleCLT.RectangleSmoothing
import RectangleCLT.InterpolationIntegration
import RectangleCLT.Optimization

/-!
# Local pair-gap Gaussian comparison

The covariance perturbation is measured entrywise. The pairwise gap is
required only for the comparison covariance; neither matrix must have full
rank, and no positive semidefinite ordering is assumed.
-/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT

namespace FaceSmoother

variable {p : ℕ} (s : FaceSmoother p)

theorem gaussianComparisonSecond_eq_convolution
    (A B C : Matrix (Fin p) (Fin p) ℝ) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hC : C * C.transpose = gaussianComparisonCovariance
      (A * A.transpose) (B * B.transpose) t) (j k : Fin p) :
    s.gaussianComparisonSecond A B t j k =
      s.convolutionSecondDerivative (gaussianLaw C) 0 j k := by
  have hcov : C * C.transpose =
      (Real.sqrt (1 - t)) ^ 2 • (A * A.transpose) +
        (Real.sqrt t) ^ 2 • (B * B.transpose) := by
    rw [Real.sq_sqrt (sub_nonneg.mpr ht1), Real.sq_sqrt ht0]
    exact hC
  have hmap := gaussianLaw_scaled_sum A B C (Real.sqrt (1 - t)) (Real.sqrt t) hcov
  rw [s.convolutionSecondDerivative_eq_integral, ← hmap,
    integral_map (measurable_gaussianScaledSum _ _).aemeasurable
      (((s.continuous_secondDerivative j k).comp
        (continuous_const.add continuous_id)).aestronglyMeasurable)]
  simp only [zero_add]
  rfl

/-- Uniform Hessian control along the actual two-Gaussian path. -/
theorem sum_abs_gaussianComparisonSecond_le (hp : 1 ≤ p)
    (A B : Matrix (Fin p) (Fin p) ℝ)
    (hA : ∀ j, (A * A.transpose) j j = 1)
    (hB : ∀ j, (B * B.transpose) j j = 1)
    (hc : 0 < pairGap (B * B.transpose))
    (hsmall : proxyCovarianceDiscrepancy (A * A.transpose) (B * B.transpose) ≤
      pairGap (B * B.transpose) / 2)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (∑ j, ∑ k, |s.gaussianComparisonSecond A B t j k|) ≤
      2 * gaussianSecondConstant * dimensionLog p / pairGap (B * B.transpose) := by
  have hS : (A * A.transpose).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose A
  have hT : (B * B.transpose).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose B
  obtain ⟨C, hC⟩ := gaussianComparison_factor_exists
    (gaussianComparisonCovariance_posSemidef hS hT ht0 ht1)
  have hdiag : ∀ j, (C * C.transpose) j j = 1 := by
    rw [hC]
    exact gaussianComparisonCovariance_unit_diagonal _ _ hA hB t
  have hgap : pairGap (B * B.transpose) / 2 ≤ pairGap (C * C.transpose) := by
    rw [hC]
    exact gaussianComparisonCovariance_pairGap_ge_half _ _ hsmall ht0 ht1
  have hcC : 0 < pairGap (C * C.transpose) := (by linarith : 0 <
    pairGap (B * B.transpose) / 2).trans_le hgap
  simp_rw [s.gaussianComparisonSecond_eq_convolution A B C ht0 ht1 hC]
  calc
    _ ≤ gaussianSecondConstant * dimensionLog p / pairGap (C * C.transpose) :=
      s.sum_abs_convolutionSecondDerivative_gaussian_le hp C 0 hdiag hcC
    _ ≤ gaussianSecondConstant * dimensionLog p / (pairGap (B * B.transpose) / 2) :=
      div_le_div_of_nonneg_left
        (mul_nonneg gaussianSecondConstant_pos.le
          (zero_le_one.trans (log_exp_mul_nat_ge_one hp))) (by linarith) hgap
    _ = _ := by field_simp [ne_of_gt hc] <;> ring

theorem abs_gaussianComparisonDerivative_le (hp : 1 ≤ p)
    (A B : Matrix (Fin p) (Fin p) ℝ)
    (hA : ∀ j, (A * A.transpose) j j = 1)
    (hB : ∀ j, (B * B.transpose) j j = 1)
    (hc : 0 < pairGap (B * B.transpose))
    (hsmall : proxyCovarianceDiscrepancy (A * A.transpose) (B * B.transpose) ≤
      pairGap (B * B.transpose) / 2)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |(1 / 2 : ℝ) * ∑ j, ∑ k,
      ((B * B.transpose) j k - (A * A.transpose) j k) *
        s.gaussianComparisonSecond A B t j k| ≤
      gaussianSecondConstant *
        proxyCovarianceDiscrepancy (A * A.transpose) (B * B.transpose) *
          dimensionLog p / pairGap (B * B.transpose) := by
  let Δ := proxyCovarianceDiscrepancy (A * A.transpose) (B * B.transpose)
  have hΔ : 0 ≤ Δ := proxyCovarianceDiscrepancy_nonneg _ _
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  calc
    _ ≤ (1 / 2 : ℝ) * (∑ j, ∑ k,
        |((B * B.transpose) j k - (A * A.transpose) j k) *
          s.gaussianComparisonSecond A B t j k|) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro j _
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (1 / 2 : ℝ) * (Δ * ∑ j, ∑ k, |s.gaussianComparisonSecond A B t j k|) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simp only [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      simpa only [abs_sub_comm] using
        abs_entry_sub_le_proxyCovarianceDiscrepancy
          (A * A.transpose) (B * B.transpose) j k
    _ ≤ (1 / 2 : ℝ) * (Δ *
        (2 * gaussianSecondConstant * dimensionLog p / pairGap (B * B.transpose))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (s.sum_abs_gaussianComparisonSecond_le hp A B hA hB hc hsmall ht0 ht1) hΔ)
        (by norm_num)
    _ = _ := by dsimp [Δ]; ring

/-- The smooth comparison bound is uniform in the smoother bandwidth. -/
theorem gaussianComparison_smoother_gap_le (hp : 1 ≤ p)
    (A B : Matrix (Fin p) (Fin p) ℝ)
    (hA : ∀ j, (A * A.transpose) j j = 1)
    (hB : ∀ j, (B * B.transpose) j j = 1)
    (hc : 0 < pairGap (B * B.transpose))
    (hsmall : proxyCovarianceDiscrepancy (A * A.transpose) (B * B.transpose) ≤
      pairGap (B * B.transpose) / 2) :
    |(∫ x, s.F x ∂gaussianLaw A) - (∫ y, s.F y ∂gaussianLaw B)| ≤
      gaussianSecondConstant *
        proxyCovarianceDiscrepancy (A * A.transpose) (B * B.transpose) *
          dimensionLog p / pairGap (B * B.transpose) := by
  have hh := abs_sub_le_integral_of_derivative_bound
    (s.continuous_gaussianComparisonExpectation A B).continuousOn
    (fun t ht => s.hasDerivAt_gaussianComparisonExpectation A B ht.1 ht.2)
    continuous_const.integrableOn_Icc
    (fun t ht => s.abs_gaussianComparisonDerivative_le hp A B hA hB hc hsmall ht.1.le ht.2.le)
  rw [s.gaussianComparisonExpectation_zero, s.gaussianComparisonExpectation_one] at hh
  simpa only [intervalIntegral.integral_const, sub_zero, one_smul, abs_sub_comm] using hh

end FaceSmoother

theorem gaussianComparison_closedBox_le_small {p : ℕ} (hp : 1 ≤ p)
    (A B : Matrix (Fin p) (Fin p) ℝ)
    (hA : ∀ j, (A * A.transpose) j j = 1)
    (hB : ∀ j, (B * B.transpose) j j = 1)
    (hc : 0 < pairGap (B * B.transpose))
    (hsmall : proxyCovarianceDiscrepancy (A * A.transpose) (B * B.transpose) ≤
      pairGap (B * B.transpose) / 2) (lo hi : Vector p) :
    |(gaussianLaw A).real (Rect.closedBox lo hi).carrier -
      (gaussianLaw B).real (Rect.closedBox lo hi).carrier| ≤
      FaceSmoother.gaussianSecondConstant *
        proxyCovarianceDiscrepancy (A * A.transpose) (B * B.transpose) *
          dimensionLog p / pairGap (B * B.transpose) := by
  have hgap : pairGap (B * B.transpose) / 2 ≤ pairGap (A * A.transpose) := by
    simpa only [gaussianComparisonCovariance_zero] using
      gaussianComparisonCovariance_pairGap_ge_half
        (A * A.transpose) (B * B.transpose) hsmall
        (t := 0) (by norm_num) (by norm_num)
  have hcA : 0 < pairGap (A * A.transpose) := (by linarith : 0 <
    pairGap (B * B.transpose) / 2).trans_le hgap
  have hL : 0 < Real.sqrt (dimensionLog p) :=
    Real.sqrt_pos.mpr (lt_of_lt_of_le zero_lt_one (log_exp_mul_nat_ge_one hp))
  apply le_of_forall_pos_le_add
  intro ε hε
  let h := ε * pairGap (B * B.transpose) / (12 * Real.sqrt (dimensionLog p))
  have hh : 0 < h := by dsimp [h]; positivity
  let s := FaceSmoother.closedBox lo hi h hh
  have hprob := s.probability_gap_le_smoother_gap_add_kappa
    (gaussianLaw A) (gaussianLaw B) id measurable_id id measurable_id
  have hKA := s.gaussian_expected_kappa_le hp A 0 hA hcA
  have hKB := s.gaussian_expected_kappa_le hp B 0 hB hc
  simp only [add_zero] at hKA hKB
  have hKA' : (∫ x, s.kappa x ∂gaussianLaw A) ≤
      4 * h * Real.sqrt (dimensionLog p) / pairGap (B * B.transpose) := by
    apply hKA.trans
    change 2 * h * Real.sqrt (dimensionLog p) / pairGap (A * A.transpose) ≤ _
    calc
      _ ≤ 2 * h * Real.sqrt (dimensionLog p) /
          (pairGap (B * B.transpose) / 2) :=
        div_le_div_of_nonneg_left (by positivity) (by linarith) hgap
      _ = _ := by field_simp [ne_of_gt hc] <;> ring
  have hsmooth := s.gaussianComparison_smoother_gap_le hp A B hA hB hc hsmall
  have hbox : {x : Vector p | s.Inside x} = (Rect.closedBox lo hi).carrier := by
    ext x
    exact FaceSmoother.closedBox_Inside lo hi h hh x
  simp only [id_eq, hbox] at hprob
  have hεeq : 12 * h * Real.sqrt (dimensionLog p) /
      pairGap (B * B.transpose) = ε := by
    dsimp [h]
    field_simp [ne_of_gt hc, ne_of_gt hL]
    ring
  change (∫ x, s.kappa x ∂gaussianLaw B) ≤
    2 * h * Real.sqrt (dimensionLog p) / pairGap (B * B.transpose) at hKB
  linarith

/-- The small-discrepancy bound extends to every endpoint convention,
including unbounded or empty coordinate intervals. -/
theorem gaussianComparison_rectangle_le_small {p : ℕ} (hp : 1 ≤ p)
    (A B : Matrix (Fin p) (Fin p) ℝ)
    (hA : ∀ j, (A * A.transpose) j j = 1)
    (hB : ∀ j, (B * B.transpose) j j = 1)
    (hc : 0 < pairGap (B * B.transpose))
    (hsmall : proxyCovarianceDiscrepancy (A * A.transpose) (B * B.transpose) ≤
      pairGap (B * B.transpose) / 2) (R : Rect p) :
    |(gaussianLaw A).real R.carrier - (gaussianLaw B).real R.carrier| ≤
      FaceSmoother.gaussianSecondConstant *
        proxyCovarianceDiscrepancy (A * A.transpose) (B * B.transpose) *
          dimensionLog p / pairGap (B * B.transpose) :=
  rectangle_abs_probability_le_of_closedBox hp (gaussianLaw A) (gaussianLaw B)
    (gaussianComparison_closedBox_le_small hp A B hA hB hc hsmall) R

/-- An explicit universal constant for local pair-gap Gaussian comparison. -/
noncomputable def gaussianComparisonLocalConstant : ℝ := max 2 FaceSmoother.gaussianSecondConstant

theorem gaussianComparisonLocalConstant_ge_two : 2 ≤ gaussianComparisonLocalConstant :=
  le_max_left _ _

/-- Gaussian comparison using only the pairwise gap of the comparison
covariance. Both Gaussian vectors may be singular. -/
theorem gaussianComparisonLocal {p : ℕ} (hp : 1 ≤ p)
    (A B : Matrix (Fin p) (Fin p) ℝ)
    (hA : ∀ j, (A * A.transpose) j j = 1)
    (hB : ∀ j, (B * B.transpose) j j = 1)
    (hc : 0 < pairGap (B * B.transpose)) (R : Rect p) :
    |(gaussianLaw A).real R.carrier - (gaussianLaw B).real R.carrier| ≤
      gaussianComparisonLocalConstant * min 1
        (proxyCovarianceDiscrepancy (A * A.transpose) (B * B.transpose) *
          dimensionLog p / pairGap (B * B.transpose)) := by
  let Δ := proxyCovarianceDiscrepancy (A * A.transpose) (B * B.transpose)
  let c := pairGap (B * B.transpose)
  have hΔ : 0 ≤ Δ := proxyCovarianceDiscrepancy_nonneg _ _
  have hL : 1 ≤ dimensionLog p := log_exp_mul_nat_ge_one hp
  have hrate : 0 ≤ Δ * dimensionLog p / c := by positivity
  have hone : |(gaussianLaw A).real R.carrier - (gaussianLaw B).real R.carrier| ≤ 1 := by
    have hA0 : 0 ≤ (gaussianLaw A).real R.carrier := measureReal_nonneg
    have hA1 : (gaussianLaw A).real R.carrier ≤ 1 := measureReal_le_one
    have hB0 : 0 ≤ (gaussianLaw B).real R.carrier := measureReal_nonneg
    have hB1 : (gaussianLaw B).real R.carrier ≤ 1 := measureReal_le_one
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hlinear : |(gaussianLaw A).real R.carrier - (gaussianLaw B).real R.carrier| ≤
      gaussianComparisonLocalConstant * (Δ * dimensionLog p / c) := by
    by_cases hsmall : Δ ≤ c / 2
    · have hh := gaussianComparison_rectangle_le_small hp A B hA hB hc hsmall R
      have hC : FaceSmoother.gaussianSecondConstant ≤ gaussianComparisonLocalConstant :=
        le_max_right _ _
      calc
        _ ≤ FaceSmoother.gaussianSecondConstant * (Δ * dimensionLog p / c) := by
          convert hh using 1 <;> dsimp [Δ, c] <;> ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hC hrate
    · have hlarge : c / 2 ≤ Δ := le_of_lt (lt_of_not_ge hsmall)
      have hhalf : 1 ≤ 2 * (Δ * dimensionLog p / c) := by
        rw [← mul_div_assoc]
        apply (le_div_iff₀ hc).mpr
        have hprod : Δ ≤ Δ * dimensionLog p := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hL hΔ
        nlinarith
      exact hone.trans (hhalf.trans
        (mul_le_mul_of_nonneg_right gaussianComparisonLocalConstant_ge_two hrate))
  have hmin := le_max_mul_min_of_le_one hrate hone hlinear
  have hC1 : 1 ≤ gaussianComparisonLocalConstant :=
    le_trans (by norm_num) gaussianComparisonLocalConstant_ge_two
  simpa only [max_eq_right hC1, Δ, c] using hmin

end RectangleCLT
