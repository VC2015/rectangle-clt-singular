import RectangleCLT.GaussianComparisonHessian
import RectangleCLT.GaussianSelectorFaceMoments
import RectangleCLT.GaussianDerivativeScaling
import RectangleCLT.GaussianFourthVarianceBounds

/-! Second-order Gaussian face moments averaged over the actual normalized
Bernoulli-retained observations. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.FaceSmoother
noncomputable section
open GaussianTube

variable {p : ℕ} (s : FaceSmoother p)

theorem mixedSecondDerivativeF_scaleDown (a : ℝ) (ha : 0 < a) (x : Vector p)
    (j k : Fin p) :
    s.mixedSecondDerivativeF x j k =
      (s.scaleDown a ha).mixedSecondDerivativeF (a⁻¹ • x) j k / a ^ 2 := by
  rw [s.mixedSecondDerivativeF_eq, (s.scaleDown a ha).mixedSecondDerivativeF_eq,
    F_scaleDown, weights_scaleDown, scaleDown_bandwidth]
  field_simp [ne_of_gt ha, ne_of_gt s.bandwidth_pos]
  ring

theorem convolutionSecondDerivative_gaussian_scaleDown
    (a : ℝ) (ha : 0 < a) (A : Matrix (Fin p) (Fin p) ℝ)
    (x : Vector p) (j k : Fin p) :
    s.convolutionSecondDerivative (gaussianLaw (a • A)) x j k =
      (s.scaleDown a ha).convolutionSecondDerivative (gaussianLaw A) (a⁻¹ • x) j k / a ^ 2 := by
  rw [s.convolutionSecondDerivative_eq_standardGaussian,
    (s.scaleDown a ha).convolutionSecondDerivative_eq_standardGaussian, ← integral_div]
  apply integral_congr_ae
  exact ae_of_all _ (fun z => by
    rw [s.mixedSecondDerivativeF_scaleDown a ha,
      Matrix.smul_mulVec_assoc, smul_add, smul_smul,
      inv_mul_cancel₀ (ne_of_gt ha), one_smul])

theorem sum_abs_convolutionSecondDerivative_gaussian_scaleDown
    (a : ℝ) (ha : 0 < a) (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) :
    (∑ j, ∑ k, |s.convolutionSecondDerivative (gaussianLaw (a • A)) x j k|) =
      (∑ j, ∑ k, |(s.scaleDown a ha).convolutionSecondDerivative
        (gaussianLaw A) (a⁻¹ • x) j k|) / a ^ 2 := by
  simp_rw [s.convolutionSecondDerivative_gaussian_scaleDown a ha, abs_div,
    abs_of_nonneg (sq_nonneg a), ← Finset.sum_div]

theorem gaussianFaceMomentSum_div_eq_orderedFaceMoments
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (q k : ℕ) :
    s.gaussianFaceMomentSum A x q k / s.bandwidth ^ q =
      ∑ T : OrderedFaceTuples s.faces q, faceMoment T.val s A x k := by
  unfold gaussianFaceMomentSum
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro T _
  rw [s.faceMoment_eq_gaussianSoftFaceMoment]
  ring

theorem sum_abs_convolutionSecondDerivative_le_faceMoments (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p)
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose)) :
    (∑ j, ∑ k, |s.convolutionSecondDerivative (gaussianLaw A) x j k|) ≤
      (1 / pairGap (A * A.transpose)) *
        ((∑ T : OrderedFaceTuples s.faces 1, faceMoment T.val s A x 1) +
          4 * ∑ T : OrderedFaceTuples s.faces 2, faceMoment T.val s A x 0) := by
  rw [← s.gaussianFaceMomentSum_div_eq_orderedFaceMoments A x 1 1,
    ← s.gaussianFaceMomentSum_div_eq_orderedFaceMoments A x 2 0]
  convert s.sum_abs_convolutionSecondDerivative_le_det_moments hp A x hdiag hc using 1
  ring

private theorem second_active_gram_isUnit {q : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (hq0 : 0 < q) (hq : q ≤ 2)
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose)) (T : CompatibleFaceSets s.faces q) :
    IsUnit ((normalMatrix (compatibleSetTuple T) A).transpose *
      normalMatrix (compatibleSetTuple T) A).det := by
  rw [normalMatrix_gram]
  have hsym : ∀ j k, (A * A.transpose) j k = (A * A.transpose) k j := by
    intro j k
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  have hqcases : q = 1 ∨ q = 2 := by omega
  rcases hqcases with rfl | rfl
  · rw [Matrix.det_fin_one, (compatibleSetTuple T).gram_diagonal hdiag 0]
    exact isUnit_one
  · exact isUnit_iff_ne_zero.mpr (ne_of_gt (hc.trans_le
      ((compatibleSetTuple T).gram_two_det_ge_pairGap hsym hdiag hc.le)))

/-- Localized second-order face moments for a bounded independent shift.
The displayed constants retain the exact face order and polynomial degree. -/
theorem sum_ordered_second_shiftedFaceMoment_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n q : ℕ} {ξ : Fin n → Ω → Vector p} {η v : ℝ}
    (h : BoundedIndependentHypotheses μ ξ η) (hp : 1 ≤ p) (hv : 0 < v)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = v)
    (A : Matrix (Fin p) (Fin p) ℝ) (hq0 : 0 < q) (hq : q ≤ 2)
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose)) (k : ℕ) :
    (∑ T : OrderedFaceTuples s.faces q, shiftedFaceMoment μ T.val s A (sumVector ξ) k) ≤
      (2 : ℝ) ^ k * 1073741824 * (q : ℝ) ^ q *
        (Real.sqrt (dimensionLog p)) ^ (q + k) *
        Real.exp (8 + (4 * (k + 1 : ℝ)) ^ 2 / 2) *
        (1 + η * Real.sqrt (dimensionLog p)) / Real.sqrt v := by
  rw [sum_ordered_shiftedFaceMoment_eq_factorial]
  have hh := sum_shiftedFaceMoment_le h hp hv hunit s A
    (by norm_num : (0 : ℝ) < 1) hdiag hq0 (hq.trans (by omega))
    (s.second_active_gram_isUnit A hq0 hq hdiag hc) k
  simpa only [Real.sqrt_one, one_pow, mul_one] using hh

theorem integral_normalizedThinnedSecondFaceMoments_le
    {Ω : Type*} [MeasurableSpace Ω] {n q k : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (hq0 : 0 < q) (hq : q ≤ 2)
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose)) :
    (∫ b, ∑ T : OrderedFaceTuples s.faces q,
      faceMoment T.val s A (normalizedThinnedShift t b) k ∂bernoulliArrayLaw μ ξ t) ≤
      (2 : ℝ) ^ k * 1073741824 * (q : ℝ) ^ q *
        (Real.sqrt (dimensionLog p)) ^ (q + k) *
        Real.exp (8 + (4 * (k + 1 : ℝ)) ^ 2 / 2) *
        (1 + (2 * δ / Real.sqrt t) * Real.sqrt (dimensionLog p)) /
          Real.sqrt ((1 - t) / t) := by
  letI : IsProbabilityMeasure (bernoulliArrayLaw μ ξ t) :=
    bernoulliArrayLaw_isProbability μ ξ h.measurable t ht.le ht1.le
  rw [integral_ordered_faceMoment_eq_shifted (bernoulliArrayLaw μ ξ t) s A (normalizedThinnedShift t)
    (measurable_const.smul (measurable_arraySum p n)) hp q k]
  have hh := s.sum_ordered_second_shiftedFaceMoment_le
    (h.normalized_thinned t ht ht1.le) hp (div_pos (sub_pos.mpr ht1) ht)
    (h.normalized_thinned_sum_unit_diagonal hunit t ht ht1.le)
    A hq0 hq hdiag hc k
  rw [sumVector_normalizedThinned] at hh
  exact hh

/-- The actual normalized expected Hessian, under the true retained-array
law. The independent Gaussian proxy enters only through its pairwise gap. -/
theorem integral_sum_abs_second_normalizedThinned_le
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose)) :
    (∫ b, ∑ j, ∑ k, |s.convolutionSecondDerivative (gaussianLaw A)
      (normalizedThinnedShift t b) j k| ∂bernoulliArrayLaw μ ξ t) ≤
      gaussianSecondConstant * 1073741824 * dimensionLog p / pairGap (A * A.transpose) *
        ((1 + (2 * δ / Real.sqrt t) * Real.sqrt (dimensionLog p)) /
          Real.sqrt ((1 - t) / t)) := by
  letI := bernoulliArrayLaw_isProbability μ ξ h.measurable t ht.le ht1.le
  let ν := bernoulliArrayLaw μ ξ t
  let F (q k : ℕ) (b : Fin n → Vector p) :=
    ∑ T : OrderedFaceTuples s.faces q, faceMoment T.val s A (normalizedThinnedShift t b) k
  have hi (q k : ℕ) : Integrable (F q k) ν :=
    integrable_normalizedThinnedFaceMoments μ ξ h.measurable s A hp ht.le ht1.le q k
  have hJ : Integrable (fun b => (1 / pairGap (A * A.transpose)) * (F 1 1 b + 4 * F 2 0 b)) ν :=
    ((hi 1 1).add ((hi 2 0).const_mul 4)).const_mul _
  have hb := integral_mono_of_nonneg
    (ae_of_all ν (fun b => Finset.sum_nonneg (fun _ _ =>
      Finset.sum_nonneg (fun _ _ => abs_nonneg _)))) hJ
    (ae_of_all ν (fun b => s.sum_abs_convolutionSecondDerivative_le_faceMoments hp A
      (normalizedThinnedShift t b) hdiag hc))
  have h₁ := s.integral_normalizedThinnedSecondFaceMoments_le (q := 1) (k := 1)
    h hp hunit A ht ht1 (by omega) (by omega) hdiag hc
  have h₂ := s.integral_normalizedThinnedSecondFaceMoments_le (q := 2) (k := 0)
    h hp hunit A ht ht1 (by omega) (by omega) hdiag hc
  have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  norm_num only [Nat.cast_ofNat, Nat.cast_one, pow_zero, pow_one, one_mul, mul_one,
    Nat.reduceAdd, Nat.cast_add, Real.sq_sqrt hL] at h₁ h₂
  apply hb.trans
  rw [integral_const_mul, integral_add (hi 1 1) ((hi 2 0).const_mul 4), integral_const_mul]
  have hm := mul_le_mul_of_nonneg_left
    (add_le_add h₁ (mul_le_mul_of_nonneg_left h₂ (by norm_num : (0 : ℝ) ≤ 4)))
    (div_nonneg zero_le_one hc.le)
  convert hm using 1
  unfold gaussianSecondConstant
  ring

theorem integral_sum_abs_second_bernoulli_scaling
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) {t : ℝ} (ht : 0 < t) :
    (∫ b, ∑ j, ∑ k, |s.convolutionSecondDerivative (gaussianLaw (Real.sqrt t • A))
      (arraySum b) j k| ∂bernoulliArrayLaw μ ξ t) =
      (∫ b, ∑ j, ∑ k,
        |(s.scaleDown (Real.sqrt t) (Real.sqrt_pos.mpr ht)).convolutionSecondDerivative
          (gaussianLaw A) (normalizedThinnedShift t b) j k| ∂bernoulliArrayLaw μ ξ t) / t := by
  simp_rw [s.sum_abs_convolutionSecondDerivative_gaussian_scaleDown (Real.sqrt t)
    (Real.sqrt_pos.mpr ht)]
  rw [integral_div, Real.sq_sqrt ht.le]
  rfl

theorem integral_sum_abs_second_bernoulli_localized_le
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose)) :
    (∫ b, ∑ j, ∑ k, |s.convolutionSecondDerivative (gaussianLaw (Real.sqrt t • A))
      (arraySum b) j k| ∂bernoulliArrayLaw μ ξ t) ≤
      gaussianSecondConstant * 1073741824 * dimensionLog p / pairGap (A * A.transpose) *
        (((1 + (2 * δ / Real.sqrt t) * Real.sqrt (dimensionLog p)) /
          Real.sqrt ((1 - t) / t)) / t) := by
  rw [s.integral_sum_abs_second_bernoulli_scaling μ ξ A ht]
  have hh := div_le_div_of_nonneg_right
    ((s.scaleDown (Real.sqrt t) (Real.sqrt_pos.mpr ht)).integral_sum_abs_second_normalizedThinned_le
      h hp hunit A ht ht1 hdiag hc) ht.le
  convert hh using 1
  ring

def gaussianSecondAverageConstant : ℝ := 8 * 1073741824 * gaussianSecondConstant

theorem gaussianSecondAverageConstant_pos : 0 < gaussianSecondAverageConstant := by
  unfold gaussianSecondAverageConstant
  exact mul_pos (by norm_num) gaussianSecondConstant_pos

/-- The localized large-time second derivative cap for the actual bounded
Bernoulli base and an independent Gaussian covariance proxy. -/
theorem integral_sum_abs_second_bernoulli_largeTime_le
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose)) (hband : 12 * δ ≤ s.bandwidth)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (hlarge : s.bandwidth ^ 2 * dimensionLog p ≤ t) :
    (∫ b, ∑ j, ∑ k, |s.convolutionSecondDerivative (gaussianLaw (Real.sqrt t • A))
      (arraySum b) j k| ∂bernoulliArrayLaw μ ξ t) ≤
      gaussianSecondAverageConstant * dimensionLog p /
        (pairGap (A * A.transpose) * Real.sqrt t) := by
  letI := bernoulliArrayLaw_isProbability μ ξ h.measurable t ht.le ht1.le
  have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hroot : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hδh : δ ≤ s.bandwidth := by linarith [h.delta_nonneg]
  have hnon : 0 ≤ gaussianSecondConstant * dimensionLog p / pairGap (A * A.transpose) :=
    div_nonneg (mul_nonneg gaussianSecondConstant_pos.le hL) hc.le
  by_cases hhalf : t ≤ 1 / 2
  · have htime : ((1 + (2 * δ / Real.sqrt t) * Real.sqrt (dimensionLog p)) /
        Real.sqrt ((1 - t) / t)) / t ≤ 8 / Real.sqrt t := by
      rw [normalized_localization_factor_eq ht ht1]
      have hh := div_le_div_of_nonneg_right
        (fourth_localization_factor_le h.delta_nonneg hδh hL hlarge hhalf) ht.le
      have heq : (3 * Real.sqrt 2 * Real.sqrt t) / t = 3 * Real.sqrt 2 / Real.sqrt t := by
        apply (div_eq_div_iff ht.ne' hroot.ne').mpr
        calc
          _ = (3 * Real.sqrt 2) * (Real.sqrt t) ^ 2 := by ring
          _ = _ := by rw [Real.sq_sqrt ht.le]
      apply (hh.trans_eq heq).trans
      apply div_le_div_of_nonneg_right _ hroot.le
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
        sq_nonneg (Real.sqrt 2 - 2)]
    have hrawnon : 0 ≤ gaussianSecondConstant * 1073741824 * dimensionLog p /
        pairGap (A * A.transpose) :=
      div_nonneg (mul_nonneg (mul_nonneg gaussianSecondConstant_pos.le (by norm_num)) hL) hc.le
    have hh := (s.integral_sum_abs_second_bernoulli_localized_le h hp hunit A ht ht1 hdiag hc).trans
      (mul_le_mul_of_nonneg_left htime hrawnon)
    convert hh using 1
    unfold gaussianSecondAverageConstant
    ring
  · rw [s.integral_sum_abs_second_bernoulli_scaling μ ξ A ht]
    let sn := s.scaleDown (Real.sqrt t) hroot
    have hb := integral_mono_of_nonneg
      (ae_of_all (bernoulliArrayLaw μ ξ t) (fun b => Finset.sum_nonneg (fun _ _ =>
        Finset.sum_nonneg (fun _ _ => abs_nonneg _))))
      (integrable_const (gaussianSecondConstant * dimensionLog p / pairGap (A * A.transpose)))
      (ae_of_all (bernoulliArrayLaw μ ξ t) (fun b =>
        sn.sum_abs_convolutionSecondDerivative_gaussian_le hp A (normalizedThinnedShift t b) hdiag hc))
    have hb' := div_le_div_of_nonneg_right hb ht.le
    simp only [integral_const, measureReal_univ_eq_one, one_smul] at hb'
    have htime : 1 / t ≤ 2 / Real.sqrt t := by
      apply (div_le_div_iff₀ ht hroot).mpr
      have hs : Real.sqrt t ≤ 1 := Real.sqrt_le_one.mpr ht1.le
      linarith [lt_of_not_ge hhalf]
    calc
      _ ≤ (gaussianSecondConstant * dimensionLog p / pairGap (A * A.transpose)) / t := hb'
      _ ≤ (gaussianSecondConstant * dimensionLog p / pairGap (A * A.transpose)) *
          (2 / Real.sqrt t) := by
        simpa only [mul_one, div_eq_mul_inv] using mul_le_mul_of_nonneg_left htime hnon
      _ ≤ (gaussianSecondConstant * dimensionLog p / pairGap (A * A.transpose)) *
          (8 * 1073741824 / Real.sqrt t) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (by norm_num) hroot.le) hnon
      _ = _ := by unfold gaussianSecondAverageConstant; ring

end
end RectangleCLT.FaceSmoother
