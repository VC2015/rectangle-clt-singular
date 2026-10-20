import RectangleCLT.GaussianFourthSupScaling
import RectangleCLT.GaussianFourthSelectorBounds
import RectangleCLT.GaussianSelectorFaceMoments
import RectangleCLT.GaussianFourthVarianceBounds
import RectangleCLT.GaussianFourthSupMoments

/-! The actual large-time fourth Gaussian derivative bound along the
Bernoulli interpolation. Scalar normalization keeps singular Gaussian
factors admissible. -/

open MeasureTheory Set
open scoped BigOperators

universe u

namespace RectangleCLT

noncomputable section

def gaussianFourthMomentConstant : ℝ :=
  1364 * Real.exp 9 * GaussianTube.fourthFaceConstant

theorem gaussianFourthMomentConstant_pos : 0 < gaussianFourthMomentConstant := by
  unfold gaussianFourthMomentConstant
  exact mul_pos (mul_pos (by norm_num) (Real.exp_pos _)) GaussianTube.fourthFaceConstant_pos

/-- A fixed absolute constant covering both Gaussian time regimes and the
already proved short-scale cap. No constant depends on dimensions or data. -/
def gaussianFourthConstant : ℝ :=
  (75 * (Real.exp 2) ^ 5 * interpolationShortScaleConstant) +
    (4 + 3 * Real.sqrt 2 * 1073741824) * gaussianFourthMomentConstant + 1

theorem gaussianFourthConstant_ge_short :
    75 * (Real.exp 2) ^ 5 * interpolationShortScaleConstant ≤ gaussianFourthConstant := by
  unfold gaussianFourthConstant
  have hh : 0 ≤ (4 + 3 * Real.sqrt 2 * 1073741824) * gaussianFourthMomentConstant := by
    exact mul_nonneg (by positivity) gaussianFourthMomentConstant_pos.le
  linarith

theorem gaussianFourthConstant_pos : 0 < gaussianFourthConstant := by
  have hh : 0 ≤ (75 : ℝ) * (Real.exp 2) ^ 5 * interpolationShortScaleConstant := by
    unfold interpolationShortScaleConstant
    positivity
  unfold gaussianFourthConstant
  have hm := gaussianFourthMomentConstant_pos
  positivity

theorem gaussianFourthConstant_ge_global :
    4 * gaussianFourthMomentConstant ≤ gaussianFourthConstant := by
  have hh : 0 ≤ (75 : ℝ) * (Real.exp 2) ^ 5 * interpolationShortScaleConstant := by
    unfold interpolationShortScaleConstant
    positivity
  have hm := gaussianFourthMomentConstant_pos
  have hs := Real.sqrt_nonneg (2 : ℝ)
  unfold gaussianFourthConstant
  nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hs)
    (by norm_num : (0 : ℝ) ≤ 1073741824)) hm.le]

theorem gaussianFourthConstant_ge_local :
    (3 * Real.sqrt 2 * 1073741824) * gaussianFourthMomentConstant ≤ gaussianFourthConstant := by
  have hh : 0 ≤ (75 : ℝ) * (Real.exp 2) ^ 5 * interpolationShortScaleConstant := by
    unfold interpolationShortScaleConstant
    positivity
  have hm := gaussianFourthMomentConstant_pos
  unfold gaussianFourthConstant
  nlinarith

namespace FaceSmoother

variable {p : ℕ} (s : FaceSmoother p)

def normalizedFourthSupAverage
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) (δ t : ℝ) (ht : 0 < t) : ℝ :=
  ∫ b, ∑ j, ∑ k, ∑ l, ∑ m,
    (s.scaleDown (Real.sqrt t) (Real.sqrt_pos.mpr ht)).localConvolutionFourthSup
      A (4 * δ / Real.sqrt t) (GaussianTube.normalizedThinnedShift t b) 1 j k l m
    ∂bernoulliArrayLaw μ ξ t

theorem sharpFourthAverage_le_normalizedFourthSupAverage
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (A : Matrix (Fin p) (Fin p) ℝ) {δ t : ℝ} (hδ : 0 ≤ δ)
    (ht : 0 < t) (ht1 : t ≤ 1) :
    s.sharpFourthAverage μ ξ A δ t ≤
      s.normalizedFourthSupAverage μ ξ A δ t ht / t ^ 2 := by
  letI := bernoulliArrayLaw_isProbability μ ξ hξ t ht.le ht1
  have hr : 0 ≤ 4 * δ := mul_nonneg (by norm_num) hδ
  have hr' : 0 ≤ 4 * δ / Real.sqrt t := div_nonneg hr (Real.sqrt_nonneg t)
  let sn := s.scaleDown (Real.sqrt t) (Real.sqrt_pos.mpr ht)
  have hW : Measurable (GaussianTube.normalizedThinnedShift t (p := p) (n := n)) :=
    measurable_const.smul (measurable_arraySum p n)
  have hi := integrable_finset_sum Finset.univ (fun j _ =>
    integrable_finset_sum Finset.univ (fun k _ =>
      integrable_finset_sum Finset.univ (fun l _ =>
        integrable_finset_sum Finset.univ (fun m _ =>
          s.integrable_localConvolutionFourthSup_comp A hr t
            (bernoulliArrayLaw μ ξ t) arraySum (measurable_arraySum p n) j k l m))))
  have hn := integrable_finset_sum Finset.univ (fun j _ =>
    integrable_finset_sum Finset.univ (fun k _ =>
      integrable_finset_sum Finset.univ (fun l _ =>
        integrable_finset_sum Finset.univ (fun m _ =>
          sn.integrable_localConvolutionFourthSup_comp A hr' 1
            (bernoulliArrayLaw μ ξ t) (GaussianTube.normalizedThinnedShift t) hW j k l m))))
  rw [s.sharpFourthAverage_eq_integral_bernoulliArrayLaw μ ξ hξ A hδ ht.le ht1]
  change _ ≤ (∫ b, ∑ j, ∑ k, ∑ l, ∑ m, sn.localConvolutionFourthSup
    A (4 * δ / Real.sqrt t) (GaussianTube.normalizedThinnedShift t b) 1 j k l m
      ∂bernoulliArrayLaw μ ξ t) / t ^ 2
  rw [← integral_div]
  apply integral_mono hi (hn.div_const _)
  intro b
  exact s.sum_localConvolutionFourthSup_gaussian_sqrt_le A hr (arraySum b) ht

theorem normalizedFourthSupAverage_le_of_uniform
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ)
    {δ t : ℝ} (hδ : 0 ≤ δ) (ht : 0 < t) {K : ℝ}
    (hpoint : ∀ x, (∑ j, ∑ k, ∑ l, ∑ m,
      (s.scaleDown (Real.sqrt t) (Real.sqrt_pos.mpr ht)).localConvolutionFourthSup
        A (4 * δ / Real.sqrt t) x 1 j k l m) ≤ K)
    (hξ : ∀ i, Measurable (ξ i)) (ht1 : t ≤ 1) :
    s.normalizedFourthSupAverage μ ξ A δ t ht ≤ K := by
  letI := bernoulliArrayLaw_isProbability μ ξ hξ t ht.le ht1
  have hnon (b : Fin n → Vector p) : 0 ≤ ∑ j, ∑ k, ∑ l, ∑ m,
      (s.scaleDown (Real.sqrt t) (Real.sqrt_pos.mpr ht)).localConvolutionFourthSup
        A (4 * δ / Real.sqrt t) (GaussianTube.normalizedThinnedShift t b) 1 j k l m := by
    apply Finset.sum_nonneg
    intro j _
    apply Finset.sum_nonneg
    intro k _
    apply Finset.sum_nonneg
    intro l _
    apply Finset.sum_nonneg
    intro m _
    exact (s.scaleDown (Real.sqrt t) (Real.sqrt_pos.mpr ht)).localConvolutionFourthSup_nonneg
      A (div_nonneg (mul_nonneg (by norm_num) hδ) (Real.sqrt_nonneg t)) _ 1 j k l m
  have hb := integral_mono_of_nonneg (ae_of_all _ hnon)
    (integrable_const K : Integrable (fun _ : Fin n → Vector p => K)
      (bernoulliArrayLaw μ ξ t))
    (ae_of_all _ (fun b => hpoint (GaussianTube.normalizedThinnedShift t b)))
  simpa only [normalizedFourthSupAverage, integral_const, measureReal_univ_eq_one, one_smul] using hb

theorem normalizedFourthSupAverage_le_of_faceMoments
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → Vector p} {δ t a₄ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (ht : 0 < t) (ht1 : t < 1)
    (hQ : LocalCovarianceLower (A * A.transpose) 4 a₄) (ha₄ : 0 < a₄)
    (hA : ∀ j, (A * A.transpose) j j = 1) {K : ℝ} (hK : 0 ≤ K)
    (hpoint : ∀ x,
      let sn := s.scaleDown (Real.sqrt t) (Real.sqrt_pos.mpr ht)
      (∑ j, ∑ k, ∑ l, ∑ m, sn.localConvolutionFourthSup A (4 * δ / Real.sqrt t) x 1 j k l m) ≤
        K * (4 * (∑ S : GaussianTube.OrderedFaceTuples sn.faces 1,
          GaussianTube.faceMoment S.val sn A x 3) +
        40 * (∑ S : GaussianTube.OrderedFaceTuples sn.faces 2,
          GaussianTube.faceMoment S.val sn A x 2) +
        240 * (∑ S : GaussianTube.OrderedFaceTuples sn.faces 3,
          GaussianTube.faceMoment S.val sn A x 1) +
        1080 * (∑ S : GaussianTube.OrderedFaceTuples sn.faces 4,
          GaussianTube.faceMoment S.val sn A x 0))) :
    s.normalizedFourthSupAverage μ ξ A δ t ht ≤
      K * 1364 * (GaussianTube.fourthFaceConstant * 1073741824 * (dimensionLog p) ^ 2 *
        (1 + (2 * δ / Real.sqrt t) * Real.sqrt (dimensionLog p)) /
          Real.sqrt ((1 - t) / t)) := by
  letI := bernoulliArrayLaw_isProbability μ ξ h.measurable t ht.le ht1.le
  let ν := bernoulliArrayLaw μ ξ t
  let sn := s.scaleDown (Real.sqrt t) (Real.sqrt_pos.mpr ht)
  let W := GaussianTube.normalizedThinnedShift (p := p) (n := n) t
  let F (q k : ℕ) (b : Fin n → Vector p) :=
    ∑ S : GaussianTube.OrderedFaceTuples sn.faces q, GaussianTube.faceMoment S.val sn A (W b) k
  have hi (q k : ℕ) : Integrable (F q k) ν :=
    GaussianTube.integrable_normalizedThinnedFaceMoments μ ξ h.measurable sn A hp ht.le ht1.le q k
  have hbound (q k : ℕ) (hq0 : 0 < q) (hq : q ≤ 4) (hqk : q + k = 4) :=
    GaussianTube.integral_normalizedThinnedFaceMoments_le h hp hunit sn A ht ht1 hq0 hq hQ ha₄ hA hqk
  have hJ : Integrable (fun b => K * (4 * F 1 3 b + 40 * F 2 2 b +
      240 * F 3 1 b + 1080 * F 4 0 b)) ν :=
    ((((hi 1 3).const_mul 4).add ((hi 2 2).const_mul 40)).add
      ((hi 3 1).const_mul 240)).add ((hi 4 0).const_mul 1080) |>.const_mul K
  have hnon (b : Fin n → Vector p) : 0 ≤ ∑ j, ∑ k, ∑ l, ∑ m,
      sn.localConvolutionFourthSup A (4 * δ / Real.sqrt t) (W b) 1 j k l m := by
    exact Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun k _ =>
      Finset.sum_nonneg (fun l _ => Finset.sum_nonneg (fun m _ =>
        sn.localConvolutionFourthSup_nonneg A
          (div_nonneg (mul_nonneg (by norm_num) h.delta_nonneg) (Real.sqrt_nonneg t))
          (W b) 1 j k l m))))
  have hb := integral_mono_of_nonneg (ae_of_all ν hnon) hJ
    (ae_of_all ν (fun b => hpoint (W b)))
  change s.normalizedFourthSupAverage μ ξ A δ t ht ≤ _
  apply hb.trans
  rw [integral_const_mul, integral_add, integral_add, integral_add]
  · simp only [integral_const_mul]
    have hm := add_le_add (add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left (hbound 1 3 (by decide) (by decide) (by decide))
        (by norm_num : (0 : ℝ) ≤ 4))
      (mul_le_mul_of_nonneg_left (hbound 2 2 (by decide) (by decide) (by decide))
        (by norm_num : (0 : ℝ) ≤ 40)))
      (mul_le_mul_of_nonneg_left (hbound 3 1 (by decide) (by decide) (by decide))
        (by norm_num : (0 : ℝ) ≤ 240)))
      (mul_le_mul_of_nonneg_left (hbound 4 0 (by decide) (by decide) (by decide))
        (by norm_num : (0 : ℝ) ≤ 1080))
    exact (mul_le_mul_of_nonneg_left hm hK).trans_eq (by ring)
  · exact (hi 1 3).const_mul 4
  · exact (hi 2 2).const_mul 40
  · exact ((hi 1 3).const_mul 4).add ((hi 2 2).const_mul 40)
  · exact (hi 3 1).const_mul 240
  · exact (((hi 1 3).const_mul 4).add ((hi 2 2).const_mul 40)).add ((hi 3 1).const_mul 240)
  · exact (hi 4 0).const_mul 1080

theorem fourthFaceMomentCombination_le
    (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) {a₄ : ℝ}
    (hQ : LocalCovarianceLower (A * A.transpose) 4 a₄) (ha₄ : 0 < a₄)
    (hA : ∀ j, (A * A.transpose) j j = 1) :
    4 * (∑ S : GaussianTube.OrderedFaceTuples s.faces 1, GaussianTube.faceMoment S.val s A x 3) +
      40 * (∑ S : GaussianTube.OrderedFaceTuples s.faces 2, GaussianTube.faceMoment S.val s A x 2) +
      240 * (∑ S : GaussianTube.OrderedFaceTuples s.faces 3, GaussianTube.faceMoment S.val s A x 1) +
      1080 * (∑ S : GaussianTube.OrderedFaceTuples s.faces 4, GaussianTube.faceMoment S.val s A x 0) ≤
      1364 * GaussianTube.fourthFaceConstant * (dimensionLog p) ^ 2 := by
  have hbound (q k : ℕ) (hq0 : 0 < q) (hq : q ≤ 4) (hqk : q + k = 4) :=
    GaussianTube.sum_ordered_fourth_faceMoment_le s A x hp hq0 hq hQ ha₄ hA k hqk
  have hm := add_le_add (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left (hbound 1 3 (by decide) (by decide) (by decide))
      (by norm_num : (0 : ℝ) ≤ 4))
    (mul_le_mul_of_nonneg_left (hbound 2 2 (by decide) (by decide) (by decide))
      (by norm_num : (0 : ℝ) ≤ 40)))
    (mul_le_mul_of_nonneg_left (hbound 3 1 (by decide) (by decide) (by decide))
      (by norm_num : (0 : ℝ) ≤ 240)))
    (mul_le_mul_of_nonneg_left (hbound 4 0 (by decide) (by decide) (by decide))
      (by norm_num : (0 : ℝ) ≤ 1080))
  exact hm.trans_eq (by ring)

/-- The actual fourth Gaussian derivative envelope, in both time regimes.
The random shift retains the concrete Bernoulli law of the observations. -/
theorem sharpFourthAverage_largeTime_le
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) {a₃ a₄ : ℝ}
    (hQ3 : LocalCovarianceLower (A * A.transpose) 3 a₃) (ha3 : 0 < a₃)
    (hQ4 : LocalCovarianceLower (A * A.transpose) 4 a₄) (ha4 : 0 < a₄)
    (h43 : a₄ ≤ a₃) (h3c : a₃ ≤ pairGap (A * A.transpose))
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose)) (hband : 12 * δ ≤ s.bandwidth)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (hlarge : s.bandwidth ^ 2 * dimensionLog p ≤ t) :
    s.sharpFourthAverage μ ξ A δ t ≤
      gaussianFourthConstant / (pairGap (A * A.transpose) * a₃ * a₄) *
        (dimensionLog p) ^ 2 * t ^ (-(3 / 2 : ℝ)) := by
  let d := pairGap (A * A.transpose) * a₃ * a₄
  have hd : 0 < d := mul_pos (mul_pos hc ha3) ha4
  let sn := s.scaleDown (Real.sqrt t) (Real.sqrt_pos.mpr ht)
  let K := Real.exp 9 / d
  have hK : 0 ≤ K := div_nonneg (Real.exp_nonneg _) hd.le
  have hδh : δ ≤ s.bandwidth := by linarith [h.delta_nonneg]
  have hr0 : 0 ≤ 4 * δ / Real.sqrt t := by
    exact div_nonneg (mul_nonneg (by norm_num) h.delta_nonneg) (Real.sqrt_nonneg t)
  have hr : 4 * δ / Real.sqrt t ≤ sn.bandwidth :=
    div_le_div_of_nonneg_right (by linarith [h.delta_nonneg]) (Real.sqrt_nonneg t)
  have hpoint (x : Vector p) := sn.sum_localConvolutionFourthSup_unit_le_faceMoments
    hp A hQ3 ha3 hQ4 ha4 h43 h3c hdiag hc hr0 hr x
  have hscale := s.sharpFourthAverage_le_normalizedFourthSupAverage μ ξ h.measurable A
    h.delta_nonneg ht ht1.le
  have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  by_cases hhalf : t ≤ 1 / 2
  · have hnorm := s.normalizedFourthSupAverage_le_of_faceMoments h hp hunit A ht ht1
      hQ4 ha4 hdiag hK hpoint
    have hraw := hscale.trans (div_le_div_of_nonneg_right hnorm (sq_nonneg t))
    let R := (1 + (2 * δ / Real.sqrt t) * Real.sqrt (dimensionLog p)) /
      Real.sqrt ((1 - t) / t)
    have htime : R / t ^ 2 ≤ 3 * Real.sqrt 2 * t ^ (-(3 / 2 : ℝ)) := by
      calc
        _ ≤ 3 * Real.sqrt 2 / t ^ (3 / 2 : ℝ) :=
          normalized_fourth_localization_div_square_le h.delta_nonneg hδh hL hlarge ht hhalf
        _ = (3 * Real.sqrt 2) * (1 / t ^ (3 / 2 : ℝ)) := by ring
        _ = _ := by rw [one_div_rpow_three_halves_eq_neg ht.le]
    have hnon : 0 ≤ (gaussianFourthMomentConstant * 1073741824 / d) * (dimensionLog p) ^ 2 := by
      exact mul_nonneg (div_nonneg (mul_nonneg gaussianFourthMomentConstant_pos.le (by norm_num)) hd.le)
        (sq_nonneg _)
    calc
      _ ≤ (gaussianFourthMomentConstant * 1073741824 / d) * (dimensionLog p) ^ 2 * (R / t ^ 2) := by
        convert hraw using 1
        dsimp only [K, d, R, gaussianFourthMomentConstant]
        ring
      _ ≤ (gaussianFourthMomentConstant * 1073741824 / d) * (dimensionLog p) ^ 2 *
          (3 * Real.sqrt 2 * t ^ (-(3 / 2 : ℝ))) := mul_le_mul_of_nonneg_left htime hnon
      _ = ((3 * Real.sqrt 2 * 1073741824) * gaussianFourthMomentConstant / d) *
          (dimensionLog p) ^ 2 * t ^ (-(3 / 2 : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right gaussianFourthConstant_ge_local hd.le)
          (sq_nonneg _)) (Real.rpow_nonneg ht.le _)
  · have hconst (x : Vector p) : (∑ j, ∑ k, ∑ l, ∑ m,
        sn.localConvolutionFourthSup A (4 * δ / Real.sqrt t) x 1 j k l m) ≤
        (gaussianFourthMomentConstant / d) * (dimensionLog p) ^ 2 := by
      have hh := (hpoint x).trans (mul_le_mul_of_nonneg_left
        (sn.fourthFaceMomentCombination_le hp A x hQ4 ha4 hdiag) hK)
      convert hh using 1
      dsimp only [K, gaussianFourthMomentConstant]
      ring
    have hnorm := s.normalizedFourthSupAverage_le_of_uniform μ ξ A h.delta_nonneg ht hconst
      h.measurable ht1.le
    have hraw := hscale.trans (div_le_div_of_nonneg_right hnorm (sq_nonneg t))
    have htime := inverse_square_le_four_mul_neg_three_halves (le_of_lt (lt_of_not_ge hhalf)) ht1.le
    have hnon : 0 ≤ (gaussianFourthMomentConstant / d) * (dimensionLog p) ^ 2 :=
      mul_nonneg (div_nonneg gaussianFourthMomentConstant_pos.le hd.le) (sq_nonneg _)
    calc
      _ ≤ (gaussianFourthMomentConstant / d) * (dimensionLog p) ^ 2 * (1 / t ^ 2) := by
        convert hraw using 1
        ring
      _ ≤ (gaussianFourthMomentConstant / d) * (dimensionLog p) ^ 2 *
          (4 * t ^ (-(3 / 2 : ℝ))) := mul_le_mul_of_nonneg_left htime hnon
      _ = ((4 * gaussianFourthMomentConstant) / d) * (dimensionLog p) ^ 2 *
          t ^ (-(3 / 2 : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right gaussianFourthConstant_ge_global hd.le)
          (sq_nonneg _)) (Real.rpow_nonneg ht.le _)

end FaceSmoother

/-- The large-time cap is proved for the concrete Gaussian convolutions and
the actual Bernoulli-retained observations, including singular full covariance. -/
theorem gaussianFourthPointwiseCap : GaussianFourthPointwiseCap.{u} gaussianFourthConstant := by
  intro Ω _ μ _ p n hp _ ξ δ A h hlocal hA s hband _ t ht hlarge
  have hQ3 : LocalCovarianceLower (A * A.transpose) 3 (a3 (covariance μ (sumVector ξ))) := by
    rw [hA]
    exact localEigenvalue_lower (matrixQuadratic_nonneg_of_posSemidef hlocal.posSemidef)
  have hQ4 : LocalCovarianceLower (A * A.transpose) 4 (a4 (covariance μ (sumVector ξ))) := by
    rw [hA]
    exact localEigenvalue_lower (matrixQuadratic_nonneg_of_posSemidef hlocal.posSemidef)
  have hh := s.sharpFourthAverage_largeTime_le h hp hlocal.unit_diagonal A
    hQ3 (hlocal.a3_pos hp) hQ4 hlocal.a4_pos
    (a4_le_a3 hp hlocal.posSemidef)
    (by simpa only [hA] using a3_le_pairGap hp hlocal.posSemidef hlocal.unit_diagonal)
    (by simpa only [hA] using hlocal.unit_diagonal)
    (by simpa only [hA] using hlocal.pairGap_pos hp) hband ht.1 ht.2 hlarge
  simpa only [hA] using hh

end
end RectangleCLT
