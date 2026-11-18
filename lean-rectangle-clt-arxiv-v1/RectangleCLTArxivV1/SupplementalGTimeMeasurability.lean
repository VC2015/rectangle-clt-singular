import RectangleCLTArxivV1.SupplementalGComplementary
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-! Genuine time measurability and integrability of the literal seeded
fourth remainder. These justify the printed time integral of its absolute value. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators Interval
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def capSeededTestIntegral {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (C : Matrix (Fin p) (Fin p) ℝ)
    (x : Vector p) (ε : ℝ) (F : Vector p → ℝ) (t : ℝ) : ℝ :=
  ∑ mask : Kane.Cube n, Kane.maskWeight (thinningProbability t) mask*
    ∫ z : Ω × Vector p, F (x+thinningScale t • maskObservationSum ξ mask z.1+
      (Real.sqrt (t+ε) • C).mulVec z.2) ∂μ.prod (standardGaussian p)

theorem capSeededTestIntegral_measurable
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [SFinite μ] (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (C : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (ε : ℝ)
    (F : Vector p → ℝ) (hF : Measurable F) : Measurable (capSeededTestIntegral μ ξ C x ε F) := by
  apply Finset.measurable_sum
  intro mask _
  have hq : Measurable thinningProbability := by unfold thinningProbability; fun_prop
  have hweight : Measurable (fun t => Kane.maskWeight (thinningProbability t) mask) := by
    unfold Kane.maskWeight
    apply Finset.measurable_prod
    intro i _
    split <;> fun_prop
  have hmask : Measurable (fun z : ℝ × (Ω × Vector p) => maskObservationSum ξ mask z.2.1) :=
    (measurable_maskObservationSum ξ hξ mask).comp measurable_snd.fst
  have hscale : Measurable (fun z : ℝ × (Ω × Vector p) => thinningScale z.1) := by
    unfold thinningScale
    fun_prop
  have hgauss : Measurable (fun z : ℝ × (Ω × Vector p) =>
      (Real.sqrt (z.1+ε) • C).mulVec z.2.2) := by
    simp only [Matrix.smul_mulVec_assoc]
    exact (measurable_fst.add_const ε).sqrt.smul ((measurable_mulVec C).comp measurable_snd.snd)
  have hpoint : Measurable (fun z : ℝ × (Ω × Vector p) => x+thinningScale z.1 • maskObservationSum ξ mask z.2.1+
      (Real.sqrt (z.1+ε) • C).mulVec z.2.2) := (measurable_const.add (hscale.smul hmask)).add hgauss
  have hi : Measurable (fun t => ∫ z : Ω × Vector p, F (x+thinningScale t • maskObservationSum ξ mask z.1+
      (Real.sqrt (t+ε) • C).mulVec z.2) ∂μ.prod (standardGaussian p)) :=
    (hF.comp hpoint).stronglyMeasurable.integral_prod_right'.measurable
  exact hweight.mul hi

/-- The measurable finite-mask expression is the actual unconditional
seeded-law test integral throughout the calibrated time interval. -/
theorem capSeededTestIntegral_eq_seededLaw
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (C : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) {ε t : ℝ}
    (hε : 0 ≤ ε) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (F : Vector p → ℝ) (hF : Measurable F) (hFb : ∃ D : ℝ, ∀ y, |F y| ≤ D) :
    capSeededTestIntegral μ ξ C x ε F t = ∫ y, F (x+y) ∂seededInterpolationLaw μ ξ C ε t := by
  let β := bernoulliArrayLaw μ ξ t
  let M := Real.sqrt (t+ε) • C
  let G : Vector p → ℝ := fun y => ∫ g, F (x+y+M.mulVec g) ∂standardGaussian p
  letI := bernoulliArrayLaw_isProbability μ ξ hξ t ht ht1
  obtain ⟨D,hD⟩ := hFb
  have hpoint : Measurable (fun z : Vector p × Vector p => x+z.1+M.mulVec z.2) :=
    (measurable_const.add measurable_fst).add ((measurable_mulVec M).comp measurable_snd)
  have hG : Measurable G := (hF.comp hpoint).stronglyMeasurable.integral_prod_right'.measurable
  have hGb (y : Vector p) : ‖G y‖ ≤ D := by
    simpa only [measureReal_univ_eq_one,mul_one] using
      norm_integral_le_of_norm_le_const (μ := standardGaussian p) (f := fun g => F (x+y+M.mulVec g))
        (ae_of_all _ (fun g => by rw [Real.norm_eq_abs]; exact hD _))
  have hGi (mask : Kane.Cube n) : Integrable (fun b => G (arraySum b)) (μ.map (retainedArray ξ t mask)) := by
    letI : IsProbabilityMeasure (μ.map (retainedArray ξ t mask)) :=
      isProbabilityMeasure_map (measurable_retainedArray ξ hξ t mask).aemeasurable
    exact (integrable_const D).mono' (hG.comp (measurable_arraySum p n)).aestronglyMeasurable
      (ae_of_all _ (fun b => hGb _))
  have hsum := integral_bernoulliArrayLaw_comp_arraySum_eq_sum μ ξ hξ ht ht1 G hG hGi
  have hk : Measurable (fun z : (Fin n → Vector p) × Vector p => F (x+arraySum z.1+M.mulVec z.2)) :=
    hF.comp ((measurable_const.add ((measurable_arraySum p n).comp measurable_fst)).add
      ((measurable_mulVec M).comp measurable_snd))
  have hki : Integrable (fun z : (Fin n → Vector p) × Vector p => F (x+arraySum z.1+M.mulVec z.2))
      (β.prod (standardGaussian p)) :=
    (integrable_const D).mono' hk.aestronglyMeasurable (ae_of_all _ (fun z => by rw [Real.norm_eq_abs]; exact hD _))
  have hmean : (∫ z, F (x+arraySum z.1+M.mulVec z.2) ∂β.prod (standardGaussian p)) =
      ∫ y, F (x+y) ∂seededInterpolationLaw μ ξ C ε t := by
    have hlaw := cap_seededWhole_map_law μ ξ hξ C x hε ht ht1
    have he := congrArg (fun ν : Measure (Vector p) => ∫ y, F y ∂ν) hlaw
    dsimp only at he
    have hY : Measurable (fun z : (Fin n → Vector p) × Vector p => x+arraySum z.1+M.mulVec z.2) :=
      (measurable_const.add ((measurable_arraySum p n).comp measurable_fst)).add
        ((measurable_mulVec M).comp measurable_snd)
    have hshift : Measurable (fun y : Vector p => x+y) := measurable_const.add measurable_id
    rw [integral_map hY.aemeasurable hF.aestronglyMeasurable,
      integral_map hshift.aemeasurable hF.aestronglyMeasurable] at he
    exact he
  rw [← hmean,integral_prod _ hki,hsum]
  unfold capSeededTestIntegral
  apply Finset.sum_congr rfl
  intro mask _
  congr 1
  have hm : Measurable (fun z : Ω × Vector p => F (x+thinningScale t • maskObservationSum ξ mask z.1+M.mulVec z.2)) :=
    hF.comp ((measurable_const.add (measurable_const.smul ((measurable_maskObservationSum ξ hξ mask).comp measurable_fst))).add
      ((measurable_mulVec M).comp measurable_snd))
  have hi : Integrable (fun z : Ω × Vector p => F (x+thinningScale t • maskObservationSum ξ mask z.1+M.mulVec z.2))
      (μ.prod (standardGaussian p)) :=
    (integrable_const D).mono' hm.aestronglyMeasurable (ae_of_all _ (fun z => by rw [Real.norm_eq_abs]; exact hD _))
  exact integral_prod _ hi

theorem cap_relativeCubicContraction_continuous
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) :
    Continuous (relativeCubicContraction s μ ξ) := by
  unfold relativeCubicContraction
  apply continuous_finset_sum
  intro j _
  apply continuous_finset_sum
  intro k _
  apply continuous_finset_sum
  intro l _
  exact continuous_const.mul (s.continuous_thirdDerivative j k l)

theorem cap_relativeCubicContraction_bounded
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) :
    ∃ D : ℝ, ∀ y, |relativeCubicContraction s μ ξ y| ≤ D := by
  refine ⟨∑ j, ∑ k, ∑ l, |relativeThirdMatrix μ ξ j k l| *(13/s.bandwidth^3), ?_⟩
  intro y
  unfold relativeCubicContraction
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro k _
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro l _
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using s.norm_thirdDerivative_le y j k l) (abs_nonneg _)

/-- Raw bounded data suffice for the exact cubic-law identity used in the
measurability argument; no quantitative relative-moment hypothesis is needed. -/
theorem cap_variableSignedCubicPathTerm_eq_seeded_integral
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (C : Matrix (Fin p) (Fin p) ℝ) (x : Vector p)
    {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    s.variableSignedCubicPathTerm (gaussianLaw (Real.sqrt (t+ε) • C)) μ ξ x (thinningProbability t) (1+t) =
      ∫ y, relativeCubicContraction s μ ξ (x+y) ∂seededInterpolationLaw μ ξ C ε t := by
  let L := seededInterpolationLaw μ ξ C ε t
  letI : IsProbabilityMeasure L := seededInterpolationLaw_isProbability μ ξ hξ C ε ht ht1
  have hi (j k l : Fin p) : Integrable (fun y => s.mixedThirdDerivativeF (x+y) j k l) L :=
    integrable_bounded_test_comp L _ (measurable_const.add measurable_id) _
      (s.continuous_thirdDerivative j k l) _ (fun y => s.norm_thirdDerivative_le y j k l)
  unfold FaceSmoother.variableSignedCubicPathTerm
  simp_rw [selectorThirdDerivativeAverage_eq_seeded_integral s μ ξ hξ C x hε ht ht1,
    ← relativeThirdMatrix_eq_coordinate_third_moment μ ξ]
  unfold relativeCubicContraction
  rw [integral_finset_sum Finset.univ (fun j _ => integrable_finset_sum Finset.univ
    (fun k _ => integrable_finset_sum Finset.univ (fun l _ => (hi j k l).const_mul _)))]
  simp_rw [integral_finset_sum Finset.univ (fun k _ => integrable_finset_sum Finset.univ
    (fun l _ => (hi _ k l).const_mul _)),
    integral_finset_sum Finset.univ (fun l _ => (hi _ _ l).const_mul _),integral_const_mul]
  rfl

theorem cap_seededFourthRemainder_eq_measurable_expression
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (C : Matrix (Fin p) (Fin p) ℝ) (hC : C*C.transpose = covariance μ (sumVector ξ))
    (x : Vector p) {ε t : ℝ} (hε : 0 ≤ ε) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    seededFourthRemainder s μ ξ C x ε t =
      deriv (s.seededSelectorHeatExpectation μ ξ C ε x) t+
        (t/3)*capSeededTestIntegral μ ξ C x ε (relativeCubicContraction s μ ξ) t := by
  have hd := (hasDerivAt_seeded_test_manuscript s μ ξ h C hC hε x ht).deriv
  have hc := cap_variableSignedCubicPathTerm_eq_seeded_integral s μ ξ h.measurable C x hε ht.1.le ht.2.le
  rw [← capSeededTestIntegral_eq_seededLaw μ ξ h.measurable C x hε ht.1.le ht.2.le
    (relativeCubicContraction s μ ξ) (cap_relativeCubicContraction_continuous s μ ξ).measurable
    (cap_relativeCubicContraction_bounded s μ ξ)] at hc
  rw [hc] at hd
  linarith

/-- The actual remainder is measurable on the open calibrated time interval. -/
theorem cap_seededFourthRemainder_indicator_measurable
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (C : Matrix (Fin p) (Fin p) ℝ) (hC : C*C.transpose = covariance μ (sumVector ξ))
    (x : Vector p) {ε : ℝ} (hε : 0 ≤ ε) :
    Measurable ((Set.Ioo (0 : ℝ) 1).indicator (fun t => seededFourthRemainder s μ ξ C x ε t)) := by
  let Q (t : ℝ) := deriv (s.seededSelectorHeatExpectation μ ξ C ε x) t+
    (t/3)*capSeededTestIntegral μ ξ C x ε (relativeCubicContraction s μ ξ) t
  have hQ : Measurable Q := (measurable_deriv _).add ((measurable_id.div_const 3).mul
    (capSeededTestIntegral_measurable μ ξ h.measurable C x ε _ (cap_relativeCubicContraction_continuous s μ ξ).measurable))
  have he : (Set.Ioo (0 : ℝ) 1).indicator (fun t => seededFourthRemainder s μ ξ C x ε t) =
      (Set.Ioo (0 : ℝ) 1).indicator Q := by
    funext t
    by_cases ht : t ∈ Set.Ioo (0 : ℝ) 1
    · simp only [Set.indicator_of_mem ht]
      exact cap_seededFourthRemainder_eq_measurable_expression s μ ξ h C hC x hε ht
    · simp only [Set.indicator_of_not_mem ht]
  rw [he]
  exact hQ.indicator measurableSet_Ioo

theorem cap_seededFourthRemainder_aestronglyMeasurable
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (C : Matrix (Fin p) (Fin p) ℝ) (hC : C*C.transpose = covariance μ (sumVector ξ))
    (x : Vector p) {ε : ℝ} (hε : 0 ≤ ε) :
    AEStronglyMeasurable (fun t => seededFourthRemainder s μ ξ C x ε t)
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
  apply (cap_seededFourthRemainder_indicator_measurable s μ ξ h C hC x hε).aestronglyMeasurable.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  simp only [Set.indicator_of_mem ht]

/-- A coarse actual bound suffices for time integrability; this intermediate
lemma allows either the old relative rate or the proved complementary rate. -/
theorem cap_seededFourthRemainder_intervalIntegrable_of_bound
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (C : Matrix (Fin p) (Fin p) ℝ) (hC : C*C.transpose = covariance μ (sumVector ξ))
    (x : Vector p) {ε B : ℝ} (hε : 0 ≤ ε)
    (hB : ∀ t ∈ Set.Ioo (0 : ℝ) 1, |seededFourthRemainder s μ ξ C x ε t| ≤ B) :
    IntervalIntegrable (fun t => seededFourthRemainder s μ ξ C x ε t) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ)≤1)]
  have hBi : IntegrableOn (fun _ : ℝ => B) (Set.Ioo (0 : ℝ) 1) volume :=
    integrableOn_const.mpr (Or.inr (by norm_num [Real.volume_Ioo]))
  apply hBi.mono' (cap_seededFourthRemainder_aestronglyMeasurable s μ ξ h C hC x hε)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  rw [Real.norm_eq_abs]
  exact hB t ht

/-- The literal remainder is time-integrable under the same raw hypotheses
as the complementary bound whenever ε>0. No integrability premise is supplied. -/
theorem cap_seededFourthRemainder_intervalIntegrable
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (A : Matrix (Fin p) (Fin r) ℝ)
    (C : Matrix (Fin p) (Fin p) ℝ)
    (hA : A*A.transpose = covariance μ (sumVector ξ)) (hC : C*C.transpose = covariance μ (sumVector ξ))
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1) (hr : 1 ≤ r)
    (s : FaceSmoother p) (x : Vector p) {h₀ ε : ℝ} (hh₀ : 0 < h₀)
    (hwidth : h₀ ≤ s.bandwidth) (hband : 16*δ ≤ h₀) (hε : 0 < ε) :
    IntervalIntegrable (fun t => seededFourthRemainder s μ ξ C x ε t) volume 0 1 := by
  apply cap_seededFourthRemainder_intervalIntegrable_of_bound s μ ξ h C hC x hε.le
    (B := capSeededComplementaryConstant*
      ((s.faces.card : ℝ)*(r : ℝ)*δ^2/(ε*Real.sqrt ε)+
        (s.faces.card : ℝ)^2*Real.sqrt (r : ℝ)*δ^2/(h₀*Real.sqrt ε)))
  intro t ht
  have hb := cap_seededFourthRemainder_complementary_bound h A C hA hC hunit hr s x hh₀ hwidth hband hε.le ht
  have hv : ε ≤ t+ε := by linarith [ht.1]
  have hv0 : 0 ≤ t+ε := by linarith [ht.1]
  have hsqrt : Real.sqrt ε ≤ Real.sqrt (t+ε) := Real.sqrt_le_sqrt hv
  have hsqrt0 : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ capSeededComplementaryConstant_nonneg
  apply add_le_add
  · exact div_le_div_of_nonneg_left (by positivity) (mul_pos hε hsqrt0)
      (mul_le_mul hv hsqrt (Real.sqrt_nonneg ε) hv0)
  · exact div_le_div_of_nonneg_left (by positivity) (mul_pos hh₀ hsqrt0)
      (mul_le_mul_of_nonneg_left hsqrt hh₀.le)

theorem cap_seededFourthRemainder_abs_intervalIntegrable
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (A : Matrix (Fin p) (Fin r) ℝ)
    (C : Matrix (Fin p) (Fin p) ℝ)
    (hA : A*A.transpose = covariance μ (sumVector ξ)) (hC : C*C.transpose = covariance μ (sumVector ξ))
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1) (hr : 1 ≤ r)
    (s : FaceSmoother p) (x : Vector p) {h₀ ε : ℝ} (hh₀ : 0 < h₀)
    (hwidth : h₀ ≤ s.bandwidth) (hband : 16*δ ≤ h₀) (hε : 0 < ε) :
    IntervalIntegrable (fun t => |seededFourthRemainder s μ ξ C x ε t|) volume 0 1 := by
  simpa only [Real.norm_eq_abs] using
    (cap_seededFourthRemainder_intervalIntegrable h A C hA hC hunit hr s x hh₀ hwidth hband hε).norm

end
end RectangleCLTArxivV1
