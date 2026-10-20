import RectangleCLT.BoundedSmoothingEstimate
import RectangleCLT.LocalReduction
import RectangleCLT.DerivativeIntegration
import RectangleCLT.GaussianDerivativeBounds
import Mathlib.Topology.Order.Compact

/-! Assembly of the sharp local-covariance target from explicit integral
caps on actual Gaussian-convolved derivative tensors. The generic reductions
in this file retain explicit analytic hypotheses. `GaussianFourthFinal.lean`
proves the last cap, and `Main.lean` applies it to prove the main CLT. -/

open MeasureTheory Set
open scoped BigOperators Topology Interval

universe u

namespace RectangleCLT

private theorem continuous_gaussian_kernel_integral {p : ℕ}
    (G : Vector p → ℝ) (hG : Continuous G) (C : ℝ) (hb : ∀ x, ‖G x‖ ≤ C)
    (A : Matrix (Fin p) (Fin p) ℝ) :
    Continuous (fun y : Vector p × ℝ =>
      ∫ z, G (y.1 + Real.sqrt y.2 • A.mulVec z) ∂standardGaussian p) := by
  apply continuous_of_dominated (bound := fun _ => C)
  · intro y
    apply Continuous.aestronglyMeasurable
    apply hG.comp
    fun_prop
  · intro y
    exact ae_of_all _ (fun z => hb _)
  · exact integrable_const C
  · exact ae_of_all _ (fun z => by apply hG.comp; fun_prop)

namespace FaceSmoother

variable {p : ℕ} (s : FaceSmoother p)

theorem convolutionThirdDerivative_gaussian_eq_standardIntegral
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (t : ℝ) (j k l : Fin p) :
    s.convolutionThirdDerivative (gaussianLaw (Real.sqrt t • A)) x j k l =
      ∫ z, s.mixedThirdDerivativeF (x + Real.sqrt t • A.mulVec z) j k l ∂standardGaussian p := by
  rw [s.convolutionThirdDerivative_eq_integral, gaussianLaw,
    integral_map (f := fun z : Vector p => s.mixedThirdDerivativeF (x + z) j k l)
      (measurable_mulVec (Real.sqrt t • A)).aemeasurable
      (((s.continuous_thirdDerivative j k l).comp (continuous_const.add continuous_id)).aestronglyMeasurable)]
  simp only [Matrix.smul_mulVec_assoc]

theorem convolutionFourthDerivative_gaussian_eq_standardIntegral
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (t : ℝ) (j k l m : Fin p) :
    s.convolutionFourthDerivative (gaussianLaw (Real.sqrt t • A)) x j k l m =
      ∫ z, s.mixedFourthDerivativeF (x + Real.sqrt t • A.mulVec z) j k l m ∂standardGaussian p := by
  rw [s.convolutionFourthDerivative_eq_integral, gaussianLaw,
    integral_map (f := fun z : Vector p => s.mixedFourthDerivativeF (x + z) j k l m)
      (measurable_mulVec (Real.sqrt t • A)).aemeasurable
      (((s.continuous_fourthDerivative j k l m).comp (continuous_const.add continuous_id)).aestronglyMeasurable)]
  simp only [Matrix.smul_mulVec_assoc]

theorem continuous_gaussianConvolutionThirdDerivative
    (A : Matrix (Fin p) (Fin p) ℝ) (j k l : Fin p) :
    Continuous (fun y : Vector p × ℝ =>
      s.convolutionThirdDerivative (gaussianLaw (Real.sqrt y.2 • A)) y.1 j k l) := by
  simp_rw [s.convolutionThirdDerivative_gaussian_eq_standardIntegral]
  exact continuous_gaussian_kernel_integral _ (s.continuous_thirdDerivative j k l) _
    (fun x => s.norm_thirdDerivative_le x j k l) A

theorem continuous_gaussianConvolutionFourthDerivative
    (A : Matrix (Fin p) (Fin p) ℝ) (j k l m : Fin p) :
    Continuous (fun y : Vector p × ℝ =>
      s.convolutionFourthDerivative (gaussianLaw (Real.sqrt y.2 • A)) y.1 j k l m) := by
  simp_rw [s.convolutionFourthDerivative_gaussian_eq_standardIntegral]
  exact continuous_gaussian_kernel_integral _ (s.continuous_fourthDerivative j k l m) _
    (fun x => s.norm_fourthDerivative_le x j k l m) A

/-- The literal local supremum of the actual Gaussian-convolved fourth
coordinate derivative, preserving convolution cancellations. -/
noncomputable def localConvolutionFourthSup
    (A : Matrix (Fin p) (Fin p) ℝ) (r : ℝ) (x : Vector p) (t : ℝ) (j k l m : Fin p) : ℝ :=
  sSup ((fun v : Vector p =>
    |s.convolutionFourthDerivative (gaussianLaw (Real.sqrt t • A)) (x + v) j k l m|) ''
      Metric.closedBall 0 r)

theorem continuous_localConvolutionFourthSup
    (A : Matrix (Fin p) (Fin p) ℝ) (r : ℝ) (j k l m : Fin p) :
    Continuous (fun y : Vector p × ℝ => s.localConvolutionFourthSup A r y.1 y.2 j k l m) := by
  have hf : Continuous (fun z : (Vector p × ℝ) × Vector p =>
      |s.convolutionFourthDerivative (gaussianLaw (Real.sqrt z.1.2 • A))
        (z.1.1 + z.2) j k l m|) := by
    have hg : Continuous (fun z : (Vector p × ℝ) × Vector p => (z.1.1 + z.2, z.1.2)) :=
      (continuous_fst.fst.add continuous_snd).prodMk continuous_fst.snd
    exact ((s.continuous_gaussianConvolutionFourthDerivative A j k l m).comp hg).abs
  exact (isCompact_closedBall (0 : Vector p) r).continuous_sSup
    (f := fun (y : Vector p × ℝ) (v : Vector p) =>
      |s.convolutionFourthDerivative (gaussianLaw (Real.sqrt y.2 • A)) (y.1 + v) j k l m|) hf

private theorem localConvolutionFourthSup_bddAbove
    (A : Matrix (Fin p) (Fin p) ℝ) (r : ℝ) (x : Vector p) (t : ℝ) (j k l m : Fin p) :
    BddAbove ((fun v : Vector p =>
      |s.convolutionFourthDerivative (gaussianLaw (Real.sqrt t • A)) (x + v) j k l m|) ''
        Metric.closedBall 0 r) := by
  refine ⟨75 / s.bandwidth ^ 4, ?_⟩
  rintro y ⟨v, _, rfl⟩
  simpa only [Real.norm_eq_abs] using
    s.norm_convolutionFourthDerivative_le (gaussianLaw (Real.sqrt t • A)) (x + v) j k l m

theorem abs_convolutionFourthDerivative_le_localSup
    (A : Matrix (Fin p) (Fin p) ℝ) {r : ℝ} (x : Vector p) (t : ℝ)
    {v : Vector p} (hv : ‖v‖ ≤ r) (j k l m : Fin p) :
    |s.convolutionFourthDerivative (gaussianLaw (Real.sqrt t • A)) (x + v) j k l m| ≤
      s.localConvolutionFourthSup A r x t j k l m := by
  apply le_csSup (s.localConvolutionFourthSup_bddAbove A r x t j k l m)
  exact ⟨v, by simpa only [Metric.mem_closedBall, dist_zero_right] using hv, rfl⟩

theorem localConvolutionFourthSup_nonneg
    (A : Matrix (Fin p) (Fin p) ℝ) {r : ℝ} (hr : 0 ≤ r) (x : Vector p) (t : ℝ) (j k l m : Fin p) :
    0 ≤ s.localConvolutionFourthSup A r x t j k l m :=
  (abs_nonneg _).trans (s.abs_convolutionFourthDerivative_le_localSup A x t
    (v := 0) (by simpa only [norm_zero] using hr) j k l m)

theorem localConvolutionFourthSup_le_const
    (A : Matrix (Fin p) (Fin p) ℝ) {r : ℝ} (hr : 0 ≤ r) (x : Vector p) (t : ℝ) (j k l m : Fin p) :
    s.localConvolutionFourthSup A r x t j k l m ≤ 75 / s.bandwidth ^ 4 := by
  apply csSup_le
  · exact ⟨_, 0, by simpa only [Metric.mem_closedBall, dist_self] using hr, rfl⟩
  · rintro y ⟨v, _, rfl⟩
    simpa only [Real.norm_eq_abs] using
      s.norm_convolutionFourthDerivative_le (gaussianLaw (Real.sqrt t • A)) (x + v) j k l m

theorem norm_localConvolutionFourthSup_le_const
    (A : Matrix (Fin p) (Fin p) ℝ) {r : ℝ} (hr : 0 ≤ r) (x : Vector p) (t : ℝ) (j k l m : Fin p) :
    ‖s.localConvolutionFourthSup A r x t j k l m‖ ≤ 75 / s.bandwidth ^ 4 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (s.localConvolutionFourthSup_nonneg A hr x t j k l m)]
  exact s.localConvolutionFourthSup_le_const A hr x t j k l m

theorem localConvolutionFourthSup_le_coarseMajorant
    (A : Matrix (Fin p) (Fin p) ℝ) {r : ℝ} (hr : 0 ≤ r) (hrh : r ≤ s.bandwidth)
    (x : Vector p) (t : ℝ) (j k l m : Fin p) :
    s.localConvolutionFourthSup A r x t j k l m ≤
      s.convolutionFourthLocalMajorant (gaussianLaw (Real.sqrt t • A)) x j k l m := by
  apply csSup_le
  · exact ⟨_, 0, by simpa only [Metric.mem_closedBall, dist_self] using hr, rfl⟩
  · rintro y ⟨v, hv, rfl⟩
    exact s.abs_convolutionFourthDerivative_shift_le (gaussianLaw (Real.sqrt t • A)) x
      ((show ‖v‖ ≤ r by simpa only [Metric.mem_closedBall, dist_zero_right] using hv).trans hrh) j k l m


private theorem continuous_shiftedKernelExpectation
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → Vector p) (hW : Measurable W) (G : Vector p × ℝ → ℝ)
    (hG : Continuous G) (C : ℝ) (hb : ∀ y, ‖G y‖ ≤ C) :
    Continuous (fun t : ℝ => ∫ ω, G (thinningScale t • W ω, t) ∂μ) := by
  apply continuous_of_dominated (bound := fun _ => C)
  · intro t
    exact (hG.measurable.comp ((measurable_const.smul hW).prodMk measurable_const)).aestronglyMeasurable
  · intro t
    exact ae_of_all _ (fun ω => hb _)
  · exact integrable_const C
  · exact ae_of_all _ (fun ω => by
      apply hG.comp
      change Continuous (fun t : ℝ => ((1 + t) • W ω, t))
      fun_prop)

private theorem continuousOn_selectorKernelAverage
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (G : Vector p × ℝ → ℝ) (hG : Continuous G) (C : ℝ) (hb : ∀ y, ‖G y‖ ≤ C) :
    ContinuousOn (fun t => ∑ mask, Kane.maskWeight (thinningProbability t) mask *
      ∫ ω, G (thinningScale t • maskObservationSum ξ mask ω, t) ∂μ) (Icc 0 1) := by
  apply continuousOn_finset_sum
  intro mask _
  apply ContinuousOn.mul
  · have hq : ContinuousOn thinningProbability (Icc (0 : ℝ) 1) := by
      apply ContinuousOn.div (continuous_const.sub continuous_id).continuousOn
        ((continuous_const.add continuous_id).pow 2).continuousOn
      intro t ht
      simp only [id_eq]
      exact pow_ne_zero 2 (by linarith [ht.1])
    unfold Kane.maskWeight
    apply continuousOn_finset_prod
    intro i _
    cases hm : mask i
    · simpa only [hm, Bool.false_eq_true, ↓reduceIte] using continuousOn_const.sub hq
    · simpa only [hm, ↓reduceIte] using hq
  · exact (continuous_shiftedKernelExpectation μ _
      (measurable_maskObservationSum ξ hξ mask) G hG C hb).continuousOn

/-- Actual expected absolute third-derivative tensor along the concrete
Bernoulli/Gaussian interpolation. -/
noncomputable def sharpThirdAverage
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) (t : ℝ) : ℝ :=
  s.selectorThirdAbsoluteAverage (gaussianLaw (Real.sqrt t • A)) μ ξ 0
    (thinningProbability t) (thinningScale t)

/-- Expected sum of the separate actual local fourth-derivative suprema.
The coordinate supremum is taken before each expectation and finite sum. -/
noncomputable def sharpFourthAverage
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) (δ t : ℝ) : ℝ :=
  ∑ j, ∑ k, ∑ l, ∑ m, ∑ mask, Kane.maskWeight (thinningProbability t) mask *
    ∫ ω, s.localConvolutionFourthSup A (4 * δ)
      (thinningScale t • maskObservationSum ξ mask ω) t j k l m ∂μ

theorem continuousOn_sharpThirdAverage
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (A : Matrix (Fin p) (Fin p) ℝ) :
    ContinuousOn (s.sharpThirdAverage μ ξ A) (Icc 0 1) := by
  have hh (j k l : Fin p) := continuousOn_selectorKernelAverage μ ξ hξ
    (fun y => |s.convolutionThirdDerivative (gaussianLaw (Real.sqrt y.2 • A)) y.1 j k l|)
    (s.continuous_gaussianConvolutionThirdDerivative A j k l).abs (13 / s.bandwidth ^ 3)
    (fun y => by simpa only [Real.norm_eq_abs, abs_abs] using
      s.norm_convolutionThirdDerivative_le (gaussianLaw (Real.sqrt y.2 • A)) y.1 j k l)
  apply (continuousOn_finset_sum Finset.univ (fun j _ =>
    continuousOn_finset_sum Finset.univ (fun k _ =>
      continuousOn_finset_sum Finset.univ (fun l _ => hh j k l)))).congr
  intro t _
  simpa only [sharpThirdAverage, zero_add] using
    s.selectorThirdAbsoluteAverage_eq_sum (gaussianLaw (Real.sqrt t • A)) μ ξ hξ 0
      (thinningProbability t) (thinningScale t)

theorem continuousOn_sharpFourthAverage
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (A : Matrix (Fin p) (Fin p) ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    ContinuousOn (s.sharpFourthAverage μ ξ A δ) (Icc 0 1) := by
  apply continuousOn_finset_sum
  intro j _
  apply continuousOn_finset_sum
  intro k _
  apply continuousOn_finset_sum
  intro l _
  apply continuousOn_finset_sum
  intro m _
  exact continuousOn_selectorKernelAverage μ ξ hξ
    (fun y => s.localConvolutionFourthSup A (4 * δ) y.1 y.2 j k l m)
    (s.continuous_localConvolutionFourthSup A (4 * δ) j k l m) (75 / s.bandwidth ^ 4)
    (fun y => s.norm_localConvolutionFourthSup_le_const A (by positivity) y.1 y.2 j k l m)

theorem integrable_localConvolutionFourthSup_comp
    (A : Matrix (Fin p) (Fin p) ℝ) {r : ℝ} (hr : 0 ≤ r) (t : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (W : Ω → Vector p) (hW : Measurable W) (j k l m : Fin p) :
    Integrable (fun ω => s.localConvolutionFourthSup A r (W ω) t j k l m) μ :=
  integrable_bounded_test_comp μ W hW _
    ((s.continuous_localConvolutionFourthSup A r j k l m).comp
      (continuous_id.prodMk continuous_const)) _
    (fun x => s.norm_localConvolutionFourthSup_le_const A hr x t j k l m)

theorem sharpFourthAverage_eq_selectorEnvelope
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (A : Matrix (Fin p) (Fin p) ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (t : ℝ) :
    s.sharpFourthAverage μ ξ A δ t = selectorFourthEnvelopeAverage μ ξ 0 t
      (fun x j k l m => s.localConvolutionFourthSup A (4 * δ) x t j k l m) := by
  have hi (mask : Kane.Cube n) (j k l m : Fin p) :=
    s.integrable_localConvolutionFourthSup_comp A (show 0 ≤ 4 * δ by positivity) t μ
      (fun ω => thinningScale t • maskObservationSum ξ mask ω)
      (measurable_const.smul (measurable_maskObservationSum ξ hξ mask)) j k l m
  unfold selectorFourthEnvelopeAverage
  simp only [zero_add]
  simp_rw [integral_finset_sum Finset.univ (fun j _ =>
    integrable_finset_sum Finset.univ (fun k _ =>
      integrable_finset_sum Finset.univ (fun l _ =>
        integrable_finset_sum Finset.univ (fun m _ => hi _ j k l m)))),
    integral_finset_sum Finset.univ (fun k _ =>
      integrable_finset_sum Finset.univ (fun l _ =>
        integrable_finset_sum Finset.univ (fun m _ => hi _ _ k l m))),
    integral_finset_sum Finset.univ (fun l _ =>
      integrable_finset_sum Finset.univ (fun m _ => hi _ _ _ l m)),
    integral_finset_sum Finset.univ (fun m _ => hi _ _ _ _ m)]
  simp only [Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.sum_comm]


/-- The canonical supremum envelope inherits the proved unconditional
short-scale expected-mass bound. -/
theorem sharpFourthAverage_shortScale_le
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = covariance μ (sumVector ξ))
    (hband : 12 * δ ≤ s.bandwidth) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    s.sharpFourthAverage μ ξ A δ t ≤
      (75 * (Real.exp 2) ^ 5 * interpolationShortScaleConstant) *
        Real.sqrt (dimensionLog p) / s.bandwidth ^ 3 := by
  rw [s.sharpFourthAverage_eq_selectorEnvelope μ ξ h.measurable A h.delta_nonneg t]
  have hc : selectorFourthEnvelopeAverage μ ξ 0 t
      (fun x j k l m => s.localConvolutionFourthSup A (4 * δ) x t j k l m) ≤
      selectorFourthEnvelopeAverage μ ξ 0 t
        (s.convolutionFourthLocalMajorant (gaussianLaw (Real.sqrt t • A))) := by
    unfold selectorFourthEnvelopeAverage
    apply Finset.sum_le_sum
    intro mask _
    apply mul_le_mul_of_nonneg_left _
      (Kane.maskWeight_nonneg (thinningProbability_nonneg ht1) (thinningProbability_le_one ht) mask)
    let W : Ω → Vector p := fun ω => 0 + thinningScale t • maskObservationSum ξ mask ω
    have hW : Measurable W := measurable_const.add
      (measurable_const.smul (measurable_maskObservationSum ξ h.measurable mask))
    have hi := integrable_finset_sum Finset.univ (fun j _ =>
      integrable_finset_sum Finset.univ (fun k _ =>
        integrable_finset_sum Finset.univ (fun l _ =>
          integrable_finset_sum Finset.univ (fun m _ =>
            s.integrable_localConvolutionFourthSup_comp A (show 0 ≤ 4 * δ from mul_nonneg (by norm_num) h.delta_nonneg) t μ W hW j k l m))))
    have hj := s.integrable_sum_convolutionFourthLocalMajorant_mask
      (gaussianLaw (Real.sqrt t • A)) μ ξ h.measurable 0 (thinningScale t) mask
    apply integral_mono hi hj
    intro ω
    exact Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ =>
      Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun m _ =>
        s.localConvolutionFourthSup_le_coarseMajorant A (show 0 ≤ 4 * δ from mul_nonneg (by norm_num) h.delta_nonneg)
          (by linarith [h.delta_nonneg]) _ t j k l m
  exact hc.trans (s.selectorFourthEnvelopeAverage_shortScale_le μ ξ h hp hunit A hA hband ht ht1)

/-- Comparison with the canonical actual derivative suprema; every local
measurability and integrability requirement is proved internally. -/
theorem abs_selectorHeatDerivative_le_sharpAverages
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = covariance μ (sumVector ξ))
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    |s.selectorHeatDerivative μ ξ A 0 t| ≤
      t / 3 * gamma3 μ ξ * s.sharpThirdAverage μ ξ A t +
        6 * gamma4 μ ξ * s.sharpFourthAverage μ ξ A δ t := by
  have hHi (mask : Kane.Cube n) : Integrable (fun ω => ∑ j, ∑ k, ∑ l, ∑ m,
      s.localConvolutionFourthSup A (4 * δ)
        (0 + thinningScale t • maskObservationSum ξ mask ω) t j k l m) μ :=
    integrable_finset_sum Finset.univ (fun j _ =>
      integrable_finset_sum Finset.univ (fun k _ =>
        integrable_finset_sum Finset.univ (fun l _ =>
          integrable_finset_sum Finset.univ (fun m _ =>
            s.integrable_localConvolutionFourthSup_comp A (show 0 ≤ 4 * δ from mul_nonneg (by norm_num) h.delta_nonneg) t μ _
              (measurable_const.add (measurable_const.smul
                (measurable_maskObservationSum ξ h.measurable mask))) j k l m))))
  have hh := s.abs_selectorHeatDerivative_le_comparison μ ξ h A hA 0 ht ht1
    (fun x j k l m => s.localConvolutionFourthSup A (4 * δ) x t j k l m)
    (fun x v hv j k l m => s.abs_convolutionFourthDerivative_le_localSup A x t hv j k l m) hHi
  rw [← s.sharpFourthAverage_eq_selectorEnvelope μ ξ h.measurable A h.delta_nonneg t] at hh
  exact hh

/-- The already proved sharp Gaussian third-derivative estimate also bounds
the actual selector-averaged tensor, for every positive variance time. -/
theorem sharpThirdAverage_gaussian_le
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i)) (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ)
    {Q : Matrix (Fin p) (Fin p) ℝ} (hQ : LocalCovarianceHypotheses Q)
    (hA : A * A.transpose = Q) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    s.sharpThirdAverage μ ξ A t ≤
      gaussianThirdConstant * (dimensionLog p) ^ (3 / 2 : ℝ) /
        (pairGap Q * a3 Q * t ^ (3 / 2 : ℝ)) := by
  let B := gaussianThirdConstant * (dimensionLog p) ^ (3 / 2 : ℝ) /
    (pairGap Q * a3 Q * t ^ (3 / 2 : ℝ))
  have hi (mask : Kane.Cube n) := integrable_finset_sum Finset.univ (fun j _ =>
    integrable_finset_sum Finset.univ (fun k _ =>
      integrable_finset_sum Finset.univ (fun l _ =>
        (s.integrable_convolutionThirdDerivative_mask (gaussianLaw (Real.sqrt t • A))
          μ ξ hξ 0 (thinningScale t) mask j k l).abs)))
  have hm (mask : Kane.Cube n) :
      (∫ ω, ∑ j, ∑ k, ∑ l,
        |s.convolutionThirdDerivative (gaussianLaw (Real.sqrt t • A))
          (0 + thinningScale t • maskObservationSum ξ mask ω) j k l| ∂μ) ≤ B := by
    have hh := integral_mono (hi mask) (integrable_const B) (fun ω =>
      s.sum_abs_convolutionThirdDerivative_gaussian_sqrt_le_of_localCovariance
        hp A _ hQ hA ht)
    simpa only [integral_const, measureReal_univ_eq_one, one_smul] using hh
  unfold sharpThirdAverage selectorThirdAbsoluteAverage
  calc
    _ ≤ ∑ mask : Kane.Cube n, Kane.maskWeight (thinningProbability t) mask * B :=
      Finset.sum_le_sum (fun mask _ => mul_le_mul_of_nonneg_left (hm mask)
        (Kane.maskWeight_nonneg (thinningProbability_nonneg ht1) (thinningProbability_le_one ht.le) mask))
    _ = B := by rw [← Finset.sum_mul, Kane.maskWeight_sum, one_mul]

private theorem rpow_three_halves_eq_mul_sqrt {L : ℝ} (hL : 0 < L) :
    L ^ (3 / 2 : ℝ) = L * Real.sqrt L := by
  calc
    _ = L ^ ((1 : ℝ) + (1 / 2 : ℝ)) := by norm_num
    _ = L ^ (1 : ℝ) * L ^ (1 / 2 : ℝ) := Real.rpow_add hL _ _
    _ = _ := by rw [Real.rpow_one, Real.sqrt_eq_rpow]

/-- The sharp cubic time integral is proved unconditionally from the actual
Gaussian third-derivative theorem. The fourth-order cap is supplied by
`gaussianFourthPointwiseCap` in `GaussianFourthFinal.lean`. -/
theorem integral_time_mul_sharpThirdAverage_le
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i)) (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ)
    {Q : Matrix (Fin p) (Fin p) ℝ} (hQ : LocalCovarianceHypotheses Q)
    (hA : A * A.transpose = Q) :
    (∫ t in (0 : ℝ)..1, t * s.sharpThirdAverage μ ξ A t) ≤
      2 * gaussianThirdConstant * dimensionLog p * Real.sqrt (dimensionLog p) /
        (pairGap Q * a3 Q) := by
  have hD : IntervalIntegrable (fun t : ℝ => t * s.sharpThirdAverage μ ξ A t) volume 0 1 :=
    (continuousOn_id.mul (s.continuousOn_sharpThirdAverage μ ξ hξ A)).intervalIntegrable_of_Icc
    (by norm_num : (0 : ℝ) ≤ 1)
  have hL : 0 < dimensionLog p := lt_of_lt_of_le (by norm_num) (log_exp_mul_nat_ge_one hp)
  have hh := integral_time_mul_third_le (B := gaussianThirdConstant *
    (dimensionLog p) ^ (3 / 2 : ℝ) / (pairGap Q * a3 Q)) hD (fun t ht => by
      have hb := s.sharpThirdAverage_gaussian_le μ ξ hξ hp A hQ hA ht.1 ht.2.le
      apply hb.trans_eq
      rw [Real.rpow_neg ht.1.le]
      ring)
  rw [rpow_three_halves_eq_mul_sqrt hL] at hh
  convert hh using 1; ring


/-- The actual fundamental theorem of calculus reduces the smoother gap to
the two concrete derivative expectations, with no integrability hypotheses. -/
theorem interpolation_smoother_gap_le_sharpTimeIntegrals
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = covariance μ (sumVector ξ)) :
    |(∫ ω, s.F (sumVector ξ ω) ∂μ) - (∫ z, s.F z ∂gaussianLaw A)| ≤
      gamma3 μ ξ / 3 * (∫ t in (0 : ℝ)..1, t * s.sharpThirdAverage μ ξ A t) +
        6 * gamma4 μ ξ * (∫ t in (0 : ℝ)..1, s.sharpFourthAverage μ ξ A δ t) := by
  let g : ℝ → ℝ := fun t => gamma3 μ ξ / 3 * (t * s.sharpThirdAverage μ ξ A t) +
    6 * gamma4 μ ξ * s.sharpFourthAverage μ ξ A δ t
  have hc3 := continuousOn_id.mul (s.continuousOn_sharpThirdAverage μ ξ h.measurable A)
  have hc4 := s.continuousOn_sharpFourthAverage μ ξ h.measurable A h.delta_nonneg
  have hgc : ContinuousOn g (Icc 0 1) :=
    (continuousOn_const.mul hc3).add (continuousOn_const.mul hc4)
  have hi3 : IntervalIntegrable (fun t : ℝ => t * s.sharpThirdAverage μ ξ A t) volume 0 1 :=
    hc3.intervalIntegrable_of_Icc (by norm_num)
  have hi4 : IntervalIntegrable (s.sharpFourthAverage μ ξ A δ) volume 0 1 :=
    hc4.intervalIntegrable_of_Icc (by norm_num)
  have hh := s.interpolation_smoother_gap_le_integral μ h A hgc.integrableOn_Icc
    (fun t ht => by
      have hb := s.abs_selectorHeatDerivative_le_sharpAverages μ ξ h A hA ht.1.le ht.2.le
      convert hb using 1; dsimp [g]; ring)
  apply hh.trans_eq
  exact (intervalIntegral.integral_add (hi3.const_mul _) (hi4.const_mul _)).trans (by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul])

end FaceSmoother

/-- Explicit actual Gaussian fourth-derivative integral cap sufficient for
the sharp master estimate. This proposition is discharged in `Main.lean`
using `GaussianFourthFinal.lean` and the checked scalar integration theorem.
The local suprema preserve Gaussian-convolution cancellations. -/
def GaussianFourthIntegralCap (C₄ : ℝ) : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p n : ℕ), 1 ≤ p → 1 ≤ n →
    ∀ (ξ : Fin n → Ω → Vector p) (δ : ℝ)
      (A : Matrix (Fin p) (Fin p) ℝ),
      BoundedIndependentHypotheses μ ξ δ →
      LocalCovarianceHypotheses (covariance μ (sumVector ξ)) →
      A * A.transpose = covariance μ (sumVector ξ) →
      ∀ s : FaceSmoother p, 12 * δ ≤ s.bandwidth →
        s.bandwidth * Real.sqrt (dimensionLog p) ≤ 1 →
        (∫ t in (0 : ℝ)..1, s.sharpFourthAverage μ ξ A δ t) ≤
          C₄ * dimensionLog p * Real.sqrt (dimensionLog p) /
            (s.bandwidth * Real.rpow
              (pairGap (covariance μ (sumVector ξ)) *
                a3 (covariance μ (sumVector ξ)) * a4 (covariance μ (sumVector ξ))) (2 / 3 : ℝ))

noncomputable def sharpMasterAssemblyConstant (C₄ : ℝ) : ℝ :=
  1 + FaceSmoother.gaussianThirdConstant + 6 * C₄ + (8 * Real.exp 4 + 4)

theorem sharpMasterAssemblyConstant_ge_one {C₄ : ℝ} (hC₄ : 0 ≤ C₄) :
    1 ≤ sharpMasterAssemblyConstant C₄ := by
  have h3 := FaceSmoother.gaussianThirdConstant_pos
  have he : 0 ≤ (8 : ℝ) * Real.exp 4 + 4 := by positivity
  unfold sharpMasterAssemblyConstant
  linarith

/-- Actual Gaussian fourth-derivative integral caps imply the exact sharp
rectangle-error master estimate. The cubic Gaussian estimate, comparison,
FTC, endpoint smoothing and all-rectangle extension are already proved. -/
theorem localMasterEstimate_of_gaussianFourthIntegralCap
    {C₄ : ℝ} (hC₄ : 0 ≤ C₄) (hcap : GaussianFourthIntegralCap.{u} C₄) :
    LocalMasterEstimate.{u} (sharpMasterAssemblyConstant C₄) := by
  intro Ω _ μ _ p n hp hn ξ δ A hdata hlocal hA R h hband
  let Q := covariance μ (sumVector ξ)
  let L := dimensionLog p
  let c := pairGap Q
  let a₃ := a3 Q
  let a₄ := a4 Q
  let cost := c * a₃ * a₄
  have hc : 0 < c := hlocal.pairGap_pos hp
  have ha₃ : 0 < a₃ := hlocal.a3_pos hp
  have ha₄ : 0 < a₄ := hlocal.a4_pos
  have hcost : 0 < cost := mul_pos (mul_pos hc ha₃) ha₄
  have hδ : 0 < δ := hdata.delta_pos hp hlocal.unit_diagonal
  have hh : 0 < h := by linarith only [hband, hδ]
  have hL : 0 < L := lt_of_lt_of_le (by norm_num) (log_exp_mul_nat_ge_one hp)
  have hLsqrt : 0 ≤ Real.sqrt L := Real.sqrt_nonneg _
  let T₃ := gamma3 μ ξ * L * Real.sqrt L / (c * a₃)
  let T₄ := gamma4 μ ξ * L * Real.sqrt L / (h * Real.rpow cost (2 / 3 : ℝ))
  let T₀ := h * Real.sqrt L / c
  have hT₃ : 0 ≤ T₃ := div_nonneg
    (mul_nonneg (mul_nonneg (gamma3_nonneg μ ξ) hL.le) hLsqrt) (mul_pos hc ha₃).le
  have hT₄ : 0 ≤ T₄ := div_nonneg
    (mul_nonneg (mul_nonneg (gamma4_nonneg μ ξ) hL.le) hLsqrt)
    (mul_pos hh (Real.rpow_pos_of_pos hcost _)).le
  have hT₀ : 0 ≤ T₀ := div_nonneg (mul_nonneg hh.le hLsqrt) hc.le
  change rectangleError μ (sumVector ξ) A R ≤ sharpMasterAssemblyConstant C₄ * (T₃ + T₄ + T₀)
  by_cases hsmall : h * Real.sqrt L ≤ 1
  · apply rectangleError_le_of_closedBox hp μ (sumVector ξ) hdata.measurable_sum A _ R
    intro lo hi
    let s := FaceSmoother.closedBox lo hi h hh
    have h3 := s.integral_time_mul_sharpThirdAverage_le μ ξ hdata.measurable hp A hlocal hA
    have h4 := hcap μ p n hp hn ξ δ A hdata hlocal hA s hband hsmall
    have hgap := s.interpolation_smoother_gap_le_sharpTimeIntegrals μ ξ hdata A hA
    have hb : δ ≤ h := by linarith only [hband, hdata.delta_nonneg]
    have herr := hdata.closedBox_error_le_smoother_gap hp hlocal.unit_diagonal A hA hc lo hi hh hb
    have hI := add_le_add
      (mul_le_mul_of_nonneg_left h3 (div_nonneg (gamma3_nonneg μ ξ) (show (0 : ℝ) ≤ 3 by norm_num)))
      (mul_le_mul_of_nonneg_left h4 (mul_nonneg (show (0 : ℝ) ≤ 6 by norm_num) (gamma4_nonneg μ ξ)))
    have hraw := herr.trans (add_le_add_right (hgap.trans hI) _)
    have hraw' : rectangleError μ (sumVector ξ) A (Rect.closedBox lo hi) ≤
        ((2 : ℝ) / 3 * FaceSmoother.gaussianThirdConstant) * T₃ +
          (6 * C₄) * T₄ + (8 * Real.exp 4 + 4) * T₀ := by
      convert hraw using 1; dsimp [s, FaceSmoother.closedBox, T₃, T₄, T₀, L, c, a₃, a₄, cost, Q]; ring
    have hK3 : (2 : ℝ) / 3 * FaceSmoother.gaussianThirdConstant ≤ sharpMasterAssemblyConstant C₄ := by
      have hpos := FaceSmoother.gaussianThirdConstant_pos
      have he : 0 ≤ (8 : ℝ) * Real.exp 4 + 4 := by positivity
      unfold sharpMasterAssemblyConstant
      linarith
    have hK4 : 6 * C₄ ≤ sharpMasterAssemblyConstant C₄ := by
      have hpos := FaceSmoother.gaussianThirdConstant_pos
      have he : 0 ≤ (8 : ℝ) * Real.exp 4 + 4 := by positivity
      unfold sharpMasterAssemblyConstant
      linarith
    have hK0 : 8 * Real.exp 4 + 4 ≤ sharpMasterAssemblyConstant C₄ := by
      have hpos := FaceSmoother.gaussianThirdConstant_pos
      unfold sharpMasterAssemblyConstant
      linarith
    exact hraw'.trans ((add_le_add
      (add_le_add (mul_le_mul_of_nonneg_right hK3 hT₃)
        (mul_le_mul_of_nonneg_right hK4 hT₄)) (mul_le_mul_of_nonneg_right hK0 hT₀)).trans_eq (by ring))
  · have hT₀one : 1 ≤ T₀ := by
      apply (le_div_iff₀ hc).mpr
      have hc1 : c ≤ 1 := pairGap_le_one Q
      linarith only [hc1, le_of_lt (lt_of_not_ge hsmall)]
    have hsum : 1 ≤ T₃ + T₄ + T₀ := by linarith only [hT₃, hT₄, hT₀one]
    exact (rectangleError_le_one μ (sumVector ξ) A R).trans
      (one_le_mul_of_one_le_of_one_le (sharpMasterAssemblyConstant_ge_one hC₄) hsum)

/-- Conditional sharp main theorem from the single remaining explicit actual
fourth-derivative integral cap, with its analytic premise visible in the type. -/
theorem localRectangleCLTExists_of_gaussianFourthIntegralCap
    {C₄ : ℝ} (hC₄ : 0 ≤ C₄) (hcap : GaussianFourthIntegralCap.{u} C₄) :
    LocalRectangleCLTExists.{u} :=
  localRectangleCLTExists_of_master
    (zero_le_one.trans (sharpMasterAssemblyConstant_ge_one hC₄))
    (localMasterEstimate_of_gaussianFourthIntegralCap hC₄ hcap)


/-- A sufficient large-time Gaussian estimate for the actual
fourth-derivative suprema. It is required only above `h² L`; the completed
short-scale estimate controls smaller times. `gaussianFourthPointwiseCap`
proves it for an explicit universal constant in `GaussianFourthFinal.lean`. -/
def GaussianFourthPointwiseCap (C : ℝ) : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p n : ℕ), 1 ≤ p → 1 ≤ n →
    ∀ (ξ : Fin n → Ω → Vector p) (δ : ℝ)
      (A : Matrix (Fin p) (Fin p) ℝ),
      BoundedIndependentHypotheses μ ξ δ →
      LocalCovarianceHypotheses (covariance μ (sumVector ξ)) →
      A * A.transpose = covariance μ (sumVector ξ) →
      ∀ s : FaceSmoother p, 12 * δ ≤ s.bandwidth →
        s.bandwidth * Real.sqrt (dimensionLog p) ≤ 1 →
        ∀ t ∈ Ioo (0 : ℝ) 1, s.bandwidth ^ 2 * dimensionLog p ≤ t →
          s.sharpFourthAverage μ ξ A δ t ≤
            C / (pairGap (covariance μ (sumVector ξ)) *
              a3 (covariance μ (sumVector ξ)) * a4 (covariance μ (sumVector ξ))) *
              (dimensionLog p) ^ 2 * t ^ (-(3 / 2 : ℝ))

/-- The completed short-scale cap plus the explicit large-time Gaussian cap
supply the exact two-thirds covariance cost in the actual time integral. -/
theorem gaussianFourthIntegralCap_of_pointwise
    {C : ℝ}
    (hC : 75 * (Real.exp 2) ^ 5 * interpolationShortScaleConstant ≤ C)
    (hlarge : GaussianFourthPointwiseCap.{u} C) : GaussianFourthIntegralCap.{u} (3 * C) := by
  intro Ω _ μ _ p n hp hn ξ δ A hdata hlocal hA s hband hsmall
  let Q := covariance μ (sumVector ξ)
  let cost := pairGap Q * a3 Q * a4 Q
  have hc := hlocal.pairGap_pos hp
  have ha₃ := hlocal.a3_pos hp
  have ha₄ := hlocal.a4_pos
  have hcost : 0 < cost := mul_pos (mul_pos hc ha₃) ha₄
  have hc1 : pairGap Q ≤ 1 := pairGap_le_one Q
  have ha31 : a3 Q ≤ 1 := (a3_le_pairGap hp hlocal.posSemidef hlocal.unit_diagonal).trans hc1
  have ha41 : a4 Q ≤ 1 := (a4_le_a3 hp hlocal.posSemidef).trans ha31
  have hca : pairGap Q * a3 Q ≤ 1 := by
    simpa only [one_mul] using mul_le_mul hc1 ha31 ha₃.le (by norm_num : (0 : ℝ) ≤ 1)
  have hcost1 : cost ≤ 1 := by
    simpa only [one_mul] using mul_le_mul hca ha41 ha₄.le (by norm_num : (0 : ℝ) ≤ 1)
  have hK : 0 ≤ (75 : ℝ) * (Real.exp 2) ^ 5 * interpolationShortScaleConstant := by
    unfold interpolationShortScaleConstant
    positivity
  have hC0 : 0 ≤ C := hK.trans hC
  have hD : IntervalIntegrable (s.sharpFourthAverage μ ξ A δ) volume 0 1 :=
    (s.continuousOn_sharpFourthAverage μ ξ hdata.measurable A hdata.delta_nonneg).intervalIntegrable_of_Icc
      (by norm_num)
  have hsmallCap (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      s.sharpFourthAverage μ ξ A δ t ≤ C * Real.sqrt (dimensionLog p) / s.bandwidth ^ 3 :=
    (s.sharpFourthAverage_shortScale_le μ ξ hdata hp hlocal.unit_diagonal A hA hband ht.1.le ht.2.le).trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC (Real.sqrt_nonneg _))
        (pow_nonneg s.bandwidth_pos.le _))
  have hh := integral_fourth_time_le_of_covariance_cost hC0 hcost hcost1
    (log_exp_mul_nat_ge_one hp) s.bandwidth_pos hD hsmallCap
    (fun t ht hb => hlarge μ p n hp hn ξ δ A hdata hlocal hA s hband hsmall t ht hb)
  rw [FaceSmoother.rpow_three_halves_eq_mul_sqrt
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (log_exp_mul_nat_ge_one hp))] at hh
  convert hh using 1
  dsimp only [cost, Q, dimensionLog]
  simp only [Real.rpow_eq_pow]
  ring

/-- The sharp main target follows conditionally from the actual fourth-order
large-time Gaussian estimate. That explicit analytic cap remains an input. -/
theorem localRectangleCLTExists_of_gaussianFourthPointwiseCap
    {C : ℝ}
    (hC : 75 * (Real.exp 2) ^ 5 * interpolationShortScaleConstant ≤ C)
    (hlarge : GaussianFourthPointwiseCap.{u} C) : LocalRectangleCLTExists.{u} := by
  have hK : 0 ≤ (75 : ℝ) * (Real.exp 2) ^ 5 * interpolationShortScaleConstant := by
    unfold interpolationShortScaleConstant
    positivity
  exact localRectangleCLTExists_of_gaussianFourthIntegralCap
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (hK.trans hC))
    (gaussianFourthIntegralCap_of_pointwise hC hlarge)

end RectangleCLT
