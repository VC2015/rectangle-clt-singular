import RectangleCLTCompanion.FourthIdentityFresh

/-! Genuine Fubini for the fourth-order identity. The sample-dependent base
and translation may be unbounded. Only the four row directions are bounded;
the checked global fourth-derivative bound supplies joint integrability. -/

open MeasureTheory
open scoped BigOperators Interval

namespace RectangleCLT.FaceSmoother

noncomputable section

variable {p : ℕ} (s : FaceSmoother p) (ν : Measure (Vector p)) [IsProbabilityMeasure ν]

/-- Joint absolute integrability on the actual sample--interval product,
including four distinct row directions and an arbitrary measurable base. -/
theorem integrable_convolutionFourthTensor_interval_prod
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (W V U₁ U₂ U₃ U₄ : Ω → Vector p)
    (hW : Measurable W) (hV : Measurable V)
    (hU₁ : Measurable U₁) (hU₂ : Measurable U₂)
    (hU₃ : Measurable U₃) (hU₄ : Measurable U₄)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hb₁ : ∀ᵐ ω ∂μ, ‖U₁ ω‖ ≤ δ) (hb₂ : ∀ᵐ ω ∂μ, ‖U₂ ω‖ ≤ δ)
    (hb₃ : ∀ᵐ ω ∂μ, ‖U₃ ω‖ ≤ δ) (hb₄ : ∀ᵐ ω ∂μ, ‖U₄ ω‖ ≤ δ)
    (a : ℝ) (K : ℝ → ℝ) (hK : Continuous K) :
    Integrable (fun y : Ω × ℝ => K y.2 *
      s.convolutionFourthTensor ν (line (W y.1) (V y.1) (a * y.2))
        (U₁ y.1) (U₂ y.1) (U₃ y.1) (U₄ y.1))
      (μ.prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) := by
  obtain ⟨C₀, hC₀⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).bddAbove_image
    hK.norm.continuousOn
  let C : ℝ := max 0 C₀
  have hC : 0 ≤ C := le_max_left _ _
  have hKb (r : ℝ) (hr : r ∈ Set.Ioc (0 : ℝ) 1) : ‖K r‖ ≤ C :=
    (hC₀ (Set.mem_image_of_mem _ ⟨hr.1.le, hr.2⟩)).trans (le_max_right _ _)
  have hline : Measurable (fun y : Ω × ℝ => line (W y.1) (V y.1) (a * y.2)) := by
    change Measurable (fun y : Ω × ℝ => W y.1 + (a * y.2) • V y.1)
    exact (hW.comp measurable_fst).add
      ((measurable_const.mul measurable_snd).smul (hV.comp measurable_fst))
  unfold convolutionFourthTensor
  simp only [Finset.mul_sum]
  apply integrable_finset_sum
  intro j _
  apply integrable_finset_sum
  intro k _
  apply integrable_finset_sum
  intro l _
  apply integrable_finset_sum
  intro m _
  apply (integrable_const (C * (75 / s.bandwidth ^ 4) * δ * δ * δ * δ)).mono'
  · have hd := (s.continuous_convolutionFourthDerivative_commonPoint ν j k l m).measurable.comp hline
    have hu₁ : Measurable (fun y : Ω × ℝ => U₁ y.1 j) :=
      (measurable_pi_apply j).comp (hU₁.comp measurable_fst)
    have hu₂ : Measurable (fun y : Ω × ℝ => U₂ y.1 k) :=
      (measurable_pi_apply k).comp (hU₂.comp measurable_fst)
    have hu₃ : Measurable (fun y : Ω × ℝ => U₃ y.1 l) :=
      (measurable_pi_apply l).comp (hU₃.comp measurable_fst)
    have hu₄ : Measurable (fun y : Ω × ℝ => U₄ y.1 m) :=
      (measurable_pi_apply m).comp (hU₄.comp measurable_fst)
    exact ((hK.measurable.comp measurable_snd).mul
      ((((hd.mul hu₁).mul hu₂).mul hu₃).mul hu₄)).aestronglyMeasurable
  · filter_upwards [Measure.quasiMeasurePreserving_fst.ae hb₁,
      Measure.quasiMeasurePreserving_fst.ae hb₂, Measure.quasiMeasurePreserving_fst.ae hb₃,
      Measure.quasiMeasurePreserving_fst.ae hb₄,
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioc)]
      with y hy₁ hy₂ hy₃ hy₄ hyr
    have hu₁ := (norm_le_pi_norm (U₁ y.1) j).trans hy₁
    have hu₂ := (norm_le_pi_norm (U₂ y.1) k).trans hy₂
    have hu₃ := (norm_le_pi_norm (U₃ y.1) l).trans hy₃
    have hu₄ := (norm_le_pi_norm (U₄ y.1) m).trans hy₄
    have hD : 0 ≤ 75 / s.bandwidth ^ 4 := by positivity
    have hh := mul_le_mul (hKb y.2 hyr)
      (s.norm_convolutionFourthDerivative_le ν
        (line (W y.1) (V y.1) (a * y.2)) j k l m)
      (norm_nonneg _) hC
    have hh₁ := mul_le_mul hh hu₁ (norm_nonneg _) (mul_nonneg hC hD)
    have hh₂ := mul_le_mul hh₁ hu₂ (norm_nonneg _) (mul_nonneg (mul_nonneg hC hD) hδ)
    have hh₃ := mul_le_mul hh₂ hu₃ (norm_nonneg _)
      (mul_nonneg (mul_nonneg (mul_nonneg hC hD) hδ) hδ)
    have hh₄ := mul_le_mul hh₃ hu₄ (norm_nonneg _)
      (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC hD) hδ) hδ) hδ)
    simpa only [norm_mul, mul_assoc] using hh₄

/-- The interpolation interval can genuinely be put outside the row/base
expectation. All joint integrability is discharged from bounded row data. -/
theorem integral_interval_convolutionFourthTensor_swap
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (W V U₁ U₂ U₃ U₄ : Ω → Vector p)
    (hW : Measurable W) (hV : Measurable V)
    (hU₁ : Measurable U₁) (hU₂ : Measurable U₂)
    (hU₃ : Measurable U₃) (hU₄ : Measurable U₄)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hb₁ : ∀ᵐ ω ∂μ, ‖U₁ ω‖ ≤ δ) (hb₂ : ∀ᵐ ω ∂μ, ‖U₂ ω‖ ≤ δ)
    (hb₃ : ∀ᵐ ω ∂μ, ‖U₃ ω‖ ≤ δ) (hb₄ : ∀ᵐ ω ∂μ, ‖U₄ ω‖ ≤ δ)
    (a : ℝ) (K : ℝ → ℝ) (hK : Continuous K) :
    (∫ ω, (∫ r in (0 : ℝ)..1, K r *
      s.convolutionFourthTensor ν (line (W ω) (V ω) (a * r))
        (U₁ ω) (U₂ ω) (U₃ ω) (U₄ ω)) ∂μ) =
    ∫ r in (0 : ℝ)..1, K r * (∫ ω,
      s.convolutionFourthTensor ν (line (W ω) (V ω) (a * r))
        (U₁ ω) (U₂ ω) (U₃ ω) (U₄ ω) ∂μ) := by
  have hi := s.integrable_convolutionFourthTensor_interval_prod ν μ W V U₁ U₂ U₃ U₄
    hW hV hU₁ hU₂ hU₃ hU₄ hδ hb₁ hb₂ hb₃ hb₄ a K hK
  have hs := integral_integral_swap (μ := μ)
    (ν := volume.restrict (Set.Ioc (0 : ℝ) 1))
    (f := fun ω r => K r *
      s.convolutionFourthTensor ν (line (W ω) (V ω) (a * r))
        (U₁ ω) (U₂ ω) (U₃ ω) (U₄ ω)) hi
  simpa only [intervalIntegral.integral_of_le zero_le_one, integral_const_mul] using hs

/-- Integrability of the outer interval integrand, needed when exchanging
the interval integral with the finite observation and selector sums. -/
theorem intervalIntegrable_integral_convolutionFourthTensor
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (W V U₁ U₂ U₃ U₄ : Ω → Vector p)
    (hW : Measurable W) (hV : Measurable V)
    (hU₁ : Measurable U₁) (hU₂ : Measurable U₂)
    (hU₃ : Measurable U₃) (hU₄ : Measurable U₄)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hb₁ : ∀ᵐ ω ∂μ, ‖U₁ ω‖ ≤ δ) (hb₂ : ∀ᵐ ω ∂μ, ‖U₂ ω‖ ≤ δ)
    (hb₃ : ∀ᵐ ω ∂μ, ‖U₃ ω‖ ≤ δ) (hb₄ : ∀ᵐ ω ∂μ, ‖U₄ ω‖ ≤ δ)
    (a : ℝ) (K : ℝ → ℝ) (hK : Continuous K) :
    IntervalIntegrable (fun r => K r * (∫ ω,
      s.convolutionFourthTensor ν (line (W ω) (V ω) (a * r))
        (U₁ ω) (U₂ ω) (U₃ ω) (U₄ ω) ∂μ)) volume 0 1 := by
  have hi := s.integrable_convolutionFourthTensor_interval_prod ν μ W V U₁ U₂ U₃ U₄
    hW hV hU₁ hU₂ hU₃ hU₄ hδ hb₁ hb₂ hb₃ hb₄ a K hK
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  simpa only [integral_const_mul] using hi.integral_prod_right

/-- A base and its fresh rows may be kept as separate actual probability
integrals. No independence claim is needed for this analytic Fubini step. -/
theorem integral_integral_interval_convolutionFourthTensor_swap
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) [IsFiniteMeasure μ] (ρ : Measure Ξ) [IsFiniteMeasure ρ]
    (W V U₁ U₂ U₃ U₄ : Ω × Ξ → Vector p)
    (hW : Measurable W) (hV : Measurable V)
    (hU₁ : Measurable U₁) (hU₂ : Measurable U₂)
    (hU₃ : Measurable U₃) (hU₄ : Measurable U₄)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hb₁ : ∀ᵐ ω ∂μ.prod ρ, ‖U₁ ω‖ ≤ δ) (hb₂ : ∀ᵐ ω ∂μ.prod ρ, ‖U₂ ω‖ ≤ δ)
    (hb₃ : ∀ᵐ ω ∂μ.prod ρ, ‖U₃ ω‖ ≤ δ) (hb₄ : ∀ᵐ ω ∂μ.prod ρ, ‖U₄ ω‖ ≤ δ)
    (a : ℝ) (K : ℝ → ℝ) (hK : Continuous K) :
    (∫ ω, (∫ η, (∫ r in (0 : ℝ)..1, K r *
      s.convolutionFourthTensor ν (line (W (ω, η)) (V (ω, η)) (a * r))
        (U₁ (ω, η)) (U₂ (ω, η)) (U₃ (ω, η)) (U₄ (ω, η))) ∂ρ) ∂μ) =
    ∫ r in (0 : ℝ)..1, K r * (∫ ω, (∫ η,
      s.convolutionFourthTensor ν (line (W (ω, η)) (V (ω, η)) (a * r))
        (U₁ (ω, η)) (U₂ (ω, η)) (U₃ (ω, η)) (U₄ (ω, η)) ∂ρ) ∂μ) := by
  have hi := s.integrable_convolutionFourthTensor_interval_prod ν (μ.prod ρ) W V U₁ U₂ U₃ U₄
    hW hV hU₁ hU₂ hU₃ hU₄ hδ hb₁ hb₂ hb₃ hb₄ a K hK
  simp only [intervalIntegral.integral_of_le zero_le_one]
  calc
    _ = ∫ z, (∫ r in Set.Ioc (0 : ℝ) 1, K r *
        s.convolutionFourthTensor ν (line (W z) (V z) (a * r))
          (U₁ z) (U₂ z) (U₃ z) (U₄ z)) ∂μ.prod ρ :=
      (integral_prod _ hi.integral_prod_left).symm
    _ = ∫ r in Set.Ioc (0 : ℝ) 1, (∫ z, K r *
        s.convolutionFourthTensor ν (line (W z) (V z) (a * r))
          (U₁ z) (U₂ z) (U₃ z) (U₄ z) ∂μ.prod ρ) :=
      integral_integral_swap (f := fun z r => K r *
        s.convolutionFourthTensor ν (line (W z) (V z) (a * r))
          (U₁ z) (U₂ z) (U₃ z) (U₄ z)) hi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hi.prod_left_ae] with r hr
      simpa only [integral_const_mul] using integral_prod (fun z => K r *
        s.convolutionFourthTensor ν (line (W z) (V z) (a * r))
          (U₁ z) (U₂ z) (U₃ z) (U₄ z)) hr

/-- Repeated-row form of the same genuine Fubini theorem. -/
theorem integral_interval_convolutionTranslationD4_swap
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (W V U : Ω → Vector p) (hW : Measurable W) (hV : Measurable V) (hU : Measurable U)
    {δ : ℝ} (hδ : 0 ≤ δ) (hb : ∀ᵐ ω ∂μ, ‖U ω‖ ≤ δ)
    (a : ℝ) (K : ℝ → ℝ) (hK : Continuous K) :
    (∫ ω, (∫ r in (0 : ℝ)..1, K r *
      s.convolutionTranslationD4 ν (line (W ω) (V ω) (a * r)) (U ω)) ∂μ) =
    ∫ r in (0 : ℝ)..1, K r * (∫ ω,
      s.convolutionTranslationD4 ν (line (W ω) (V ω) (a * r)) (U ω) ∂μ) := by
  simpa only [convolutionFourthTensor, convolutionTranslationD4] using
    s.integral_interval_convolutionFourthTensor_swap ν μ W V U U U U
      hW hV hU hU hU hU hδ hb hb hb hb a K hK

/-- The actual repeated-row remainder has an outer interval integral, with
the row expectation inside exactly as required by restoration estimates. -/
theorem fourthRowA_eq_intervalIntegral
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (ξ : Ω → Vector p) (hξ : Measurable ξ)
    {δ : ℝ} (hδ : 0 ≤ δ) (hb : ∀ᵐ ω ∂μ, ‖ξ ω‖ ≤ δ)
    (x : Vector p) (t : ℝ) :
    s.fourthRowA ν μ ξ x t =
      ∫ r in (0 : ℝ)..1, Companion.fourthKernel t r * (∫ ω,
        s.convolutionTranslationD4 ν
          (line x (ξ ω) (thinningScale t * r)) (ξ ω) ∂μ) := by
  exact s.integral_interval_convolutionTranslationD4_swap ν μ (fun _ => x) ξ ξ
    measurable_const hξ hξ hδ hb (thinningScale t) (Companion.fourthKernel t)
    (by unfold Companion.fourthKernel; fun_prop)

end
end RectangleCLT.FaceSmoother
