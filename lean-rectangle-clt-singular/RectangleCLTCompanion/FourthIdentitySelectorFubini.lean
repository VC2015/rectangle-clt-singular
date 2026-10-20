import RectangleCLTCompanion.FourthIdentityFubini
import RectangleCLTCompanion.FourthIdentityFreshPairs

/-! Actual outer-interval representations of all three fourth-order
selector terms. The expectations use the base law and genuinely independent
fresh row copies through their concrete product measures. -/

open MeasureTheory
open scoped BigOperators Interval

namespace RectangleCLT.FaceSmoother

noncomputable section

variable {p : ℕ} (s : FaceSmoother p) (ν : Measure (Vector p)) [IsProbabilityMeasure ν]

private theorem base_interval_to_product
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
    ((∫ ω, (∫ η, (∫ r in (0 : ℝ)..1, K r *
      s.convolutionFourthTensor ν (line (W (ω, η)) (V (ω, η)) (a * r))
        (U₁ (ω, η)) (U₂ (ω, η)) (U₃ (ω, η)) (U₄ (ω, η))) ∂ρ) ∂μ) =
      ∫ r in (0 : ℝ)..1, K r * (∫ z,
        s.convolutionFourthTensor ν (line (W z) (V z) (a * r))
          (U₁ z) (U₂ z) (U₃ z) (U₄ z) ∂μ.prod ρ)) ∧
    IntervalIntegrable (fun r => K r * (∫ z,
      s.convolutionFourthTensor ν (line (W z) (V z) (a * r))
        (U₁ z) (U₂ z) (U₃ z) (U₄ z) ∂μ.prod ρ)) volume 0 1 := by
  have hi := s.integrable_convolutionFourthTensor_interval_prod ν (μ.prod ρ) W V U₁ U₂ U₃ U₄
    hW hV hU₁ hU₂ hU₃ hU₄ hδ hb₁ hb₂ hb₃ hb₄ a K hK
  constructor
  · calc
      _ = ∫ z, (∫ r in (0 : ℝ)..1, K r *
          s.convolutionFourthTensor ν (line (W z) (V z) (a * r))
            (U₁ z) (U₂ z) (U₃ z) (U₄ z)) ∂μ.prod ρ := by
        simpa only [intervalIntegral.integral_of_le zero_le_one] using
          (integral_prod _ hi.integral_prod_left).symm
      _ = _ := s.integral_interval_convolutionFourthTensor_swap ν (μ.prod ρ) W V U₁ U₂ U₃ U₄
        hW hV hU₁ hU₂ hU₃ hU₄ hδ hb₁ hb₂ hb₃ hb₄ a K hK
  · exact s.intervalIntegrable_integral_convolutionFourthTensor ν (μ.prod ρ) W V U₁ U₂ U₃ U₄
      hW hV hU₁ hU₂ hU₃ hU₄ hδ hb₁ hb₂ hb₃ hb₄ a K hK

private theorem interval_sum2 {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β → ℝ → ℝ) (c : α → β → ℝ) (K : ℝ → ℝ)
    (hi : ∀ i j, IntervalIntegrable (fun r => K r * f i j r) volume 0 1) :
    (∑ i, ∑ j, c i j * (∫ r in (0 : ℝ)..1, K r * f i j r)) =
      ∫ r in (0 : ℝ)..1, K r * ∑ i, ∑ j, c i j * f i j r := by
  classical
  have hinner (i : α) : (∑ j, c i j * (∫ r in (0 : ℝ)..1, K r * f i j r)) =
      ∫ r in (0 : ℝ)..1, ∑ j, c i j * (K r * f i j r) := by
    rw [intervalIntegral.integral_finset_sum (fun j _ => (hi i j).const_mul _)]
    simp only [intervalIntegral.integral_const_mul]
  simp_rw [hinner]
  have ho := intervalIntegral.integral_finset_sum (s := Finset.univ) (fun i _ =>
    IntervalIntegrable.sum Finset.univ (fun j _ => (hi i j).const_mul (c i j)))
  simp only [Finset.sum_apply] at ho
  rw [← ho]
  apply intervalIntegral.integral_congr
  intro r _
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Signed fourth-order A integrand with one actual independent fresh row. -/
def fourthPathIntegrandA {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (x : Vector p) (t r : ℝ) : ℝ :=
  ∑ i, ∑ mask, Kane.maskWeight (thinningProbability t) mask *
    ∫ z : Ω × Ω, s.convolutionFourthTensor ν
      (line (x + thinningScale t • maskObservationSum ξ (Function.update mask i false) z.1)
        (ξ i z.2) (thinningScale t * r)) (ξ i z.2) (ξ i z.2) (ξ i z.2) (ξ i z.2) ∂μ.prod μ

/-- Signed B integrand with the two independent fresh copies retained. -/
def fourthPathIntegrandB {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (x : Vector p) (t r : ℝ) : ℝ :=
  ∑ i, ∑ mask, Kane.maskWeight (thinningProbability t) mask *
    ∫ z : Ω × (Ω × Ω), s.convolutionFourthTensor ν
      (line (x + thinningScale t • maskObservationSum ξ (Function.update mask i false) z.1)
        (ξ i z.2.2) (thinningScale t * r))
      (ξ i z.2.1) (ξ i z.2.1) (ξ i z.2.2) (ξ i z.2.2) ∂μ.prod (μ.prod μ)

/-- Signed C integrand, with three occurrences of the first fresh copy. -/
def fourthPathIntegrandC {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (x : Vector p) (t r : ℝ) : ℝ :=
  ∑ i, ∑ mask, Kane.maskWeight (thinningProbability t) mask *
    ∫ z : Ω × (Ω × Ω), s.convolutionFourthTensor ν
      (line (x + thinningScale t • maskObservationSum ξ (Function.update mask i false) z.1)
        (ξ i z.2.2) (thinningScale t * r))
      (ξ i z.2.1) (ξ i z.2.1) (ξ i z.2.1) (ξ i z.2.2) ∂μ.prod (μ.prod μ)

theorem selectorFourthA_eq_interval_integral
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (x : Vector p) (t : ℝ) :
    s.selectorFourthA ν μ ξ x t =
      ∫ r in (0 : ℝ)..1, Companion.fourthKernel t r * s.fourthPathIntegrandA ν μ ξ x t r := by
  let f := fun (i : Fin n) (mask : Kane.Cube n) (r : ℝ) =>
    ∫ z : Ω × Ω, s.convolutionFourthTensor ν
      (line (x + thinningScale t • maskObservationSum ξ (Function.update mask i false) z.1)
        (ξ i z.2) (thinningScale t * r)) (ξ i z.2) (ξ i z.2) (ξ i z.2) (ξ i z.2) ∂μ.prod μ
  have hdata (i : Fin n) (mask : Kane.Cube n) :
      (∫ ω, s.fourthRowA ν μ (ξ i)
        (x + thinningScale t • maskObservationSum ξ (Function.update mask i false) ω) t ∂μ) =
        (∫ r in (0 : ℝ)..1, Companion.fourthKernel t r * f i mask r) ∧
      IntervalIntegrable (fun r => Companion.fourthKernel t r * f i mask r) volume 0 1 := by
    have hbase : Measurable (fun z : Ω × Ω =>
        x + thinningScale t • maskObservationSum ξ (Function.update mask i false) z.1) :=
      (measurable_const.add (measurable_const.smul
        (measurable_maskObservationSum ξ h.measurable _))).comp measurable_fst
    have hrow : Measurable (fun z : Ω × Ω => ξ i z.2) := (h.measurable i).comp measurable_snd
    have hb : ∀ᵐ z ∂μ.prod μ, ‖ξ i z.2‖ ≤ δ :=
      Measure.quasiMeasurePreserving_snd.ae (h.bounded i)
    simpa only [fourthRowA, convolutionTranslationD4, convolutionFourthTensor] using
      s.base_interval_to_product ν μ μ
        (fun z => x + thinningScale t • maskObservationSum ξ (Function.update mask i false) z.1)
        (fun z => ξ i z.2) (fun z => ξ i z.2) (fun z => ξ i z.2)
        (fun z => ξ i z.2) (fun z => ξ i z.2)
        hbase hrow hrow hrow hrow hrow h.delta_nonneg hb hb hb hb
        (thinningScale t) (Companion.fourthKernel t)
        (by unfold Companion.fourthKernel; fun_prop)
  unfold selectorFourthA
  simp_rw [(hdata _ _).1]
  exact interval_sum2 f (fun _ mask => Kane.maskWeight (thinningProbability t) mask)
    (Companion.fourthKernel t) (fun i mask => (hdata i mask).2)

theorem selectorFourthB_eq_interval_integral
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (x : Vector p) {t : ℝ} (ht : 0 ≤ t) :
    s.selectorFourthB ν μ ξ x t = (1 - t) / 2 *
      ∫ r in (0 : ℝ)..1, (1 - r) * s.fourthPathIntegrandB ν μ ξ x t r := by
  let f := fun (i : Fin n) (mask : Kane.Cube n) (r : ℝ) =>
    ∫ z : Ω × (Ω × Ω), s.convolutionFourthTensor ν
      (line (x + thinningScale t • maskObservationSum ξ (Function.update mask i false) z.1)
        (ξ i z.2.2) (thinningScale t * r))
      (ξ i z.2.1) (ξ i z.2.1) (ξ i z.2.2) (ξ i z.2.2) ∂μ.prod (μ.prod μ)
  have hdata (i : Fin n) (mask : Kane.Cube n) :
      ((∫ ω, (∫ z : Ω × Ω, (∫ r in (0 : ℝ)..1, (1 - r) *
        s.convolutionFourthTensor ν
          (line (x + thinningScale t • maskObservationSum ξ (Function.update mask i false) ω)
            (ξ i z.2) (thinningScale t * r))
          (ξ i z.1) (ξ i z.1) (ξ i z.2) (ξ i z.2)) ∂μ.prod μ) ∂μ) =
        ∫ r in (0 : ℝ)..1, (1 - r) * f i mask r) ∧
      IntervalIntegrable (fun r => (1 - r) * f i mask r) volume 0 1 := by
    have hbase : Measurable (fun z : Ω × (Ω × Ω) =>
        x + thinningScale t • maskObservationSum ξ (Function.update mask i false) z.1) :=
      (measurable_const.add (measurable_const.smul
        (measurable_maskObservationSum ξ h.measurable _))).comp measurable_fst
    have hrow₁ : Measurable (fun z : Ω × (Ω × Ω) => ξ i z.2.1) :=
      (h.measurable i).comp (measurable_fst.comp measurable_snd)
    have hrow₂ : Measurable (fun z : Ω × (Ω × Ω) => ξ i z.2.2) :=
      (h.measurable i).comp (measurable_snd.comp measurable_snd)
    have hb₁ : ∀ᵐ z ∂μ.prod (μ.prod μ), ‖ξ i z.2.1‖ ≤ δ :=
      Measure.quasiMeasurePreserving_snd.ae
        (Measure.quasiMeasurePreserving_fst.ae (h.bounded i))
    have hb₂ : ∀ᵐ z ∂μ.prod (μ.prod μ), ‖ξ i z.2.2‖ ≤ δ :=
      Measure.quasiMeasurePreserving_snd.ae
        (Measure.quasiMeasurePreserving_snd.ae (h.bounded i))
    exact s.base_interval_to_product ν μ (μ.prod μ)
      (fun z => x + thinningScale t • maskObservationSum ξ (Function.update mask i false) z.1)
      (fun z => ξ i z.2.2) (fun z => ξ i z.2.1) (fun z => ξ i z.2.1)
      (fun z => ξ i z.2.2) (fun z => ξ i z.2.2)
      hbase hrow₂ hrow₁ hrow₁ hrow₂ hrow₂ h.delta_nonneg hb₁ hb₁ hb₂ hb₂
      (thinningScale t) (fun r => 1 - r) (continuous_const.sub continuous_id)
  have heq (i : Fin n) (mask : Kane.Cube n) :
      (∫ ω, s.fourthRowB ν μ (ξ i)
        (x + thinningScale t • maskObservationSum ξ (Function.update mask i false) ω) t ∂μ) =
      (1 - t) / 2 * (∫ r in (0 : ℝ)..1, (1 - r) * f i mask r) := by
    simp_rw [s.fourthRowB_eq_freshPair ν μ (ξ i) (h.measurable i) (h.bounded i) _ ht]
    unfold fourthRowB_freshPair
    rw [integral_const_mul]
    exact congrArg (fun y => (1 - t) / 2 * y) (hdata i mask).1
  unfold selectorFourthB
  simp_rw [heq]
  calc
    _ = (1 - t) / 2 * (∑ i, ∑ mask,
        Kane.maskWeight (thinningProbability t) mask *
          (∫ r in (0 : ℝ)..1, (1 - r) * f i mask r)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro mask _
      ring
    _ = _ := congrArg (fun y => (1 - t) / 2 * y)
      (interval_sum2 f (fun _ mask => Kane.maskWeight (thinningProbability t) mask)
        (fun r => 1 - r) (fun i mask => (hdata i mask).2))

theorem selectorFourthC_eq_interval_integral
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (x : Vector p) {t : ℝ} (ht : 0 ≤ t) :
    s.selectorFourthC ν μ ξ x t = t * (1 - t) / (3 * (1 + t)) *
      ∫ r in (0 : ℝ)..1, s.fourthPathIntegrandC ν μ ξ x t r := by
  let f := fun (i : Fin n) (mask : Kane.Cube n) (r : ℝ) =>
    ∫ z : Ω × (Ω × Ω), s.convolutionFourthTensor ν
      (line (x + thinningScale t • maskObservationSum ξ (Function.update mask i false) z.1)
        (ξ i z.2.2) (thinningScale t * r))
      (ξ i z.2.1) (ξ i z.2.1) (ξ i z.2.1) (ξ i z.2.2) ∂μ.prod (μ.prod μ)
  have hdata (i : Fin n) (mask : Kane.Cube n) :
      ((∫ ω, (∫ z : Ω × Ω, (∫ r in (0 : ℝ)..1,
        s.convolutionFourthTensor ν
          (line (x + thinningScale t • maskObservationSum ξ (Function.update mask i false) ω)
            (ξ i z.2) (thinningScale t * r))
          (ξ i z.1) (ξ i z.1) (ξ i z.1) (ξ i z.2)) ∂μ.prod μ) ∂μ) =
        ∫ r in (0 : ℝ)..1, f i mask r) ∧
      IntervalIntegrable (f i mask) volume 0 1 := by
    have hbase : Measurable (fun z : Ω × (Ω × Ω) =>
        x + thinningScale t • maskObservationSum ξ (Function.update mask i false) z.1) :=
      (measurable_const.add (measurable_const.smul
        (measurable_maskObservationSum ξ h.measurable _))).comp measurable_fst
    have hrow₁ : Measurable (fun z : Ω × (Ω × Ω) => ξ i z.2.1) :=
      (h.measurable i).comp (measurable_fst.comp measurable_snd)
    have hrow₂ : Measurable (fun z : Ω × (Ω × Ω) => ξ i z.2.2) :=
      (h.measurable i).comp (measurable_snd.comp measurable_snd)
    have hb₁ : ∀ᵐ z ∂μ.prod (μ.prod μ), ‖ξ i z.2.1‖ ≤ δ :=
      Measure.quasiMeasurePreserving_snd.ae
        (Measure.quasiMeasurePreserving_fst.ae (h.bounded i))
    have hb₂ : ∀ᵐ z ∂μ.prod (μ.prod μ), ‖ξ i z.2.2‖ ≤ δ :=
      Measure.quasiMeasurePreserving_snd.ae
        (Measure.quasiMeasurePreserving_snd.ae (h.bounded i))
    simpa only [one_mul] using s.base_interval_to_product ν μ (μ.prod μ)
      (fun z => x + thinningScale t • maskObservationSum ξ (Function.update mask i false) z.1)
      (fun z => ξ i z.2.2) (fun z => ξ i z.2.1) (fun z => ξ i z.2.1)
      (fun z => ξ i z.2.1) (fun z => ξ i z.2.2)
      hbase hrow₂ hrow₁ hrow₁ hrow₁ hrow₂ h.delta_nonneg hb₁ hb₁ hb₁ hb₂
      (thinningScale t) (fun _ => 1) continuous_const
  have heq (i : Fin n) (mask : Kane.Cube n) :
      (∫ ω, s.fourthRowC ν μ (ξ i)
        (x + thinningScale t • maskObservationSum ξ (Function.update mask i false) ω) t ∂μ) =
      t * (1 - t) / (3 * (1 + t)) * (∫ r in (0 : ℝ)..1, f i mask r) := by
    simp_rw [s.fourthRowC_eq_freshPair ν μ (ξ i) (h.measurable i) (h.bounded i) _ ht]
    unfold fourthRowC_freshPair
    rw [integral_const_mul]
    exact congrArg (fun y => t * (1 - t) / (3 * (1 + t)) * y) (hdata i mask).1
  unfold selectorFourthC
  simp_rw [heq]
  calc
    _ = t * (1 - t) / (3 * (1 + t)) * (∑ i, ∑ mask,
        Kane.maskWeight (thinningProbability t) mask *
          (∫ r in (0 : ℝ)..1, f i mask r)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro mask _
      ring
    _ = _ := by
      apply congrArg (fun y => t * (1 - t) / (3 * (1 + t)) * y)
      simpa only [one_mul] using
        interval_sum2 f (fun _ mask => Kane.maskWeight (thinningProbability t) mask)
          (fun _ => 1) (fun i mask => by simpa only [one_mul] using (hdata i mask).2)

end
end RectangleCLT.FaceSmoother
