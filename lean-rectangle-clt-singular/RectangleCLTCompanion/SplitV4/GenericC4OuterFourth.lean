import RectangleCLTCompanion.SplitV4.GenericC4FourthIntegral

/-! The genuine outer interval fourth remainder for a generic C4 test.
The base, Gaussian, and two fresh row copies all appear in the actual
product integral; no conditional or integrability identity is assumed. -/

open MeasureTheory
open scoped BigOperators Interval

namespace RectangleCLT.Companion.SplitV4
noncomputable section

def genericFourthPathIntegrand {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ν : Measure (Vector p)) (F : Vector p → ℝ)
    (ξ : Fin n → Ω → Vector p) (x : Vector p) (q a σ c b d r : ℝ) : ℝ :=
  ∑ i, ∑ mask : Kane.Cube n, Kane.maskWeight q mask *
    ∫ z : (Vector p × Ω) × (Ω × Ω),
      genericFourthCombination F
        (x+σ • z.1.1+a • maskObservationSum ξ (Function.update mask i false) z.1.2)
        (ξ i z.2.1) (ξ i z.2.2) q a c b d r ∂(ν.prod μ).prod (μ.prod μ)

theorem genericFourthPath_row_data
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure (Vector p)) [IsFiniteMeasure ν]
    {F : Vector p → ℝ} (hF : ContDiff ℝ 4 F) {C δ : ℝ} (hC : 0 ≤ C)
    (hjet : ∀ x, ‖iteratedFDeriv ℝ 4 F x‖ ≤ C)
    (ξ : Fin n → Ω → Vector p) (h : BoundedIndependentHypotheses μ ξ δ)
    (i : Fin n) (mask : Kane.Cube n) (x : Vector p) (q a σ c b d : ℝ) :
    Integrable (fun g => ∫ ω, genericRowFourthTotal μ F (ξ i)
      (x+σ • g+a • maskObservationSum ξ (Function.update mask i false) ω) q a c b d ∂μ) ν ∧
    IntervalIntegrable (fun r => ∫ z : (Vector p × Ω) × (Ω × Ω),
      genericFourthCombination F
        (x+σ • z.1.1+a • maskObservationSum ξ (Function.update mask i false) z.1.2)
        (ξ i z.2.1) (ξ i z.2.2) q a c b d r ∂(ν.prod μ).prod (μ.prod μ)) volume 0 1 ∧
    (∫ g, (∫ ω, genericRowFourthTotal μ F (ξ i)
      (x+σ • g+a • maskObservationSum ξ (Function.update mask i false) ω) q a c b d ∂μ) ∂ν) =
      ∫ r in (0 : ℝ)..1, (∫ z : (Vector p × Ω) × (Ω × Ω),
        genericFourthCombination F
          (x+σ • z.1.1+a • maskObservationSum ξ (Function.update mask i false) z.1.2)
          (ξ i z.2.1) (ξ i z.2.2) q a c b d r ∂(ν.prod μ).prod (μ.prod μ)) := by
  let W := fun z : Vector p × Ω => x+σ • z.1+a • maskObservationSum ξ (Function.update mask i false) z.2
  have hW : Measurable W :=
    (measurable_const.add (measurable_const.smul measurable_fst)).add
      (measurable_const.smul ((measurable_maskObservationSum ξ h.measurable _).comp measurable_snd))
  have hd := integral_genericRowFourthTotal_eq_interval (ν.prod μ) μ hF hC h.delta_nonneg hjet
    W hW (ξ i) (h.measurable i) (h.bounded i) q a c b d
  exact ⟨hd.1.integral_prod_left, hd.2.1, (integral_prod _ hd.1).symm.trans hd.2.2⟩

theorem genericSelectorFourthRemainder_outer_interval
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure (Vector p)) [IsFiniteMeasure ν]
    {F : Vector p → ℝ} (hF : ContDiff ℝ 4 F) {C δ : ℝ} (hC : 0 ≤ C)
    (hjet : ∀ x, ‖iteratedFDeriv ℝ 4 F x‖ ≤ C)
    (ξ : Fin n → Ω → Vector p) (h : BoundedIndependentHypotheses μ ξ δ)
    (x : Vector p) (q a σ c b d : ℝ) :
    Integrable (fun g => genericSelectorFourthRemainder μ F ξ (x+σ • g) q a c b d) ν ∧
    IntervalIntegrable (genericFourthPathIntegrand μ ν F ξ x q a σ c b d) volume 0 1 ∧
    (∫ g, genericSelectorFourthRemainder μ F ξ (x+σ • g) q a c b d ∂ν) =
      ∫ r in (0 : ℝ)..1, genericFourthPathIntegrand μ ν F ξ x q a σ c b d r := by
  let J := fun (i : Fin n) (mask : Kane.Cube n) (g : Vector p) => ∫ ω,
    genericRowFourthTotal μ F (ξ i)
      (x+σ • g+a • maskObservationSum ξ (Function.update mask i false) ω) q a c b d ∂μ
  let K := fun (i : Fin n) (mask : Kane.Cube n) (r : ℝ) =>
    ∫ z : (Vector p × Ω) × (Ω × Ω), genericFourthCombination F
      (x+σ • z.1.1+a • maskObservationSum ξ (Function.update mask i false) z.1.2)
      (ξ i z.2.1) (ξ i z.2.2) q a c b d r ∂(ν.prod μ).prod (μ.prod μ)
  have hd (i : Fin n) (mask : Kane.Cube n) :=
    genericFourthPath_row_data μ ν hF hC hjet ξ h i mask x q a σ c b d
  have hJ (i : Fin n) (mask : Kane.Cube n) : Integrable (J i mask) ν := (hd i mask).1
  have hK (i : Fin n) (mask : Kane.Cube n) : IntervalIntegrable (K i mask) volume 0 1 := (hd i mask).2.1
  have he (i : Fin n) (mask : Kane.Cube n) : (∫ g, J i mask g ∂ν) = ∫ r in (0 : ℝ)..1, K i mask r := (hd i mask).2.2
  have hinner (i : Fin n) : IntervalIntegrable
      (fun r => ∑ mask : Kane.Cube n, Kane.maskWeight q mask*K i mask r) volume 0 1 := by
    have hh := IntervalIntegrable.sum (f := fun mask r => Kane.maskWeight q mask*K i mask r)
      Finset.univ (fun mask _ => (hK i mask).const_mul (Kane.maskWeight q mask))
    have hf : (∑ mask : Kane.Cube n, fun r => Kane.maskWeight q mask*K i mask r) =
        (fun r => ∑ mask : Kane.Cube n, Kane.maskWeight q mask*K i mask r) := by
      funext r
      exact Finset.sum_apply r Finset.univ _
    rw [hf] at hh
    exact hh
  refine ⟨?_, ?_, ?_⟩
  · exact integrable_finset_sum _ (fun i _ => integrable_finset_sum _
      (fun mask _ => (hJ i mask).const_mul (Kane.maskWeight q mask)))
  · have hh := IntervalIntegrable.sum
      (f := fun i r => ∑ mask : Kane.Cube n, Kane.maskWeight q mask*K i mask r)
      Finset.univ (fun i _ => hinner i)
    have hf : (∑ i : Fin n, fun r => ∑ mask : Kane.Cube n, Kane.maskWeight q mask*K i mask r) =
        genericFourthPathIntegrand μ ν F ξ x q a σ c b d := by
      funext r
      exact Finset.sum_apply r Finset.univ _
    rw [hf] at hh
    exact hh
  · change (∫ g, ∑ i, ∑ mask : Kane.Cube n, Kane.maskWeight q mask*J i mask g ∂ν) =
      ∫ r in (0 : ℝ)..1, ∑ i, ∑ mask : Kane.Cube n, Kane.maskWeight q mask*K i mask r
    rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _
      (fun mask _ => (hJ i mask).const_mul (Kane.maskWeight q mask)))]
    simp_rw [integral_finset_sum _ (fun mask _ => (hJ _ mask).const_mul (Kane.maskWeight q mask)), integral_const_mul, he]
    rw [intervalIntegral.integral_finset_sum (fun i _ => hinner i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [intervalIntegral.integral_finset_sum (fun mask _ => (hK i mask).const_mul (Kane.maskWeight q mask))]
    simp only [intervalIntegral.integral_const_mul]

end
end RectangleCLT.Companion.SplitV4
