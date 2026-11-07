import RectangleCLTCompanion.SplitV4.DirectFourthRestoration

/-! Actual independent-common-base averaging of restored fourth-copy
tensors. The product Fubini theorem is derived from genuine fibre moments
and the integrable smaller envelope, rather than assumed. -/

open MeasureTheory Set
open scoped BigOperators
namespace RectangleCLT.Companion.SplitV4
noncomputable section
set_option autoImplicit false

theorem integrable_smallerEnvelope_comp
    {Β : Type*} [MeasurableSpace Β] {p : ℕ}
    (ν : Measure Β) [IsFiniteMeasure ν] (s : FaceSmoother p)
    (X : Β → Vector p) (hX : Measurable X) :
    Integrable (fun β => s.F (X β)*(1-s.F (X β))) ν := by
  apply (integrable_const (1 : ℝ)).mono'
    (((s.continuous_F.mul (continuous_const.sub s.continuous_F)).measurable.comp hX).aestronglyMeasurable)
  filter_upwards [] with β
  simp only [Function.comp_apply, Real.norm_eq_abs]
  rw [abs_of_nonneg (mul_nonneg (s.F_pos _).le (sub_nonneg.mpr (s.F_le_one _)))]
  nlinarith [s.F_le_one (X β), (s.F_pos (X β)).le, sq_nonneg (s.F (X β))]

set_option maxHeartbeats 1000000 in
theorem sum_integral_norm_fourth_shift_copies_common_base_le
    {Β Ω : Type*} [MeasurableSpace Β] [MeasurableSpace Ω] {p n : ℕ}
    (ν : Measure Β) [IsFiniteMeasure ν] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {s₃ s₄ : ℝ} (h : RelativeMomentBounds μ ξ s₃ s₄)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1) (s : FaceSmoother p)
    (X : Β → Vector p) (hX : Measurable X)
    (v : Fin n → Β × (Ω × Ω) → Vector p) (hv : ∀ i, Measurable (v i))
    (hvb : ∀ i, ∀ᵐ z ∂ν.prod (μ.prod μ), ‖v i z‖ ≤ s.bandwidth) (b : Fin 4 → Bool) :
    (∀ i, Integrable (fun z : Β × (Ω × Ω) => iteratedFDeriv ℝ 4 s.F (X z.1+v i z)
      (fun a => directCopyVector ξ i (b a) z.2)) (ν.prod (μ.prod μ))) ∧
    (∑ i, ∫ z : Β × (Ω × Ω), ‖iteratedFDeriv ℝ 4 s.F (X z.1+v i z)
      (fun a => directCopyVector ξ i (b a) z.2)‖ ∂ν.prod (μ.prod μ)) ≤
      (fourthDerivativeEnvelopeConstant*s₄/s.bandwidth^4)*
        ∫ β, s.F (X β)*(1-s.F (X β)) ∂ν := by
  let D : Fin n → Β × (Ω × Ω) → ℝ := fun i z =>
    iteratedFDeriv ℝ 4 s.F (X z.1+v i z) (fun a => directCopyVector ξ i (b a) z.2)
  let I : Fin n → Β → ℝ := fun i β => ∫ z : Ω × Ω, ‖D i (β, z)‖ ∂μ.prod μ
  let E : Β → ℝ := fun β => s.F (X β)*(1-s.F (X β))
  let C : ℝ := fourthDerivativeEnvelopeConstant*s₄/s.bandwidth^4
  have hmD (i : Fin n) : Measurable (D i) := by
    have hc : Continuous (fun y : Vector p × (Fin 4 → Vector p) => iteratedFDeriv ℝ 4 s.F y.1 y.2) :=
      ((s.contDiff_F_translation.continuous_iteratedFDeriv (by simp)).comp continuous_fst).eval continuous_snd
    exact hc.measurable.comp (((hX.comp measurable_fst).add (hv i)).prodMk
      (measurable_pi_lambda _ (fun a => (measurable_directCopyVector ξ h.measurable i (b a)).comp measurable_snd)))
  have hiE : Integrable E ν := integrable_smallerEnvelope_comp ν s X hX
  have hgood : ∀ᵐ β ∂ν, ∀ i, ∀ᵐ z ∂μ.prod μ, ‖v i (β, z)‖ ≤ s.bandwidth :=
    ae_all_iff.mpr (fun i => Measure.ae_ae_of_ae_prod (hvb i))
  have hfibre : ∀ᵐ β ∂ν,
      (∀ i, Integrable (fun z : Ω × Ω => D i (β, z)) (μ.prod μ)) ∧
        (∑ i, I i β) ≤ C*E β := by
    filter_upwards [hgood] with β hβ
    have hm (i : Fin n) : Measurable (fun z : Ω × Ω => v i (β, z)) :=
      (hv i).comp (measurable_const.prodMk measurable_id)
    have he := sum_integral_norm_fourth_shift_copies_le μ ξ h hunit s (X β)
      (fun i z => v i (β, z)) hm hβ b
    refine ⟨he.1, he.2.trans_eq ?_⟩
    dsimp only [C, E]
    ring
  have hiI (i : Fin n) : Integrable (I i) ν := by
    apply (hiE.const_mul C).mono' ((hmD i).norm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable
    filter_upwards [hfibre] with β hβ
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    exact (Finset.single_le_sum (fun j _ => integral_nonneg (fun _ => norm_nonneg _)) (Finset.mem_univ i)).trans hβ.2
  have hiD (i : Fin n) : Integrable (D i) (ν.prod (μ.prod μ)) :=
    (integrable_prod_iff (hmD i).aestronglyMeasurable).mpr
      ⟨hfibre.mono (fun _ hβ => hβ.1 i), hiI i⟩
  refine ⟨hiD, ?_⟩
  calc
    _ = ∑ i, ∫ β, I i β ∂ν := Finset.sum_congr rfl (fun i _ => integral_prod _ (hiD i).norm)
    _ = ∫ β, ∑ i, I i β ∂ν := (integral_finset_sum _ (fun i _ => hiI i)).symm
    _ ≤ ∫ β, C*E β ∂ν :=
      integral_mono_ae (integrable_finset_sum _ (fun i _ => hiI i)) (hiE.const_mul C) (hfibre.mono (fun _ hβ => hβ.2))
    _ = _ := integral_const_mul _ _

end
end RectangleCLT.Companion.SplitV4
