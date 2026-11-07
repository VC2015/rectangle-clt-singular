import RectangleCLTCompanion.SplitV4.GenericC4Interpolation

/-! Genuine moment integrability and one-row Taylor identities for an
arbitrary actual C4 function. No value boundedness or remainder identity is
assumed. -/

open MeasureTheory
open scoped BigOperators Interval

namespace RectangleCLT.Companion.SplitV4
noncomputable section

theorem integrable_canonical_derivative_eval
    {Ω : Type*} [MeasurableSpace Ω] {p k : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] {F : Vector p → ℝ} (hF : ContDiff ℝ 4 F)
    (hk : k ≤ 4) (W : Ω → Vector p) (hW : Measurable W)
    (U : Fin k → Ω → Vector p) (hU : ∀ i, Measurable (U i))
    {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hjet : ∀ x, ‖iteratedFDeriv ℝ k F x‖ ≤ C)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, ‖U i ω‖ ≤ δ) :
    Integrable (fun ω => iteratedFDeriv ℝ k F (W ω) (fun i => U i ω)) μ := by
  borelize (ContinuousMultilinearMap ℝ (fun _ : Fin k => Vector p) ℝ)
  have hEval : Continuous (fun z :
      (ContinuousMultilinearMap ℝ (fun _ : Fin k => Vector p) ℝ) × (Fin k → Vector p) => z.1 z.2) :=
    continuous_fst.eval continuous_snd
  have hm : Measurable (fun ω => iteratedFDeriv ℝ k F (W ω) (fun i => U i ω)) :=
    hEval.measurable.comp (((hF.continuous_iteratedFDeriv (m := k) (by exact_mod_cast hk)).measurable.comp hW).prodMk
      (measurable_pi_lambda _ hU))
  apply (integrable_const (C*δ^k)).mono' hm.aestronglyMeasurable
  filter_upwards [ae_all_iff.mpr hbound] with ω hω
  calc
    _ ≤ ‖iteratedFDeriv ℝ k F (W ω)‖*∏ i, ‖U i ω‖ := (iteratedFDeriv ℝ k F (W ω)).le_opNorm _
    _ ≤ C*∏ _i : Fin k, δ := mul_le_mul (hjet _) (Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hω i))
      (Finset.prod_nonneg (fun i _ => norm_nonneg _)) hC
    _ = _ := by simp

theorem integrable_canonicalDiagonal_bounded
    {Ω : Type*} [MeasurableSpace Ω] {p k : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] {F : Vector p → ℝ} (hF : ContDiff ℝ 4 F)
    (hk : k ≤ 4) (W T : Ω → Vector p) (hW : Measurable W) (hT : Measurable T)
    {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hjet : ∀ x, ‖iteratedFDeriv ℝ k F x‖ ≤ C)
    (hbound : ∀ᵐ ω ∂μ, ‖T ω‖ ≤ δ) :
    Integrable (fun ω => canonicalDiagonal F k (W ω) (T ω)) μ :=
  integrable_canonical_derivative_eval μ hF hk W hW (fun _ => T) (fun _ => hT) hC hδ hjet (fun _ => hbound)

theorem integral_canonicalLinear_zero
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Vector p → ℝ)
    (T : Ω → Vector p) (hT : Measurable T) {δ : ℝ}
    (hbound : ∀ᵐ ω ∂μ, ‖T ω‖ ≤ δ)
    (hc : ∀ j, (∫ ω, T ω j ∂μ) = 0) (x : Vector p) :
    (∫ ω, canonicalDiagonal F 1 x (T ω) ∂μ) = 0 := by
  have hiT : Integrable T μ := (integrable_const δ).mono' hT.aestronglyMeasurable hbound
  have hmean : (∫ ω, T ω ∂μ) = 0 := by
    ext j
    have he := (ContinuousLinearMap.proj j : Vector p →L[ℝ] ℝ).integral_comp_comm hiT
    change (∫ ω, T ω j ∂μ) = (∫ ω, T ω ∂μ) j at he
    simpa only [hc j, Pi.zero_apply] using he.symm
  simp only [canonicalDiagonal, iteratedFDeriv_one_apply]
  rw [(fderiv ℝ F x).integral_comp_comm hiT, hmean, map_zero]

def genericValueTaylorPolynomial {p : ℕ} (F : Vector p → ℝ) (x v : Vector p) (a : ℝ) : ℝ :=
  F x+a*canonicalDiagonal F 1 x v+a^2/2*canonicalDiagonal F 2 x v+a^3/6*canonicalDiagonal F 3 x v

def genericGradientTaylorPolynomial {p : ℕ} (F : Vector p → ℝ) (x v : Vector p) (a : ℝ) : ℝ :=
  canonicalDiagonal F 1 x v+a*canonicalDiagonal F 2 x v+a^2/2*canonicalDiagonal F 3 x v

def genericRowFourthRemainder {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) (F : Vector p → ℝ) (T : Ω → Vector p) (x : Vector p) (a c b : ℝ) : ℝ :=
  ∫ ω, (∫ r in (0 : ℝ)..1, (c*a^4/6*(1-r)^3+b*a^3/2*(1-r)^2)*
    canonicalDiagonal F 4 (x+(a*r) • T ω) (T ω)) ∂μ

theorem generic_row_remainder_pointwise {p : ℕ} {F : Vector p → ℝ}
    (hF : ContDiff ℝ 4 F) (x v : Vector p) (a c b : ℝ) :
    c*(F (x+a • v)-genericValueTaylorPolynomial F x v a)+
      b*(canonicalDiagonal F 1 (x+a • v) v-genericGradientTaylorPolynomial F x v a) =
      ∫ r in (0 : ℝ)..1, (c*a^4/6*(1-r)^3+b*a^3/2*(1-r)^2)*
        canonicalDiagonal F 4 (x+(a*r) • v) v := by
  rw [genericValueTaylorPolynomial, genericGradientTaylorPolynomial,
    canonical_value_taylor_four hF, canonical_gradient_taylor_three hF]
  have hc : Continuous (fun r => canonicalDiagonal F 4 (x+(a*r) • v) v) :=
    ((hF.continuous_iteratedFDeriv (m := 4) (by norm_num)).comp
      (show Continuous (fun r : ℝ => x+(a*r) • v) by fun_prop)).eval continuous_const
  have hi0 : IntervalIntegrable (fun r : ℝ => a^4/6*(1-r)^3*canonicalDiagonal F 4 (x+(a*r) • v) v) volume 0 1 :=
    ((by fun_prop : Continuous (fun r : ℝ => a^4/6*(1-r)^3)).mul hc).intervalIntegrable 0 1
  have hi1 : IntervalIntegrable (fun r : ℝ => a^3/2*(1-r)^2*canonicalDiagonal F 4 (x+(a*r) • v) v) volume 0 1 :=
    ((by fun_prop : Continuous (fun r : ℝ => a^3/2*(1-r)^2)).mul hc).intervalIntegrable 0 1
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add (hi0.const_mul c) (hi1.const_mul b)]
  apply intervalIntegral.integral_congr
  intro r _
  ring

theorem integrable_canonicalValue_shifted_bounded
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] {F : Vector p → ℝ} (hF : ContDiff ℝ 4 F)
    {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hjet : ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ∀ x, ‖iteratedFDeriv ℝ k F x‖ ≤ C)
    (T : Ω → Vector p) (hT : Measurable T) (hbound : ∀ᵐ ω ∂μ, ‖T ω‖ ≤ δ)
    (x : Vector p) (a : ℝ) : Integrable (fun ω => F (x+a • T ω)) μ := by
  let f := C4Test.ofContDiff F hF C hC hjet
  have hpoint : Measurable (fun ω => x+a • T ω) := measurable_const.add (measurable_const.smul hT)
  have hi : Integrable (fun ω => ‖x+a • T ω‖) μ := by
    apply (integrable_const (‖x‖+|a| * δ)).mono' hpoint.norm.aestronglyMeasurable
    filter_upwards [hbound] with ω hω
    rw [norm_norm]
    exact (norm_add_le _ _).trans (add_le_add_left (by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left hω (abs_nonneg a)) _)
  exact f.integrable_value_of_norm μ _ hpoint hi

theorem genericRowTranslation_identity
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] {F : Vector p → ℝ} (hF : ContDiff ℝ 4 F)
    {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hjet : ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ∀ x, ‖iteratedFDeriv ℝ k F x‖ ≤ C)
    (T : Ω → Vector p) (hT : Measurable T) (hbound : ∀ᵐ ω ∂μ, ‖T ω‖ ≤ δ)
    (hc : ∀ j, (∫ ω, T ω j ∂μ) = 0) (x : Vector p) (a c b d : ℝ)
    (h2 : c*a^2/2+b*a = -(1/2 : ℝ)) (h3 : c*a^3/6+b*a^2/2 = d) :
    c*((∫ ω, F (x+a • T ω) ∂μ)-F x)+
      b*(∫ ω, canonicalDiagonal F 1 (x+a • T ω) (T ω) ∂μ) =
      -(1/2 : ℝ)*(∫ ω, canonicalDiagonal F 2 x (T ω) ∂μ)+
      d*(∫ ω, canonicalDiagonal F 3 x (T ω) ∂μ)+
      genericRowFourthRemainder μ F T x a c b := by
  let D1 : Ω → ℝ := fun ω => canonicalDiagonal F 1 x (T ω)
  let D2 : Ω → ℝ := fun ω => canonicalDiagonal F 2 x (T ω)
  let D3 : Ω → ℝ := fun ω => canonicalDiagonal F 3 x (T ω)
  let J1 : Ω → ℝ := fun ω => canonicalDiagonal F 1 (x+a • T ω) (T ω)
  have hpoint : Measurable (fun ω => x+a • T ω) := measurable_const.add (measurable_const.smul hT)
  have hi1 : Integrable D1 μ := integrable_canonicalDiagonal_bounded μ hF (by decide)
    (fun _ => x) T measurable_const hT hC hδ (hjet 1 (by decide) (by decide)) hbound
  have hi2 : Integrable D2 μ := integrable_canonicalDiagonal_bounded μ hF (by decide)
    (fun _ => x) T measurable_const hT hC hδ (hjet 2 (by decide) (by decide)) hbound
  have hi3 : Integrable D3 μ := integrable_canonicalDiagonal_bounded μ hF (by decide)
    (fun _ => x) T measurable_const hT hC hδ (hjet 3 (by decide) (by decide)) hbound
  have hj1 : Integrable J1 μ := integrable_canonicalDiagonal_bounded μ hF (by decide)
    (fun ω => x+a • T ω) T hpoint hT hC hδ (hjet 1 (by decide) (by decide)) hbound
  have hv := integrable_canonicalValue_shifted_bounded μ hF hC hδ hjet T hT hbound x a
  have hzero : (∫ ω, D1 ω ∂μ) = 0 := integral_canonicalLinear_zero μ F T hT hbound hc x
  let P0 : Ω → ℝ := fun ω => F x+a*D1 ω+a^2/2*D2 ω+a^3/6*D3 ω
  let P1 : Ω → ℝ := fun ω => D1 ω+a*D2 ω+a^2/2*D3 ω
  have hp0 : Integrable P0 μ := (((integrable_const _).add (hi1.const_mul a)).add
    (hi2.const_mul (a^2/2))).add (hi3.const_mul (a^3/6))
  have hp1 : Integrable P1 μ := (hi1.add (hi2.const_mul a)).add (hi3.const_mul (a^2/2))
  have ep0 : (∫ ω, P0 ω ∂μ) = F x+a^2/2*(∫ ω, D2 ω ∂μ)+a^3/6*(∫ ω, D3 ω ∂μ) := by
    unfold P0
    rw [integral_add (f := fun ω => F x+a*D1 ω+a^2/2*D2 ω) (g := fun ω => a^3/6*D3 ω)
      (((integrable_const _).add (hi1.const_mul a)).add (hi2.const_mul (a^2/2))) (hi3.const_mul (a^3/6)),
      integral_add (f := fun ω => F x+a*D1 ω) (g := fun ω => a^2/2*D2 ω)
        ((integrable_const _).add (hi1.const_mul a)) (hi2.const_mul (a^2/2)),
      integral_add (f := fun _ : Ω => F x) (g := fun ω => a*D1 ω) (integrable_const _) (hi1.const_mul a)]
    simp only [integral_const_mul, integral_const, measureReal_univ_eq_one, one_smul, hzero, mul_zero, add_zero]
  have ep1 : (∫ ω, P1 ω ∂μ) = a*(∫ ω, D2 ω ∂μ)+a^2/2*(∫ ω, D3 ω ∂μ) := by
    unfold P1
    rw [integral_add (f := fun ω => D1 ω+a*D2 ω) (g := fun ω => a^2/2*D3 ω)
      (hi1.add (hi2.const_mul a)) (hi3.const_mul (a^2/2)),
      integral_add (f := D1) (g := fun ω => a*D2 ω) hi1 (hi2.const_mul a)]
    simp only [integral_const_mul, hzero, zero_add]
  have hr0 : Integrable (fun ω => F (x+a • T ω)-P0 ω) μ := hv.sub hp0
  have hr1 : Integrable (fun ω => J1 ω-P1 ω) μ := hj1.sub hp1
  have er : genericRowFourthRemainder μ F T x a c b =
      c*((∫ ω, F (x+a • T ω) ∂μ)-(∫ ω, P0 ω ∂μ))+
        b*((∫ ω, J1 ω ∂μ)-(∫ ω, P1 ω ∂μ)) := by
    unfold genericRowFourthRemainder
    have he (ω : Ω) : (∫ r in (0 : ℝ)..1, (c*a^4/6*(1-r)^3+b*a^3/2*(1-r)^2)*
        canonicalDiagonal F 4 (x+(a*r) • T ω) (T ω)) =
        c*(F (x+a • T ω)-P0 ω)+b*(J1 ω-P1 ω) :=
      (generic_row_remainder_pointwise hF x (T ω) a c b).symm
    rw [integral_congr_ae (ae_of_all _ he),
      integral_add (f := fun ω => c*(F (x+a • T ω)-P0 ω)) (g := fun ω => b*(J1 ω-P1 ω))
        (hr0.const_mul c) (hr1.const_mul b), integral_const_mul, integral_const_mul,
      integral_sub hv hp0, integral_sub hj1 hp1]
  rw [er, ep0, ep1]
  change c*((∫ ω, F (x+a • T ω) ∂μ)-F x)+b*(∫ ω, J1 ω ∂μ) =
    -(1/2 : ℝ)*(∫ ω, D2 ω ∂μ)+d*(∫ ω, D3 ω ∂μ)+_
  linear_combination (∫ ω, D2 ω ∂μ)*h2+(∫ ω, D3 ω ∂μ)*h3

end
end RectangleCLT.Companion.SplitV4
