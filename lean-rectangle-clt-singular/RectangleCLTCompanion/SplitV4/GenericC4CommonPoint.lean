import RectangleCLTCompanion.SplitV4.GenericC4RowTaylor

/-! Actual mixed C4 common-point Taylor corrections. The argument order
below is mathlib's iterated-derivative order; slot permutation to the
manuscript convention is a separate checked equivalence. -/

open MeasureTheory
open scoped BigOperators Interval

namespace RectangleCLT.Companion.SplitV4
noncomputable section

theorem integral_linear_centered_zero
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Vector p) (hT : Measurable T) {δ : ℝ} (hbound : ∀ᵐ ω ∂μ, ‖T ω‖ ≤ δ)
    (hc : ∀ j, (∫ ω, T ω j ∂μ) = 0) (L : Vector p →L[ℝ] ℝ) :
    (∫ ω, L (T ω) ∂μ) = 0 := by
  have hi : Integrable T μ := (integrable_const δ).mono' hT.aestronglyMeasurable hbound
  have hmean : (∫ ω, T ω ∂μ) = 0 := by
    ext j
    have he := (ContinuousLinearMap.proj j : Vector p →L[ℝ] ℝ).integral_comp_comm hi
    change (∫ ω, T ω j ∂μ) = (∫ ω, T ω ∂μ) j at he
    simpa only [hc j, Pi.zero_apply] using he.symm
  rw [L.integral_comp_comm hi, hmean, map_zero]

theorem canonical_mixed_cubic_integral_zero
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Vector p → ℝ) (T : Ω → Vector p) (hT : Measurable T) {δ : ℝ}
    (hbound : ∀ᵐ ω ∂μ, ‖T ω‖ ≤ δ) (hc : ∀ j, (∫ ω, T ω j ∂μ) = 0)
    (x u : Vector p) :
    (∫ ω, iteratedFDeriv ℝ 3 F x (Fin.cons (T ω) (fun _ : Fin 2 => u)) ∂μ) = 0 := by
  have he (v : Vector p) : Fin.cons v (fun _ : Fin 2 => u) =
      Function.update (fun _ : Fin 3 => u) 0 v := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp only [Fin.cons_succ, Function.update_of_ne (Fin.succ_ne_zero j)]
  simp_rw [he]
  exact integral_linear_centered_zero μ T hT hbound hc
    ((iteratedFDeriv ℝ 3 F x).toContinuousLinearMap (fun _ => u) 0)

theorem integral_canonical_hessian_shift_sub
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    {F : Vector p → ℝ} (hF : ContDiff ℝ 4 F) {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hjet : ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ∀ x, ‖iteratedFDeriv ℝ k F x‖ ≤ C)
    (T : Ω → Vector p) (hT : Measurable T) (hbound : ∀ᵐ ω ∂μ, ‖T ω‖ ≤ δ)
    (hc : ∀ j, (∫ ω, T ω j ∂μ) = 0) (x u : Vector p) {a : ℝ} (ha : a ≠ 0) :
    (∫ ω, iteratedFDeriv ℝ 2 F (x+a • T ω) (fun _ => u) ∂μ)-
      iteratedFDeriv ℝ 2 F x (fun _ => u) =
      a^2*(∫ ω, (∫ r in (0 : ℝ)..1, (1-r)*iteratedFDeriv ℝ 4 F (x+(a*r) • T ω)
        (Fin.cons (T ω) (Fin.cons (T ω) (fun _ : Fin 2 => u)))) ∂μ) := by
  let D := max δ ‖u‖
  have hD : 0 ≤ D := hδ.trans (le_max_left _ _)
  have hTbound : ∀ᵐ ω ∂μ, ‖T ω‖ ≤ D := hbound.mono fun ω hω => hω.trans (le_max_left _ _)
  have hUb : ∀ i : Fin 2, ∀ᵐ ω ∂μ, ‖(fun _ : Ω => u) ω‖ ≤ D :=
    fun _ => ae_of_all _ fun _ => le_max_right _ _
  have hshift : Integrable (fun ω => iteratedFDeriv ℝ 2 F (x+a • T ω) (fun _ => u)) μ :=
    integrable_canonical_derivative_eval μ hF (by decide) _
      (measurable_const.add (measurable_const.smul hT)) (fun _ _ => u) (fun _ => measurable_const)
      hC hD (hjet 2 (by decide) (by decide)) hUb
  let Lin := fun ω => iteratedFDeriv ℝ 3 F x (Fin.cons (T ω) (fun _ : Fin 2 => u))
  have hLin : Integrable Lin μ := by
    change Integrable (fun ω => iteratedFDeriv ℝ 3 F x (Fin.cons (T ω) (fun _ : Fin 2 => u))) μ
    apply integrable_canonical_derivative_eval (k := 3) μ hF (by decide) (fun _ => x) measurable_const
      (fun i ω => (Fin.cons (T ω) (fun _ : Fin 2 => u) : Fin 3 → Vector p) i)
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hT
      · exact measurable_const
    · exact hC
    · exact hD
    · exact hjet 3 (by decide) (by decide)
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hTbound
      · exact ae_of_all _ fun _ => le_max_right _ _
  have hzero : (∫ ω, Lin ω ∂μ) = 0 := canonical_mixed_cubic_integral_zero μ F T hT hbound hc x u
  let R := fun ω => ∫ r in (0 : ℝ)..1, (1-r)*iteratedFDeriv ℝ 4 F (x+(a*r) • T ω)
    (Fin.cons (T ω) (Fin.cons (T ω) (fun _ : Fin 2 => u)))
  have he (ω : Ω) : iteratedFDeriv ℝ 2 F (x+a • T ω) (fun _ => u)-
      (iteratedFDeriv ℝ 2 F x (fun _ => u)+a*Lin ω) = a^2*R ω := by
    rw [canonical_hessian_taylor_two hF]
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro r _
    ring
  have hRA : Integrable (fun ω => a^2*R ω) μ :=
    (hshift.sub ((integrable_const _).add (hLin.const_mul a))).congr (ae_of_all _ he)
  have hR : Integrable R μ := by
    apply (hRA.const_mul ((a^2)⁻¹)).congr
    apply ae_of_all
    intro ω
    change (a^2)⁻¹*(a^2*R ω) = R ω
    field_simp
  have hh := integral_congr_ae (ae_of_all μ he)
  rw [integral_sub
      (f := fun ω => iteratedFDeriv ℝ 2 F (x+a • T ω) (fun _ => u))
      (g := fun ω => iteratedFDeriv ℝ 2 F x (fun _ => u)+a*Lin ω)
      hshift ((integrable_const _).add (hLin.const_mul a)),
    integral_add (f := fun _ : Ω => iteratedFDeriv ℝ 2 F x (fun _ => u)) (g := fun ω => a*Lin ω)
      (integrable_const _) (hLin.const_mul a), integral_const_mul, integral_const_mul,
    integral_const, measureReal_univ_eq_one, one_smul, hzero, mul_zero, add_zero] at hh
  exact hh

theorem integral_canonical_third_shift_sub
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    {F : Vector p → ℝ} (hF : ContDiff ℝ 4 F) {C : ℝ} (hC : 0 ≤ C)
    (hjet : ∀ x, ‖iteratedFDeriv ℝ 3 F x‖ ≤ C)
    (T : Ω → Vector p) (hT : Measurable T) (x u : Vector p) {a : ℝ} (ha : a ≠ 0) :
    (∫ ω, iteratedFDeriv ℝ 3 F (x+a • T ω) (fun _ => u) ∂μ)-
      iteratedFDeriv ℝ 3 F x (fun _ => u) =
      a*(∫ ω, (∫ r in (0 : ℝ)..1, iteratedFDeriv ℝ 4 F (x+(a*r) • T ω)
        (Fin.cons (T ω) (fun _ : Fin 3 => u))) ∂μ) := by
  have hshift : Integrable (fun ω => iteratedFDeriv ℝ 3 F (x+a • T ω) (fun _ => u)) μ :=
    integrable_canonical_derivative_eval μ hF (by decide) _
      (measurable_const.add (measurable_const.smul hT)) (fun _ _ => u) (fun _ => measurable_const)
      hC (norm_nonneg u) hjet (fun _ => ae_of_all _ fun _ => le_rfl)
  let R := fun ω => ∫ r in (0 : ℝ)..1, iteratedFDeriv ℝ 4 F (x+(a*r) • T ω)
    (Fin.cons (T ω) (fun _ : Fin 3 => u))
  have he (ω : Ω) : iteratedFDeriv ℝ 3 F (x+a • T ω) (fun _ => u)-
      iteratedFDeriv ℝ 3 F x (fun _ => u) = a*R ω := by
    rw [canonical_third_taylor_one hF, intervalIntegral.integral_const_mul]
  have hRA : Integrable (fun ω => a*R ω) μ :=
    (hshift.sub (integrable_const _)).congr (ae_of_all _ he)
  have hR : Integrable R μ := by
    apply (hRA.const_mul a⁻¹).congr
    apply ae_of_all
    intro ω
    change a⁻¹*(a*R ω) = R ω
    field_simp
  have hh := integral_congr_ae (ae_of_all μ he)
  rw [integral_sub (f := fun ω => iteratedFDeriv ℝ 3 F (x+a • T ω) (fun _ => u))
      (g := fun _ : Ω => iteratedFDeriv ℝ 3 F x (fun _ => u)) hshift (integrable_const _),
    integral_const_mul, integral_const, measureReal_univ_eq_one, one_smul] at hh
  exact hh

end
end RectangleCLT.Companion.SplitV4
