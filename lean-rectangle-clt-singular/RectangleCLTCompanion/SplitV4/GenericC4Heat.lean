import RectangleCLTCompanion.SplitV4.GenericC4Interpolation

/-! Actual Gaussian heat differentiation for an arbitrary C4 test.
The covariance is the concrete matrix `A Aᵀ`, and may be singular.
Gaussian integration by parts and all Fubini interchanges are discharged
from bounded derivatives and genuine first moments. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4.C4Test
noncomputable section
set_option autoImplicit false
variable {p : ℕ} (f : C4Test p)

/-- Gaussian integration by parts at an arbitrary measurable translated
base. Bounded first and second derivatives need no moments of that base. -/
theorem generic_shifted_gaussian_stein
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (V : Ω → Vector p) (hV : Measurable V)
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (a b : ℝ) :
    (∫ z : Ω × Vector p, f.gradient (x+a • V z.1+b • z.2) z.2 ∂μ.prod (gaussianLaw A)) =
      b * ∫ z : Ω × Vector p, f.hessianTrace (A*A.transpose)
        (x+a • V z.1+b • z.2) ∂μ.prod (gaussianLaw A) := by
  have hm : Measurable (fun z : Ω × Vector p => x+a • V z.1+b • z.2) :=
    (measurable_const.add (measurable_const.smul (hV.comp measurable_fst))).add
      (measurable_const.smul measurable_snd)
  have hiG : Integrable (fun z : Ω × Vector p => ‖z.2‖) (μ.prod (gaussianLaw A)) := by
    simpa only [one_mul] using
      (integrable_const (1 : ℝ) : Integrable (fun _ : Ω => (1 : ℝ)) μ).mul_prod
        (gaussianLaw_integrable_norm A)
  have hig := f.integrable_gradient_direction_of_norm (μ.prod (gaussianLaw A))
    _ Prod.snd hm measurable_snd hiG
  have hiH := f.integrable_hessianTrace (μ.prod (gaussianLaw A)) _ hm (A*A.transpose)
  have hs (ω : Ω) :
      (∫ g : Vector p, f.gradient (x+a • V ω+b • g) g ∂gaussianLaw A) =
        b * ∫ g : Vector p, f.hessianTrace (A*A.transpose) (x+a • V ω+b • g)
          ∂gaussianLaw A := by
    have hmp : Measurable (fun g : Vector p => x+a • V ω+b • g) := by fun_prop
    rw [f.integral_hessianTrace_eq _ _ hmp]
    simpa only [add_comm] using f.gaussian_gradient_stein A b (x+a • V ω)
  calc
    _ = ∫ ω, ∫ g : Vector p, f.gradient (x+a • V ω+b • g) g ∂gaussianLaw A ∂μ :=
      integral_prod _ hig
    _ = ∫ ω, b * ∫ g : Vector p,
        f.hessianTrace (A*A.transpose) (x+a • V ω+b • g) ∂gaussianLaw A ∂μ :=
      integral_congr_ae (ae_of_all _ hs)
    _ = b * ∫ ω, ∫ g : Vector p,
        f.hessianTrace (A*A.transpose) (x+a • V ω+b • g) ∂gaussianLaw A ∂μ :=
      integral_const_mul _ _
    _ = _ := congrArg (fun q => b*q) (integral_prod _ hiH).symm

/-- Exact spatial-plus-heat decomposition, requiring only a genuine first
moment of the observation direction. There is no heat identity premise. -/
theorem genericVariableHeatDerivative_eq_spatial_add_heat_of_integrable
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (V : Ω → Vector p) (hV : Measurable V)
    (hVnorm : Integrable (fun ω => ‖V ω‖) μ)
    (A : Matrix (Fin p) (Fin p) ℝ) (γ γ' : ℝ → ℝ) (ε : ℝ) (x : Vector p)
    {t : ℝ} (ht : 0 < t+ε) :
    f.genericVariableHeatDerivative μ V A γ γ' ε x t =
      γ' t * (∫ z : Ω × Vector p,
        f.gradient (x+γ t • V z.1+Real.sqrt (t+ε) • z.2) (V z.1) ∂μ.prod (gaussianLaw A)) +
      (1/2 : ℝ) * ∑ j, ∑ k, (A*A.transpose) j k *
        ∫ z : Ω × Vector p, f.hessianCoordinate
          (x+γ t • V z.1+Real.sqrt (t+ε) • z.2) j k ∂μ.prod (gaussianLaw A) := by
  have hm : Measurable (fun z : Ω × Vector p => x+γ t • V z.1+Real.sqrt (t+ε) • z.2) :=
    (measurable_const.add (measurable_const.smul (hV.comp measurable_fst))).add
      (measurable_const.smul measurable_snd)
  have hiV : Integrable (fun z : Ω × Vector p => ‖V z.1‖) (μ.prod (gaussianLaw A)) := by
    simpa only [mul_one] using hVnorm.mul_prod (integrable_const (1 : ℝ))
  have hiG : Integrable (fun z : Ω × Vector p => ‖z.2‖) (μ.prod (gaussianLaw A)) := by
    simpa only [one_mul] using
      (integrable_const (1 : ℝ) : Integrable (fun _ : Ω => (1 : ℝ)) μ).mul_prod
        (gaussianLaw_integrable_norm A)
  have higV := f.integrable_gradient_direction_of_norm (μ.prod (gaussianLaw A))
    _ (fun z : Ω × Vector p => V z.1) hm (hV.comp measurable_fst) hiV
  have higG := f.integrable_gradient_direction_of_norm (μ.prod (gaussianLaw A))
    _ Prod.snd hm measurable_snd hiG
  have hsplit (z : Ω × Vector p) :
      f.gradient (x+γ t • V z.1+Real.sqrt (t+ε) • z.2)
        (γ' t • V z.1+(1/(2*Real.sqrt (t+ε))) • z.2) =
      γ' t * f.gradient (x+γ t • V z.1+Real.sqrt (t+ε) • z.2) (V z.1) +
      (1/(2*Real.sqrt (t+ε))) *
        f.gradient (x+γ t • V z.1+Real.sqrt (t+ε) • z.2) z.2 := by
    simp only [map_add, map_smul, smul_eq_mul]
  unfold genericVariableHeatDerivative
  simp_rw [hsplit]
  rw [integral_add (higV.const_mul _) (higG.const_mul _), integral_const_mul,
    integral_const_mul, f.generic_shifted_gaussian_stein μ V hV A x (γ t) (Real.sqrt (t+ε)),
    f.integral_hessianTrace_eq _ _ hm]
  have hs : Real.sqrt (t+ε) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr ht)
  field_simp [hs]; ring

/-- The bounded-observation specialization used by the seeded array path. -/
theorem genericVariableHeatDerivative_eq_spatial_add_heat
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (V : Ω → Vector p) (hV : Measurable V) {δ : ℝ}
    (hbound : ∀ᵐ ω ∂μ, ‖V ω‖ ≤ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) (γ γ' : ℝ → ℝ) (ε : ℝ) (x : Vector p)
    {t : ℝ} (ht : 0 < t+ε) :
    f.genericVariableHeatDerivative μ V A γ γ' ε x t =
      γ' t * (∫ z : Ω × Vector p,
        f.gradient (x+γ t • V z.1+Real.sqrt (t+ε) • z.2) (V z.1) ∂μ.prod (gaussianLaw A)) +
      (1/2 : ℝ) * ∑ j, ∑ k, (A*A.transpose) j k *
        ∫ z : Ω × Vector p, f.hessianCoordinate
          (x+γ t • V z.1+Real.sqrt (t+ε) • z.2) j k ∂μ.prod (gaussianLaw A) := by
  apply f.genericVariableHeatDerivative_eq_spatial_add_heat_of_integrable μ V hV _ A γ γ' ε x ht
  apply (integrable_const δ).mono' hV.norm.aestronglyMeasurable
  filter_upwards [hbound] with ω hω
  simpa only [norm_norm] using hω

/-- The actual expectation derivative, with its Gaussian velocity fully
identified as the covariance-weighted Hessian term. -/
theorem hasDerivAt_genericVariableHeatExpectation_spatial_add_heat
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (V : Ω → Vector p) (hV : Measurable V) {δ : ℝ} (hδ : 0 ≤ δ)
    (hbound : ∀ᵐ ω ∂μ, ‖V ω‖ ≤ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) (γ γ' : ℝ → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hderiv : ∀ r ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt γ (γ' r) r)
    (x : Vector p) {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (hcont : ContinuousAt γ' t) :
    HasDerivAt (f.genericVariableHeatExpectation μ V A γ ε x)
      (γ' t * (∫ z : Ω × Vector p,
        f.gradient (x+γ t • V z.1+Real.sqrt (t+ε) • z.2) (V z.1) ∂μ.prod (gaussianLaw A)) +
      (1/2 : ℝ) * ∑ j, ∑ k, (A*A.transpose) j k *
        ∫ z : Ω × Vector p, f.hessianCoordinate
          (x+γ t • V z.1+Real.sqrt (t+ε) • z.2) j k ∂μ.prod (gaussianLaw A)) t := by
  have hd := f.hasDerivAt_genericVariableHeatExpectation μ V hV hδ hbound A γ γ' hε
    hderiv x ht ht1 hcont
  rw [f.genericVariableHeatDerivative_eq_spatial_add_heat μ V hV hbound A γ γ' ε x
    (by linarith)] at hd
  exact hd

end
end RectangleCLT.Companion.SplitV4.C4Test
