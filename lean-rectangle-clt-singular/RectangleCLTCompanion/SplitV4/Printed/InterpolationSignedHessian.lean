import RectangleCLTCompanion.SplitV4.Printed.InterpolationTaylorTwo
import RectangleCLTCompanion.SplitV4.GenericC4FourthIdentity
import RectangleCLTCompanion.SplitV4.GenericC4DerivativeOperator

/-! The signed-Hessian intermediate printed as appx-an:signed-hessian,
lines 2084--2091. The signed density is retained before any Taylor
expansion or absolute value. Independent fresh directions are actual
integrals; finite Bernoulli masks merely expand the printed expectation. -/

open MeasureTheory
open scoped BigOperators Interval

namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

theorem genericRowOperator_eq_signed_hessian
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] {F : Vector p → ℝ} (hF : ContDiff ℝ 4 F)
    {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hjet : ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ∀ x, ‖iteratedFDeriv ℝ k F x‖ ≤ C)
    (T : Ω → Vector p) (hT : Measurable T) (hbound : ∀ᵐ ω ∂μ, ‖T ω‖ ≤ δ)
    (hc : ∀ j, (∫ ω, T ω j ∂μ) = 0) (x : Vector p)
    (γ γ' : ℝ → ℝ) {t : ℝ} (hγ : γ t ≠ 0) :
    genericRowOperator μ F T x (γ t) (variableRetentionDerivative γ γ' t)
      (variableRetention γ t*γ' t) =
      -(1/2 : ℝ)*∫ r in (0 : ℝ)..1, signedDensity (variableEta γ γ' t) r*
        (∫ u, canonicalDiagonal F 2 (x+(γ t*r) • T u) (T u) ∂μ) := by
  let M : ℝ → ℝ := fun r => ∫ u, canonicalDiagonal F 2 (x+(γ t*r) • T u) (T u) ∂μ
  have hM : IntervalIntegrable M volume 0 1 := by
    have hi := integrable_canonicalDiagonal_interval_prod μ hF (by decide) hC hδ
      (hjet 2 (by decide) (by decide)) T hT hbound x (γ t) (fun _ => 1) continuous_const
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    simpa only [one_mul, M] using hi.integral_prod_right
  have h1M : IntervalIntegrable (fun r => (1-r)*M r) volume 0 1 := by
    have hi := integrable_canonicalDiagonal_interval_prod μ hF (by decide) hC hδ
      (hjet 2 (by decide) (by decide)) T hT hbound x (γ t) (fun r => 1-r) (by fun_prop)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    simpa only [integral_const_mul, M] using hi.integral_prod_right
  unfold genericRowOperator
  rw [centered_value_hessian_identity μ hF hC hδ hjet T hT hbound hc,
    centered_gradient_hessian_identity μ hF hC hδ hjet T hT hbound hc]
  change variableRetentionDerivative γ γ' t*((γ t)^2*∫ r in (0 : ℝ)..1, (1-r)*M r)+
    (variableRetention γ t*γ' t)*(γ t*∫ r in (0 : ℝ)..1, M r) = _
  rw [← mul_assoc, ← mul_assoc, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add (h1M.const_mul _) (hM.const_mul _),
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro r _
  have he := variable_signed_hessian_coefficient γ γ' hγ r
  dsimp only [M]
  linear_combination (∫ u, canonicalDiagonal F 2 (x+(γ t*r) • T u) (T u) ∂μ)*he

/-- Deleted-row part of the literal signed-Hessian expectation. -/
def signedDeletedHessian {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (F : Vector p → ℝ) (ξ : Fin n → Ω → Vector p)
    (i : Fin n) (x : Vector p) (q a η : ℝ) : ℝ :=
  ∑ mask : Kane.Cube n, Kane.maskWeight q mask*∫ ω,
    (∫ r in (0 : ℝ)..1, signedDensity η r*
      (∫ u, canonicalDiagonal F 2
        (x+a • maskObservationSum ξ (Function.update mask i false) ω+(a*r) • ξ i u)
        (ξ i u) ∂μ)) ∂μ

def signedHessianSelector {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (F : Vector p → ℝ) (ξ : Fin n → Ω → Vector p)
    (x : Vector p) (q a η : ℝ) : ℝ :=
  (1/2 : ℝ)*∑ i, (genericFullMoment μ F 2 ξ i x q a-signedDeletedHessian μ F ξ i x q a η)

theorem genericSelectorOperator_eq_signedHessian
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] {F : Vector p → ℝ} (hF : ContDiff ℝ 4 F)
    {C δ : ℝ} (hC : 0 ≤ C)
    (hjet : ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ∀ x, ‖iteratedFDeriv ℝ k F x‖ ≤ C)
    (ξ : Fin n → Ω → Vector p) (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose = covariance μ (sumVector ξ))
    (x : Vector p) (γ γ' : ℝ → ℝ) {t : ℝ} (hγ : γ t ≠ 0) :
    genericSelectorOperator μ F ξ (A*A.transpose) x (variableRetention γ t) (γ t)
      (variableRetentionDerivative γ γ' t) (variableRetention γ t*γ' t) =
      signedHessianSelector μ F ξ x (variableRetention γ t) (γ t) (variableEta γ γ' t) := by
  let q := variableRetention γ t
  let a := γ t
  let c := variableRetentionDerivative γ γ' t
  let b := variableRetention γ t*γ' t
  let V := genericFixedValue μ F ξ x a
  let G := fun i mask => genericFixedGradient μ F ξ x a i mask
  have hforced : genericSelectorOperator μ F ξ (A*A.transpose) x q a c b =
      (∑ i, ∑ mask : Kane.Cube n, Kane.maskWeight q mask*(∫ ω, genericRowOperator μ F (ξ i)
        (x+a • maskObservationSum ξ (Function.update mask i false) ω) a c b ∂μ))+
      ∑ mask : Kane.Cube n, Kane.maskWeight q mask*genericFixedHeat μ F ξ (A*A.transpose) x a mask := by
    unfold genericSelectorOperator
    have he (i : Fin n) :
        (∑ mask : Kane.Cube n, Kane.maskWeight q mask*
          (c*(V (Function.update mask i true)-V (Function.update mask i false))+b*G i (Function.update mask i true))) =
        c*(∑ mask, Kane.maskWeight q mask*(V (Function.update mask i true)-V (Function.update mask i false)))+
        b*(∑ mask, Kane.maskWeight q mask*G i (Function.update mask i true)) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro mask _ <;> ring
    calc
      _ = (∑ i, ∑ mask : Kane.Cube n, Kane.maskWeight q mask*
          (c*(V (Function.update mask i true)-V (Function.update mask i false))+b*G i (Function.update mask i true)))+
          ∑ mask : Kane.Cube n, Kane.maskWeight q mask*genericFixedHeat μ F ξ (A*A.transpose) x a mask := by
        simp_rw [he]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = _ := by
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro mask _
        congr 1
        exact generic_forced_increment_eq_rowOperator μ hF hC hjet ξ h mask i x a c b
  have hrow (i : Fin n) : (∑ mask : Kane.Cube n, Kane.maskWeight q mask*(∫ ω, genericRowOperator μ F (ξ i)
      (x+a • maskObservationSum ξ (Function.update mask i false) ω) a c b ∂μ)) =
      -(1/2 : ℝ)*signedDeletedHessian μ F ξ i x q a (variableEta γ γ' t) := by
    dsimp only [a,c,b]
    simp_rw [genericRowOperator_eq_signed_hessian μ hF hC h.delta_nonneg hjet (ξ i)
      (h.measurable i) (h.bounded i) (h.centered i) _ γ γ' hγ]
    simp only [integral_const_mul, signedDeletedHessian, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro mask _
    ring
  have hheat : (∑ mask : Kane.Cube n, Kane.maskWeight q mask*genericFixedHeat μ F ξ (A*A.transpose) x a mask) =
      (1/2 : ℝ)*∑ i, genericFullMoment μ F 2 ξ i x q a := by
    simp_rw [genericFixedHeat_eq_half_sum_moments μ hF hC hjet ξ h A hA x a]
    unfold genericFullMoment
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro mask _
    ring
  change genericSelectorOperator μ F ξ (A*A.transpose) x q a c b = _
  rw [hforced]
  simp_rw [hrow]
  rw [hheat]
  simp only [signedHessianSelector, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- The actual B.1 path derivative, stopped at the printed signed-Hessian
stage. It has no supplied derivative or analytic comparison premise. -/
theorem hasDerivAt_seededExpectation_signedHessian
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    {F : Vector p → ℝ} (hF : ContDiff ℝ 4 F) {C : ℝ} (hC : 0 ≤ C)
    (hjet : ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ∀ x, ‖iteratedFDeriv ℝ k F x‖ ≤ C)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose = covariance μ (sumVector ξ))
    (γ γ' : ℝ → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hderiv : ∀ r ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt γ (γ' r) r)
    (hpos : ∀ r ∈ Set.Ioo (0 : ℝ) 1, 0 < γ r)
    (hq : ∀ r ∈ Set.Ioo (0 : ℝ) 1, variableRetention γ r ∈ Set.Icc (0 : ℝ) 1)
    (x : Vector p) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) (hcont : ContinuousAt γ' t) :
    HasDerivAt (fun r => ∫ y, F (x+y) ∂variableSeededInterpolationLaw μ ξ A γ ε r)
      (∫ g, signedHessianSelector μ F ξ (x+Real.sqrt (t+ε) • g)
        (variableRetention γ t) (γ t) (variableEta γ γ' t) ∂gaussianLaw A) t := by
  let f := C4Test.ofContDiff F hF C hC hjet
  have hd := f.hasDerivAt_integral_variableSeededInterpolationLaw μ ξ h.measurable h.delta_nonneg
    h.bounded A γ γ' hε hderiv hpos hq x ht ht1 hcont
  have he := genericVariableSelectorDerivative_eq_operator μ ξ h hF hC hjet A γ γ' ε x (by linarith)
  simp_rw [genericSelectorOperator_eq_signedHessian μ hF hC hjet ξ h A hA _ γ γ'
    (hpos t ⟨ht,ht1⟩).ne'] at he
  rw [he] at hd
  exact hd

end
end RectangleCLT.Companion.SplitV4.Printed
