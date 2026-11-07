import RectangleCLTCompanion.SplitV4.GenericC4DerivativeOperator
import RectangleCLTCompanion.SplitV4.GenericC4CubicLaw
import RectangleCLTCompanion.SplitV4.GenericC4OuterFourth

/-! Appendix B.1 for a genuinely C4 test with bounded derivatives. The
Gaussian seed is independent, the amplitude is arbitrary C1, and the cubic
tensor is aggregated with its sign at the actual common interpolation law.
The fourth tensors are in the manuscript's ordinary derivative slot order. -/

open MeasureTheory
open scoped BigOperators Interval

namespace RectangleCLT.Companion.SplitV4
noncomputable section

theorem hasDerivAt_genericThirdMomentMultiplier
    {γ : ℝ → ℝ} {g t : ℝ} (hγ : HasDerivAt γ g t) :
    HasDerivAt (fun r => (1-r)*γ r) (-γ t+(1-t)*g) t := by
  have hd := ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).mul hγ
  simpa only [id_eq, zero_sub, neg_mul, one_mul] using hd

theorem genericVariableSelectorDerivative_fourth_identity
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    {F : Vector p → ℝ} (hF : ContDiff ℝ 4 F) {C : ℝ} (hC : 0 ≤ C)
    (hjet : ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ∀ x, ‖iteratedFDeriv ℝ k F x‖ ≤ C)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose = covariance μ (sumVector ξ))
    (γ γ' : ℝ → ℝ) (ε : ℝ) (x : Vector p) {t : ℝ}
    (hγ : γ t ≠ 0) (ht : 0 < t+ε) (hq : variableRetention γ t ∈ Set.Icc (0 : ℝ) 1) :
    (C4Test.ofContDiff F hF C hC hjet).genericVariableSelectorDerivative μ ξ A γ γ' ε x t =
      ((-(γ t)+(1-t)*γ' t)/6)*
        (∫ y, genericCubicContraction μ F ξ (x+y) ∂variableSeededInterpolationLaw μ ξ A γ ε t)+
      ∫ r in (0 : ℝ)..1, genericFourthPathIntegrand μ (gaussianLaw A) F ξ x
        (variableRetention γ t) (γ t) (Real.sqrt (t+ε))
        (variableRetentionDerivative γ γ' t) (variableRetention γ t*γ' t)
        ((-(γ t)+(1-t)*γ' t)/6) r := by
  have h2 : variableRetentionDerivative γ γ' t*(γ t)^2/2+
      (variableRetention γ t*γ' t)*γ t = -(1/2 : ℝ) := by
    unfold variableRetentionDerivative variableRetention
    field_simp [hγ]
    <;> ring
  have h3 : variableRetentionDerivative γ γ' t*(γ t)^3/6+
      (variableRetention γ t*γ' t)*(γ t)^2/2 = (-(γ t)+(1-t)*γ' t)/6 := by
    unfold variableRetentionDerivative variableRetention
    field_simp [hγ]
    <;> ring
  have hCubic := integrable_genericCommonCubic_gaussian μ ξ h hF hC
    (hjet 3 (by decide) (by decide)) A x (variableRetention γ t) (γ t) (Real.sqrt (t+ε))
  have hFourth := genericSelectorFourthRemainder_outer_interval μ (gaussianLaw A) hF hC
    (hjet 4 (by decide) (by decide)) ξ h x (variableRetention γ t) (γ t) (Real.sqrt (t+ε))
    (variableRetentionDerivative γ γ' t) (variableRetention γ t*γ' t) ((-(γ t)+(1-t)*γ' t)/6)
  rw [genericVariableSelectorDerivative_eq_operator μ ξ h hF hC hjet A γ γ' ε x ht]
  simp_rw [genericSelectorOperator_fourth_identity μ hF hC hjet ξ h A hA _
    (variableRetention γ t) (γ t) (variableRetentionDerivative γ γ' t)
    (variableRetention γ t*γ' t) ((-(γ t)+(1-t)*γ' t)/6) hγ h2 h3]
  rw [integral_add (f := fun g => ((-(γ t)+(1-t)*γ' t)/6)*
        genericCommonCubic μ F ξ (x+Real.sqrt (t+ε) • g) (variableRetention γ t) (γ t))
      (g := fun g => genericSelectorFourthRemainder μ F ξ (x+Real.sqrt (t+ε) • g)
        (variableRetention γ t) (γ t) (variableRetentionDerivative γ γ' t)
        (variableRetention γ t*γ' t) ((-(γ t)+(1-t)*γ' t)/6)) (hCubic.const_mul _) hFourth.1,
    integral_const_mul,
    integral_genericCommonCubic_eq_seededLaw μ ξ h hF hC (hjet 3 (by decide) (by decide)) A γ ε x t hq,
    hFourth.2.2]

theorem hasDerivAt_integral_genericVariableSeededInterpolationLaw_fourth_identity
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
      (((-(γ t)+(1-t)*γ' t)/6)*
        (∫ y, genericCubicContraction μ F ξ (x+y) ∂variableSeededInterpolationLaw μ ξ A γ ε t)+
       ∫ r in (0 : ℝ)..1, genericFourthPathIntegrand μ (gaussianLaw A) F ξ x
         (variableRetention γ t) (γ t) (Real.sqrt (t+ε))
         (variableRetentionDerivative γ γ' t) (variableRetention γ t*γ' t)
         ((-(γ t)+(1-t)*γ' t)/6) r) t := by
  have hd := (C4Test.ofContDiff F hF C hC hjet).hasDerivAt_integral_variableSeededInterpolationLaw
    μ ξ h.measurable h.delta_nonneg h.bounded A γ γ' hε hderiv hpos hq x ht ht1 hcont
  rw [genericVariableSelectorDerivative_fourth_identity μ ξ h hF hC hjet A hA γ γ' ε x
    (hpos t ⟨ht,ht1⟩).ne' (by linarith) (hq t ⟨ht,ht1⟩)] at hd
  exact hd

def genericManuscriptFourthCombination {p : ℕ} (F : Vector p → ℝ)
    (x u v : Vector p) (a η t r : ℝ) : ℝ :=
  seededFourthKernel a η r * canonicalFourthTensor F (x+(a*r) • v) v v v v+
    ((1-t)/2*(1-r))*canonicalFourthTensor F (x+(a*r) • v) u u v v+
    ((1-t)/6*(1-η))*canonicalFourthTensor F (x+(a*r) • v) u u u v

theorem genericFourthCombination_variable_eq_manuscript
    {p : ℕ} (F : Vector p → ℝ) (x u v : Vector p) (γ γ' : ℝ → ℝ)
    {t : ℝ} (hγ : γ t ≠ 0) (r : ℝ) :
    genericFourthCombination F x u v (variableRetention γ t) (γ t)
      (variableRetentionDerivative γ γ' t) (variableRetention γ t*γ' t)
      ((-(γ t)+(1-t)*γ' t)/6) r =
      genericManuscriptFourthCombination F x u v (γ t) (variableEta γ γ' t) t r := by
  have hA : variableRetentionDerivative γ γ' t*(γ t)^4/6*(1-r)^3+
      (variableRetention γ t*γ' t)*(γ t)^3/2*(1-r)^2 =
        seededFourthKernel (γ t) (variableEta γ γ' t) r := by
    unfold variableRetentionDerivative variableRetention variableEta seededFourthKernel
    field_simp [hγ]
    <;> ring
  have hB : variableRetention γ t*(γ t)^2/2 = (1-t)/2 := by
    rw [variable_covariance_calibration γ hγ]
  unfold genericFourthCombination genericManuscriptFourthCombination
  rw [hA, hB, variable_independent_copy_cubic_coefficient γ γ' hγ]

def genericManuscriptFourthPathIntegrand
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ν : Measure (Vector p)) (F : Vector p → ℝ)
    (ξ : Fin n → Ω → Vector p) (x : Vector p) (q a σ η t r : ℝ) : ℝ :=
  ∑ i, ∑ mask : Kane.Cube n, Kane.maskWeight q mask *
    ∫ z : (Vector p × Ω) × (Ω × Ω),
      genericManuscriptFourthCombination F
        (x+σ • z.1.1+a • maskObservationSum ξ (Function.update mask i false) z.1.2)
        (ξ i z.2.1) (ξ i z.2.2) a η t r ∂(ν.prod μ).prod (μ.prod μ)

theorem genericFourthPathIntegrand_variable_eq_manuscript
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ν : Measure (Vector p)) (F : Vector p → ℝ)
    (ξ : Fin n → Ω → Vector p) (x : Vector p) (γ γ' : ℝ → ℝ)
    {t : ℝ} (hγ : γ t ≠ 0) (σ r : ℝ) :
    genericFourthPathIntegrand μ ν F ξ x (variableRetention γ t) (γ t) σ
      (variableRetentionDerivative γ γ' t) (variableRetention γ t*γ' t)
      ((-(γ t)+(1-t)*γ' t)/6) r =
      genericManuscriptFourthPathIntegrand μ ν F ξ x (variableRetention γ t) (γ t) σ
        (variableEta γ γ' t) t r := by
  unfold genericFourthPathIntegrand genericManuscriptFourthPathIntegrand
  simp_rw [genericFourthCombination_variable_eq_manuscript F _ _ _ γ γ' hγ]

/-- The full general-amplitude seeded fourth-order identity, with exactly
the three manuscript scalar kernels and ordinary canonical fourth slots.
The signed cubic tensor is summed before any absolute value is taken. -/
theorem hasDerivAt_integral_genericVariableSeededInterpolationLaw_manuscript
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
      (((-(γ t)+(1-t)*γ' t)/6)*
        (∫ y, genericCubicContraction μ F ξ (x+y) ∂variableSeededInterpolationLaw μ ξ A γ ε t)+
       ∫ r in (0 : ℝ)..1, genericManuscriptFourthPathIntegrand μ (gaussianLaw A) F ξ x
         (variableRetention γ t) (γ t) (Real.sqrt (t+ε)) (variableEta γ γ' t) t r) t := by
  have hd := hasDerivAt_integral_genericVariableSeededInterpolationLaw_fourth_identity
    μ ξ h hF hC hjet A hA γ γ' hε hderiv hpos hq x ht ht1 hcont
  simp_rw [genericFourthPathIntegrand_variable_eq_manuscript μ (gaussianLaw A) F ξ x γ γ'
    (hpos t ⟨ht,ht1⟩).ne'] at hd
  exact hd

theorem intervalIntegrable_genericManuscriptFourthPathIntegrand
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    {F : Vector p → ℝ} (hF : ContDiff ℝ 4 F) {C : ℝ} (hC : 0 ≤ C)
    (hjet : ∀ x, ‖iteratedFDeriv ℝ 4 F x‖ ≤ C)
    (A : Matrix (Fin p) (Fin p) ℝ) (γ γ' : ℝ → ℝ) {t : ℝ}
    (hγ : γ t ≠ 0) (x : Vector p) (σ : ℝ) :
    IntervalIntegrable (genericManuscriptFourthPathIntegrand μ (gaussianLaw A) F ξ x
      (variableRetention γ t) (γ t) σ (variableEta γ γ' t) t) volume 0 1 := by
  have hi := (genericSelectorFourthRemainder_outer_interval μ (gaussianLaw A) hF hC hjet ξ h x
    (variableRetention γ t) (γ t) σ (variableRetentionDerivative γ γ' t)
    (variableRetention γ t*γ' t) ((-(γ t)+(1-t)*γ' t)/6)).2.1
  have he : genericFourthPathIntegrand μ (gaussianLaw A) F ξ x (variableRetention γ t) (γ t) σ
      (variableRetentionDerivative γ γ' t) (variableRetention γ t*γ' t) ((-(γ t)+(1-t)*γ' t)/6) =
      genericManuscriptFourthPathIntegrand μ (gaussianLaw A) F ξ x (variableRetention γ t) (γ t) σ
        (variableEta γ γ' t) t := by
    funext r
    exact genericFourthPathIntegrand_variable_eq_manuscript μ (gaussianLaw A) F ξ x γ γ' hγ σ r
  rw [he] at hi
  exact hi

end
end RectangleCLT.Companion.SplitV4
