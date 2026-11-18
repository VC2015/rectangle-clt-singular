import RectangleCLTCompanion.SplitV4.GenericC4CubicTensor

/-!
# Lemma B.1: the actual seeded interpolation identity

The Bernoulli law is specified separately at each time. The fourth-order
integrand below uses the removed-summand base, the two independent copies,
and the three literal scalar kernels from the manuscript.
-/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators Interval
noncomputable section

def seededInterpolationThirdMultiplier (γ : ℝ → ℝ) (t : ℝ) : ℝ := (1-t)*γ t

theorem seededInterpolationThirdMultiplier_hasDerivAt
    {γ : ℝ → ℝ} {g t : ℝ} (hγ : HasDerivAt γ g t) :
    HasDerivAt (seededInterpolationThirdMultiplier γ) (-γ t+(1-t)*g) t :=
  hasDerivAt_genericThirdMomentMultiplier hγ

/-- Scalar covariance budget of the retained array and its independent seed. -/
theorem seededInterpolation_covariance_calibration (γ : ℝ → ℝ)
    {t : ℝ} (hγ : γ t ≠ 0) (ε : ℝ) :
    variableRetention γ t * (γ t) ^ 2 + (t+ε) = 1+ε := by
  rw [variable_covariance_calibration γ hγ]
  ring

/-- The signed cubic aggregate has exactly the multiplier q₃ in B.1. -/
theorem seededInterpolation_third_calibration (γ : ℝ → ℝ)
    {t : ℝ} (hγ : γ t ≠ 0) :
    variableRetention γ t * (γ t) ^ 3 = seededInterpolationThirdMultiplier γ t :=
  variable_third_moment_calibration γ hγ

def seededInterpolationKernelA (a η s : ℝ) : ℝ :=
  a ^ 2 / 6 * (1-s) ^ 2 * (η-1+(1+2*η)*s)

def seededInterpolationKernelB (t s : ℝ) : ℝ := (1-t)/2*(1-s)

def seededInterpolationKernelC (η t : ℝ) : ℝ := (1-t)/6*(1-η)

def seededInterpolationFourthCombination {p : ℕ} (F : Vector p → ℝ)
    (x u v : Vector p) (a η t s : ℝ) : ℝ :=
  seededInterpolationKernelA a η s * canonicalFourthTensor F (x+(a*s) • v) v v v v +
  seededInterpolationKernelB t s * canonicalFourthTensor F (x+(a*s) • v) u u v v +
  seededInterpolationKernelC η t * canonicalFourthTensor F (x+(a*s) • v) u u u v

theorem seededInterpolationFourthCombination_eq {p : ℕ} (F : Vector p → ℝ)
    (x u v : Vector p) (a η t s : ℝ) :
    seededInterpolationFourthCombination F x u v a η t s =
      genericManuscriptFourthCombination F x u v a η t s := rfl

/-- The two copies are the second product factor. The removed original
summand is set to false before either copy is inserted along its segment. -/
def seededInterpolationFourthPath
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ν : Measure (Vector p)) (F : Vector p → ℝ)
    (ξ : Fin n → Ω → Vector p) (x : Vector p) (q a σ η t s : ℝ) : ℝ :=
  ∑ i, ∑ mask : Kane.Cube n, Kane.maskWeight q mask *
    ∫ z : (Vector p × Ω) × (Ω × Ω),
      seededInterpolationFourthCombination F
        (x+σ • z.1.1+a • maskObservationSum ξ (Function.update mask i false) z.1.2)
        (ξ i z.2.1) (ξ i z.2.2) a η t s ∂(ν.prod μ).prod (μ.prod μ)

theorem seededInterpolationFourthPath_eq
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ν : Measure (Vector p)) (F : Vector p → ℝ)
    (ξ : Fin n → Ω → Vector p) (x : Vector p) (q a σ η t s : ℝ) :
    seededInterpolationFourthPath μ ν F ξ x q a σ η t s =
      genericManuscriptFourthPathIntegrand μ ν F ξ x q a σ η t s := rfl

/-- B.1 with the actual signed aggregate cubic tensor and all three
fourth-order kernels, for any covariance factor and any nonnegative seed. -/
theorem lemma_B1_gaussian_seed_interpolation
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
        (∫ y, canonicalSignedCubicContraction μ F ξ (x+y) ∂variableSeededInterpolationLaw μ ξ A γ ε t)+
       ∫ r in (0 : ℝ)..1, seededInterpolationFourthPath μ (gaussianLaw A) F ξ x
         (variableRetention γ t) (γ t) (Real.sqrt (t+ε)) (variableEta γ γ' t) t r) t := by
  simpa only [seededInterpolationFourthPath_eq] using
    hasDerivAt_integral_genericVariableSeededInterpolationLaw_tensor μ ξ h hF hC hjet
      A hA γ γ' hε hderiv hpos hq x ht ht1 hcont

end
end RectangleCLTArxivV1
