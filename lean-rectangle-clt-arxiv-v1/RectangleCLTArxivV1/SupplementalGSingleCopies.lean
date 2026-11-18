import RectangleCLTArxivV1.SupplementalGCopyModel

/-! The single complementary estimate with actual independent old/fresh
copies. Every copy moment and coefficient envelope is discharged from the
original bounded independent family and its covariance factor. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open RectangleCLT.FaceSmoother
open scoped BigOperators
noncomputable section
set_option autoImplicit false

theorem cap_single_face_actual_copies
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] {n₀ n q p r : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Fin n₀ → Ω → Vector 2} {η : ℝ}
    (hbase : BoundedIndependentHypotheses μ X η) (B : Matrix (Fin 2) (Fin q) ℝ)
    (hvar : (1/2 : ℝ) ≤ capMixedCovariance μ X B 0 0)
    (s : FaceSmoother p) (hband : η ≤ s.bandwidth) (f : Face p)
    (V : Ω × Vector q → Vector p) (hV : Measurable V) (a₀ : ℝ)
    (hproj : ∀ z, normalDot f (V z) = capMixedValue X B z 0+a₀)
    {ν : Measure Ξ} [IsProbabilityMeasure ν] {ξ : Fin n → Ξ → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses ν ξ δ) (A : Matrix (Fin p) (Fin r) ℝ)
    (hA : A*A.transpose = covariance ν (sumVector ξ))
    (hunit : ∀ j, covariance ν (sumVector ξ) j j = 1) (hr : 1 ≤ r)
    (oldFresh₁ oldFresh₂ : Bool)
    (v : Fin n → (Ω × Vector q) × (Ξ × Ξ) → Vector p) (hv : ∀ i, Measurable (v i))
    {R : ℝ} (hR : 0 ≤ R)
    (hvb : ∀ i, ∀ᵐ z ∂(μ.prod (standardGaussian q)).prod (ν.prod ν), ‖v i z‖ ≤ R)
    (hsmall : R/s.bandwidth ≤ Real.log (3/2 : ℝ)) (σ : ℝ) (hσ : 0 < σ) :
    |-(1/(s.bandwidth*σ^3))*(∫ g, ∫ ω, ∑ i, ∫ z,
      ((normalDot f (capOriginalCopy ξ oldFresh₁ i z)*normalDot f (capOriginalCopy ξ oldFresh₂ i z))*
        capThirdHermiteScore (capRectangularFactorNormal A f) (capWhitenedCopy A ξ i z) g)*
        selectorTupleWeight s ![f] ((σ • A).mulVec g+V ω+v i (ω,z)) ∂ν.prod ν
          ∂μ.prod (standardGaussian q) ∂standardGaussian r)| ≤
      (480*Real.exp (1/2)*Real.sqrt (Real.pi/capGaussianExponent)*δ^2*(r : ℝ))/σ^3 := by
  let c (i : Fin n) (z : (Ω × Vector q) × (Ξ × Ξ)) :=
    normalDot f (capOriginalCopy ξ oldFresh₁ i z.2)*normalDot f (capOriginalCopy ξ oldFresh₂ i z.2)
  have hc (i : Fin n) : Measurable (c i) := by
    have hm₁ := (capOriginalCopy_measurable ξ h.measurable oldFresh₁ i).comp
      (measurable_snd : Measurable (Prod.snd : (Ω × Vector q) × (Ξ × Ξ) → Ξ × Ξ))
    have hm₂ := (capOriginalCopy_measurable ξ h.measurable oldFresh₂ i).comp
      (measurable_snd : Measurable (Prod.snd : (Ω × Vector q) × (Ξ × Ξ) → Ξ × Ξ))
    dsimp only [c]
    unfold normalDot
    split <;> fun_prop
  have hcb (i : Fin n) : ∀ᵐ z ∂(μ.prod (standardGaussian q)).prod (ν.prod ν), |c i z| ≤ δ^2 :=
    Measure.quasiMeasurePreserving_snd.ae (capOriginalCopy_face_product_bounded h oldFresh₁ oldFresh₂ f i)
  have hdiag : ∀ j, (A*A.transpose) j j = 1 := by intro j; rw [hA]; exact hunit j
  have hu := capRectangularFactorNormal_unit A hdiag f
  have ht := cap_single_face_complementary_remainder_ae hbase B hvar s hband f V hV a₀ hproj
    (σ • A) (capRectangularFactorNormal A f) hr hu (ν.prod ν) (capWhitenedCopy A ξ)
    (capWhitenedCopy_measurable h A) (capWhitenedCopy_integrable_coordinate_pair h A)
    c hc v hv (sq_nonneg δ) (by norm_num : (0 : ℝ) ≤ 1) hR hcb hvb
    (fun y => by simpa only [one_mul] using capWhitenedCopy_quadratic_budget h A hA y)
    hsmall σ hσ
  simpa only [c,mul_one] using ht

end
end RectangleCLTArxivV1
