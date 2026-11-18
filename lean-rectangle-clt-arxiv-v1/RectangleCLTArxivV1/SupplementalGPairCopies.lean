import RectangleCLTArxivV1.SupplementalGPairRemainder
import RectangleCLTArxivV1.SupplementalGCopyModel

/-! The large-angle pair estimate for actual old/fresh independent copies.
All copy moments and coefficient budgets are discharged from the raw data. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open RectangleCLT.FaceSmoother
open scoped BigOperators
noncomputable section
set_option autoImplicit false

theorem capRectangularPairCoefficient_abs_le {p r : ℕ}
    (A : Matrix (Fin p) (Fin r) ℝ) (f g : Face p) (Y W : Vector p) {δ : ℝ}
    (hδ : 0 ≤ δ) (hρ : |faceDot (capRectangularFactorNormal A f) (capRectangularFactorNormal A g)| ≤ 1)
    (huz : |normalDot f Y| ≤ δ) (hvz : |normalDot g Y| ≤ δ)
    (huw : |normalDot f W| ≤ δ) (hvw : |normalDot g W| ≤ δ) :
    |capRectangularPairCoefficient A f g Y W| ≤ 4*δ^2 := by
  have h₁ := mul_le_mul huz hvw (abs_nonneg _) hδ
  have h₂ := mul_le_mul hvz huw (abs_nonneg _) hδ
  have h₃ := mul_le_mul huz huw (abs_nonneg _) hδ
  have h₄ := mul_le_mul hvz hvw (abs_nonneg _) hδ
  have hsum : |normalDot f Y*normalDot f W + normalDot g Y*normalDot g W| ≤ 2*δ^2 := by
    calc
      _ ≤ |normalDot f Y| *|normalDot f W| + |normalDot g Y| *|normalDot g W| := by
        simpa only [abs_mul] using abs_add (normalDot f Y*normalDot f W) (normalDot g Y*normalDot g W)
      _ ≤ _ := by nlinarith only [h₃,h₄]
  have hlast := mul_le_mul hρ hsum (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
  unfold capRectangularPairCoefficient
  calc
    _ ≤ |normalDot f Y*normalDot g W + normalDot g Y*normalDot f W| +
        |faceDot (capRectangularFactorNormal A f) (capRectangularFactorNormal A g)*(normalDot f Y*normalDot f W+normalDot g Y*normalDot g W)| := abs_sub _ _
    _ ≤ (|normalDot f Y| *|normalDot g W|+|normalDot g Y| *|normalDot f W|) + 2*δ^2 := by
      exact add_le_add (by simpa only [abs_mul] using abs_add (normalDot f Y*normalDot g W) (normalDot g Y*normalDot f W))
        (by simpa only [abs_mul,one_mul] using hlast)
    _ ≤ _ := by nlinarith only [h₁,h₂]

theorem capOriginalCopy_pair_coefficient_bounded
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (A : Matrix (Fin p) (Fin r) ℝ)
    (a b : Bool) (f g : Face p)
    (hρ : |faceDot (capRectangularFactorNormal A f) (capRectangularFactorNormal A g)| ≤ 1) (i : Fin n) :
    ∀ᵐ z ∂μ.prod μ,
      |capRectangularPairCoefficient A f g (capOriginalCopy ξ a i z) (capOriginalCopy ξ b i z)| ≤ 4*δ^2 := by
  filter_upwards [capOriginalCopy_bounded h a i,capOriginalCopy_bounded h b i] with z ha hb
  exact capRectangularPairCoefficient_abs_le A f g _ _ h.delta_nonneg hρ
    (abs_normalDot_le_of_norm_le f ha) (abs_normalDot_le_of_norm_le g ha)
    (abs_normalDot_le_of_norm_le f hb) (abs_normalDot_le_of_norm_le g hb)

/-- The actual pair contribution has its required rδ²/(νσ²) bound for
all old/fresh copy choices. No concentration or desired remainder premise occurs. -/
theorem cap_pair_face_actual_copies
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] {n₀ n q p r : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Fin n₀ → Ω → Vector 2} {η : ℝ}
    (hbase : BoundedIndependentHypotheses μ X η) (B : Matrix (Fin 2) (Fin q) ℝ)
    {τ ρ : ℝ} (hτ : (1/2 : ℝ) ≤ τ) (hρ : ρ^2 < 1)
    (hcov : capMixedCovariance μ X B = !![τ,τ*ρ;τ*ρ,τ])
    (s : FaceSmoother p) (hband : 2*η ≤ s.bandwidth) (f₁ f₂ : Face p)
    (V : Ω × Vector q → Vector p) (hV : Measurable V) (a₀ a₁ : ℝ)
    (hproj₀ : ∀ z, normalDot f₁ (V z) = capMixedValue X B z 0+a₀)
    (hproj₁ : ∀ z, normalDot f₂ (V z) = capMixedValue X B z 1+a₁)
    {ν : Measure Ξ} [IsProbabilityMeasure ν] {ξ : Fin n → Ξ → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses ν ξ δ) (A : Matrix (Fin p) (Fin r) ℝ)
    (hA : A*A.transpose = covariance ν (sumVector ξ))
    (hangle : faceDot (capRectangularFactorNormal A f₁) (capRectangularFactorNormal A f₂) = ρ)
    (oldFresh₁ oldFresh₂ : Bool)
    (v : Fin n → (Ω × Vector q) × (Ξ × Ξ) → Vector p) (hv : ∀ i, Measurable (v i))
    {R : ℝ} (hR : 0 ≤ R)
    (hvb : ∀ i, ∀ᵐ z ∂(μ.prod (standardGaussian q)).prod (ν.prod ν), ‖v i z‖ ≤ R)
    (hsmall : R/s.bandwidth ≤ Real.log (3/2 : ℝ)) (σ : ℝ) (hσ : 0 < σ) :
    |(1/(s.bandwidth^2*σ^2))*(∫ g, ∫ ω, ∑ i, ∫ z,
      (capRectangularPairCoefficient A f₁ f₂ (capOriginalCopy ξ oldFresh₁ i z)
        (capOriginalCopy ξ oldFresh₂ i z)*repeatedDirectionScore g (capWhitenedCopy A ξ i z))*
        selectorTupleWeight s ![f₁,f₂] ((σ • A).mulVec g+V ω+v i (ω,z)) ∂ν.prod ν
          ∂μ.prod (standardGaussian q) ∂standardGaussian r)| ≤
      (9216*Real.exp 1*Real.pi^3*δ^2*(r : ℝ))/(Real.sqrt (1-ρ^2)*σ^2) := by
  let c (i : Fin n) (z : (Ω × Vector q) × (Ξ × Ξ)) :=
    capRectangularPairCoefficient A f₁ f₂ (capOriginalCopy ξ oldFresh₁ i z.2)
      (capOriginalCopy ξ oldFresh₂ i z.2)
  have hc (i : Fin n) : Measurable (c i) := by
    have hm₁ := (capOriginalCopy_measurable ξ h.measurable oldFresh₁ i).comp
      (measurable_snd : Measurable (Prod.snd : (Ω × Vector q) × (Ξ × Ξ) → Ξ × Ξ))
    have hm₂ := (capOriginalCopy_measurable ξ h.measurable oldFresh₂ i).comp
      (measurable_snd : Measurable (Prod.snd : (Ω × Vector q) × (Ξ × Ξ) → Ξ × Ξ))
    dsimp only [c]
    unfold capRectangularPairCoefficient normalDot
    split <;> split <;> fun_prop
  have hangle' : |faceDot (capRectangularFactorNormal A f₁) (capRectangularFactorNormal A f₂)| ≤ 1 := by
    rw [hangle]
    nlinarith [sq_abs ρ,abs_nonneg ρ]
  have hcb (i : Fin n) : ∀ᵐ z ∂(μ.prod (standardGaussian q)).prod (ν.prod ν), |c i z| ≤ 4*δ^2 :=
    Measure.quasiMeasurePreserving_snd.ae
      (capOriginalCopy_pair_coefficient_bounded h A oldFresh₁ oldFresh₂ f₁ f₂ hangle' i)
  have ht := cap_pair_face_complementary_remainder hbase B hτ hρ hcov s hband f₁ f₂ V hV a₀ a₁
    hproj₀ hproj₁ (σ • A) (ν.prod ν) (capWhitenedCopy A ξ)
    (capWhitenedCopy_measurable h A) (capWhitenedCopy_integrable_coordinate_pair h A)
    c hc v hv (by positivity : 0 ≤ 4*δ^2) (by norm_num : (0 : ℝ) ≤ 1) hR hcb hvb
    (fun y => by simpa only [one_mul] using capWhitenedCopy_quadratic_budget h A hA y)
    hsmall σ hσ
  dsimp only [c] at ht
  convert ht using 1
  ring

end
end RectangleCLTArxivV1
