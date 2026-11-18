import RectangleCLTArxivV1.SupplementalGConditionalAE
import RectangleCLTArxivV1.SupplementalGFaceMass
import RectangleCLTArxivV1.SupplementalGHermiteNuclearMoments

/-! The actual one-face complementary remainder estimate under jointly
almost-sure shift and coefficient envelopes. The local-mass
input of conditional restoration is discharged by the raw G.2 model. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open RectangleCLT.FaceSmoother
open scoped BigOperators
noncomputable section
set_option autoImplicit false

/-- The signed one-face H3 expectation has the required linear rank cost,
without a concentration or analytic-remainder hypothesis. -/
theorem cap_single_face_complementary_expectation_ae
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] {n q p r N : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Fin n → Ω → Vector 2} {δ : ℝ}
    (hdata : BoundedIndependentHypotheses μ X δ) (B : Matrix (Fin 2) (Fin q) ℝ)
    (hvar : (1/2 : ℝ) ≤ capMixedCovariance μ X B 0 0)
    (s : FaceSmoother p) (hband : δ ≤ s.bandwidth) (f : Face p)
    (V : Ω × Vector q → Vector p) (hV : Measurable V) (a : ℝ)
    (hproj : ∀ z, normalDot f (V z) = capMixedValue X B z 0+a)
    (A : Matrix (Fin p) (Fin r) ℝ) (u : Vector r) (hr : 1 ≤ r) (hu : vectorNormSq u = 1)
    (κ : Measure Ξ) [SFinite κ]
    (Z : Fin N → Ξ → Vector r) (hZm : ∀ i, Measurable (Z i))
    (hZ : ∀ i j l, Integrable (fun ξ => Z i ξ j*Z i ξ l) κ)
    (c : Fin N → (Ω × Vector q) × Ξ → ℝ) (hc : ∀ i, Measurable (c i))
    (v : Fin N → (Ω × Vector q) × Ξ → Vector p) (hv : ∀ i, Measurable (v i))
    {b K R : ℝ} (hb : 0 ≤ b) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hcb : ∀ i, ∀ᵐ z ∂(μ.prod (standardGaussian q)).prod κ, |c i z| ≤ b)
    (hvb : ∀ i, ∀ᵐ z ∂(μ.prod (standardGaussian q)).prod κ, ‖v i z‖ ≤ R)
    (hbudget : ∀ y : Vector r, ∑ i, ∫ ξ, (faceDot y (Z i ξ))^2 ∂κ ≤ K*vectorNormSq y)
    (hsmall : R/s.bandwidth ≤ Real.log (3/2 : ℝ)) :
    |∫ g, ∫ ω, ∑ i, ∫ ξ,
      (c i (ω,ξ)*capThirdHermiteScore u (Z i ξ) g)*
        selectorTupleWeight s ![f] (A.mulVec g+V ω+v i (ω,ξ)) ∂κ
          ∂μ.prod (standardGaussian q) ∂standardGaussian r| ≤
      480*Real.exp (1/2)*Real.sqrt (Real.pi/capGaussianExponent)*
        s.bandwidth*b*K*(r : ℝ) := by
  have hh := s.bandwidth_pos
  have hmass (g : Vector r) : (∫ ω, selectorTupleWeight s ![f] (A.mulVec g+V ω)
      ∂μ.prod (standardGaussian q)) ≤
      16*Real.exp (1/2)*s.bandwidth*Real.sqrt (Real.pi/capGaussianExponent) := by
    apply cap_original_single_face_mass hdata B hvar s hband f
      (fun ω => A.mulVec g+V ω) (measurable_const.add hV) (a+normalDot f (A.mulVec g))
    intro ω
    rw [normalDot_add,hproj]
    ring
  have ht := capThirdHermite_conditional_mass_bound_ae s (μ.prod (standardGaussian q)) κ A V hV
    Z hZm hZ c hc v hv ![f] u hb hK hR (by positivity) hcb hvb hbudget hsmall
    (capThirdHermiteMatrix_nuclear_integrable u) hmass
  apply ht.2.trans
  have hM : 0 ≤ 16*Real.exp (1/2)*s.bandwidth*Real.sqrt (Real.pi/capGaussianExponent) := by positivity
  have hC : 0 ≤ (2*3^1*b*K)*(16*Real.exp (1/2)*s.bandwidth*Real.sqrt (Real.pi/capGaussianExponent)) := by positivity
  calc
    _ ≤ ((2*3^1*b*K)*(16*Real.exp (1/2)*s.bandwidth*Real.sqrt (Real.pi/capGaussianExponent)))*(5*r) :=
      mul_le_mul_of_nonneg_left (capThirdHermite_integral_nuclear_le u hr hu) hC
    _ = _ := by ring

/-- The one-face term with the exact fourth-tensor prefactor. Its scale is
linear in rank and σ⁻³, as required by the complementary remainder. -/
theorem cap_single_face_complementary_remainder_ae
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] {n q p r N : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Fin n → Ω → Vector 2} {δ : ℝ}
    (hdata : BoundedIndependentHypotheses μ X δ) (B : Matrix (Fin 2) (Fin q) ℝ)
    (hvar : (1/2 : ℝ) ≤ capMixedCovariance μ X B 0 0)
    (s : FaceSmoother p) (hband : δ ≤ s.bandwidth) (f : Face p)
    (V : Ω × Vector q → Vector p) (hV : Measurable V) (a : ℝ)
    (hproj : ∀ z, normalDot f (V z) = capMixedValue X B z 0+a)
    (A : Matrix (Fin p) (Fin r) ℝ) (u : Vector r) (hr : 1 ≤ r) (hu : vectorNormSq u = 1)
    (κ : Measure Ξ) [SFinite κ]
    (Z : Fin N → Ξ → Vector r) (hZm : ∀ i, Measurable (Z i))
    (hZ : ∀ i j l, Integrable (fun ξ => Z i ξ j*Z i ξ l) κ)
    (c : Fin N → (Ω × Vector q) × Ξ → ℝ) (hc : ∀ i, Measurable (c i))
    (v : Fin N → (Ω × Vector q) × Ξ → Vector p) (hv : ∀ i, Measurable (v i))
    {b K R : ℝ} (hb : 0 ≤ b) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hcb : ∀ i, ∀ᵐ z ∂(μ.prod (standardGaussian q)).prod κ, |c i z| ≤ b)
    (hvb : ∀ i, ∀ᵐ z ∂(μ.prod (standardGaussian q)).prod κ, ‖v i z‖ ≤ R)
    (hbudget : ∀ y : Vector r, ∑ i, ∫ ξ, (faceDot y (Z i ξ))^2 ∂κ ≤ K*vectorNormSq y)
    (hsmall : R/s.bandwidth ≤ Real.log (3/2 : ℝ))
    (σ : ℝ) (hσ : 0 < σ) :
    |-(1/(s.bandwidth*σ^3))*(∫ g, ∫ ω, ∑ i, ∫ ξ,
      (c i (ω,ξ)*capThirdHermiteScore u (Z i ξ) g)*
        selectorTupleWeight s ![f] (A.mulVec g+V ω+v i (ω,ξ)) ∂κ
          ∂μ.prod (standardGaussian q) ∂standardGaussian r)| ≤
      (480*Real.exp (1/2)*Real.sqrt (Real.pi/capGaussianExponent)*b*K*(r : ℝ))/σ^3 := by
  have hh := s.bandwidth_pos
  have ht := cap_single_face_complementary_expectation_ae hdata B hvar s hband f V hV a hproj
    A u hr hu κ Z hZm hZ c hc v hv hb hK hR hcb hvb hbudget hsmall
  calc
    _ = (1/(s.bandwidth*σ^3))*|∫ g, ∫ ω, ∑ i, ∫ ξ,
      (c i (ω,ξ)*capThirdHermiteScore u (Z i ξ) g)*
        selectorTupleWeight s ![f] (A.mulVec g+V ω+v i (ω,ξ)) ∂κ
          ∂μ.prod (standardGaussian q) ∂standardGaussian r| := by
      rw [abs_mul,abs_neg,abs_of_pos (one_div_pos.mpr (mul_pos hh (pow_pos hσ 3)))]
    _ ≤ (1/(s.bandwidth*σ^3))*(480*Real.exp (1/2)*Real.sqrt (Real.pi/capGaussianExponent)*
        s.bandwidth*b*K*(r : ℝ)) :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    _ = _ := by field_simp only [hh.ne',hσ.ne']; ring

end
end RectangleCLTArxivV1
