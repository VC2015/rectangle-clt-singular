import RectangleCLTArxivV1.SupplementalGSecondHermite
import RectangleCLTArxivV1.SupplementalGFaceMass

/-! The large-angle complementary pair estimate. The actual raw G.2
projected model discharges the mass input of signed H2 restoration. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open RectangleCLT.FaceSmoother
open scoped BigOperators
noncomputable section
set_option autoImplicit false

theorem cap_pair_face_complementary_remainder
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] {n q p r N : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Fin n → Ω → Vector 2} {δ : ℝ}
    (hdata : BoundedIndependentHypotheses μ X δ) (B : Matrix (Fin 2) (Fin q) ℝ)
    {τ ρ : ℝ} (hτ : (1/2 : ℝ) ≤ τ) (hρ : ρ^2 < 1)
    (hcov : capMixedCovariance μ X B = !![τ,τ*ρ;τ*ρ,τ])
    (s : FaceSmoother p) (hband : 2*δ ≤ s.bandwidth) (f₁ f₂ : Face p)
    (V : Ω × Vector q → Vector p) (hV : Measurable V) (a₀ a₁ : ℝ)
    (hproj₀ : ∀ z, normalDot f₁ (V z) = capMixedValue X B z 0+a₀)
    (hproj₁ : ∀ z, normalDot f₂ (V z) = capMixedValue X B z 1+a₁)
    (A : Matrix (Fin p) (Fin r) ℝ) (κ : Measure Ξ) [SFinite κ]
    (Z : Fin N → Ξ → Vector r) (hZm : ∀ i, Measurable (Z i))
    (hZ : ∀ i j l, Integrable (fun ξ => Z i ξ j*Z i ξ l) κ)
    (c : Fin N → (Ω × Vector q) × Ξ → ℝ) (hc : ∀ i, Measurable (c i))
    (v : Fin N → (Ω × Vector q) × Ξ → Vector p) (hv : ∀ i, Measurable (v i))
    {b K R : ℝ} (hb : 0 ≤ b) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hcb : ∀ i, ∀ᵐ z ∂(μ.prod (standardGaussian q)).prod κ, |c i z| ≤ b)
    (hvb : ∀ i, ∀ᵐ z ∂(μ.prod (standardGaussian q)).prod κ, ‖v i z‖ ≤ R)
    (hbudget : ∀ y : Vector r, ∑ i, ∫ ξ, (faceDot y (Z i ξ))^2 ∂κ ≤ K*vectorNormSq y)
    (hsmall : R/s.bandwidth ≤ Real.log (3/2 : ℝ)) (σ : ℝ) (hσ : 0 < σ) :
    |(1/(s.bandwidth^2*σ^2))*(∫ g, ∫ ω, ∑ i, ∫ ξ,
      (c i (ω,ξ)*repeatedDirectionScore g (Z i ξ))*
        selectorTupleWeight s ![f₁,f₂] (A.mulVec g+V ω+v i (ω,ξ)) ∂κ
          ∂μ.prod (standardGaussian q) ∂standardGaussian r)| ≤
      (2304*Real.exp 1*Real.pi^3*b*K*(r : ℝ))/(Real.sqrt (1-ρ^2)*σ^2) := by
  have hh := s.bandwidth_pos
  have hν : 0 < Real.sqrt (1-ρ^2) := Real.sqrt_pos.mpr (by linarith)
  let M := 64*Real.exp 1*Real.pi^3*s.bandwidth^2/Real.sqrt (1-ρ^2)
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hmass (g : Vector r) : (∫ ω, selectorTupleWeight s ![f₁,f₂] (A.mulVec g+V ω)
      ∂μ.prod (standardGaussian q)) ≤ M := by
    apply cap_original_pair_face_mass hdata B hτ hρ hcov s hband f₁ f₂
      (fun ω => A.mulVec g+V ω) (measurable_const.add hV)
      (a₀+normalDot f₁ (A.mulVec g)) (a₁+normalDot f₂ (A.mulVec g))
    · intro ω; rw [normalDot_add,hproj₀]; ring
    · intro ω; rw [normalDot_add,hproj₁]; ring
  have ht := capSecondHermite_conditional_mass_bound_ae s (μ.prod (standardGaussian q)) κ A V hV
    Z hZm hZ c hc v hv ![f₁,f₂] hb hK hR hM hcb hvb hbudget hsmall
    (capSecondHermite_nuclear_integrable r) hmass
  have hC : 0 ≤ (2*3^2*b*K)*M := by positivity
  have hraw := ht.2.trans (mul_le_mul_of_nonneg_left (capSecondHermite_integral_nuclear_le r) hC)
  calc
    _ = (1/(s.bandwidth^2*σ^2))*|∫ g, ∫ ω, ∑ i, ∫ ξ,
      (c i (ω,ξ)*repeatedDirectionScore g (Z i ξ))*
        selectorTupleWeight s ![f₁,f₂] (A.mulVec g+V ω+v i (ω,ξ)) ∂κ
          ∂μ.prod (standardGaussian q) ∂standardGaussian r| := by
      rw [abs_mul,abs_of_pos (one_div_pos.mpr (mul_pos (pow_pos hh 2) (pow_pos hσ 2)))]
    _ ≤ (1/(s.bandwidth^2*σ^2))*(((2*3^2*b*K)*M)*(2*r)) :=
      mul_le_mul_of_nonneg_left hraw (by positivity)
    _ = _ := by dsimp only [M]; field_simp only [hh.ne',hσ.ne',hν.ne']; ring

end
end RectangleCLTArxivV1
