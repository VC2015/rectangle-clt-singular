import RectangleCLTCompanion.SplitV4.Printed.LowerModerateGeneral

/-! The literal uniform scalar moderate-tail Lemma F.1 for actual laws. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set RectangleCLT RectangleCLT.Companion
open RectangleCLT.Companion.SplitV4
open scoped BigOperators
universe u
noncomputable section
set_option autoImplicit false

def scalarModerateTailRadius : ℝ := 1/moderateTailSmallConstant
def scalarModerateTailErrorConstant : ℝ := moderateTailRemainderConstant

theorem scalarModerateTailRadius_pos : 0 < scalarModerateTailRadius :=
  div_pos zero_lt_one moderateTailSmallConstant_bounds.1

theorem scalarModerateTailErrorConstant_pos : 0 < scalarModerateTailErrorConstant :=
  moderateTailRemainderConstant_bounds.1

/-- The actual strict tail is positive and has the asserted cubic log
correction. No tail comparison or distributional construction is an input. -/
theorem lemma_F_1_bound {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (η : Fin n → Ω → ℝ) (δ : ℝ)
    (hn : 1 ≤ n) (hη : ∀ i, Measurable (η i)) (hind : iIndepFun η μ) (hδ : 0 < δ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |η i ω| ≤ δ)
    (hcenter : ∀ i, (∫ ω, η i ω ∂μ) = 0)
    (hvariance : (∑ i, ∫ ω, η i ω^2 ∂μ) = 1) {x : ℝ} (hx : 0 ≤ x)
    (hsmall : δ*(1+x) ≤ scalarModerateTailRadius) :
    0 < μ.real {ω | x < ∑ i, η i ω} ∧
    |Real.log (μ.real {ω | x < ∑ i, η i ω}/standardNormalUpperTail x)-
      (∑ i, ∫ ω, η i ω^3 ∂μ)*x^3/6| ≤
      scalarModerateTailErrorConstant*(δ*(1+x)+δ^2*x^4) := by
  have hs : moderateTailSmallConstant*(δ*(1+x)) ≤ 1 := by
    have hh := (le_div_iff₀ moderateTailSmallConstant_bounds.1).mp hsmall
    nlinarith only [hh]
  simpa only [moderateScalarSum,moderateArrayGamma,scalarModerateTailErrorConstant] using
    Printed.moderateScalarTail_bound_printed hn hη hind hδ.le hbound hcenter hvariance hx hs

/-- Absolute constants precede the probability space, array, summand
bound and threshold, exactly as in the printed Lemma F.1. -/
theorem lemma_F_1_uniform_scalar_moderate_tail :
    ∃ c₀ C : ℝ, 0 < c₀ ∧ 0 < C ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        {n : ℕ} (η : Fin n → Ω → ℝ) (δ : ℝ),
        1 ≤ n → (∀ i, Measurable (η i)) → iIndepFun η μ → 0 < δ →
        (∀ i, ∀ᵐ ω ∂μ, |η i ω| ≤ δ) → (∀ i, (∫ ω, η i ω ∂μ) = 0) →
        (∑ i, ∫ ω, η i ω^2 ∂μ) = 1 →
        ∀ x : ℝ, 0 ≤ x → δ*(1+x) ≤ c₀ →
          0 < μ.real {ω | x < ∑ i, η i ω} ∧
          |Real.log (μ.real {ω | x < ∑ i, η i ω}/standardNormalUpperTail x)-
            (∑ i, ∫ ω, η i ω^3 ∂μ)*x^3/6| ≤ C*(δ*(1+x)+δ^2*x^4) := by
  refine ⟨scalarModerateTailRadius,scalarModerateTailErrorConstant,
    scalarModerateTailRadius_pos,scalarModerateTailErrorConstant_pos,?_⟩
  intro Ω _ μ _ n η δ hn hη hind hδ hbound hcenter hvariance x hx hsmall
  exact lemma_F_1_bound μ η δ hn hη hind hδ hbound hcenter hvariance hx hsmall

end
end RectangleCLTArxivV1
