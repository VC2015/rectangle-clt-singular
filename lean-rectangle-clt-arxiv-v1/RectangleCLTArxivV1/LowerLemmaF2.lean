import RectangleCLTCompanion.SplitV4.ShiftComparison

/-! The actual conditioning and signed Taylor comparison in Lemma F.2. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set RectangleCLT RectangleCLT.Companion
open RectangleCLT.Companion.SplitV4
noncomputable section
set_option autoImplicit false

theorem lemma_F_2_independent_conditioning {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A U : Ω → ℝ)
    (hA : Measurable A) (hU : Measurable U) (hAU : IndepFun A U μ) (t : ℝ) :
    μ.real {ω | A ω+U ω ≤ t} = ∫ ω, realCDF μ A (t-U ω) ∂μ :=
  independent_shift_cdf μ A U hA hU hAU t

theorem lemma_F_2_signed_taylor (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (hbounded : BddAbove (Set.range (fun x => |deriv (deriv F) x|))) (t y : ℝ) :
    |F (t-y)-F t+deriv F t*y| ≤ (1/2 : ℝ)*secondDerivativeSupNorm F*y^2 := by
  have hB : ∀ x, |deriv (deriv F) x| ≤ secondDerivativeSupNorm F :=
    (secondDerivativeSupNorm_le_iff F hbounded _).mp le_rfl
  convert shifted_taylor_bound F hF (secondDerivativeSupNorm F) hB t y using 1
  ring

/-- The separate independent pairs may use different probability spaces.
The shifts need neither a fixed sign nor zero mean nor joint independence. -/
theorem lemma_F_2_independently_shifted_variables
    {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Γ) [IsProbabilityMeasure ν]
    (A U : Ω → ℝ) (G V : Γ → ℝ)
    (hA : Measurable A) (hU : Measurable U) (hG : Measurable G) (hV : Measurable V)
    (hAU : IndepFun A U μ) (hGV : IndepFun G V ν)
    (hU2 : Integrable (fun ω => U ω^2) μ) (hV2 : Integrable (fun ω => V ω^2) ν)
    (hF : ContDiff ℝ 2 (realCDF ν G))
    (hbounded : BddAbove (Set.range (fun x => |deriv (deriv (realCDF ν G)) x|)))
    (ε : ℝ) (hε : 0 ≤ ε)
    (hApprox : ∀ x, |μ.real {ω | A ω ≤ x}-ν.real {ω | G ω ≤ x}| ≤ ε) (t : ℝ) :
    |μ.real {ω | A ω+U ω ≤ t}-ν.real {ω | G ω+V ω ≤ t}-
      deriv (realCDF ν G) t*((∫ ω, V ω ∂ν)-∫ ω, U ω ∂μ)| ≤
      ε+(1/2 : ℝ)*secondDerivativeSupNorm (realCDF ν G)*
        ((∫ ω, U ω^2 ∂μ)+∫ ω, V ω^2 ∂ν) := by
  have hCDF : realCDFDistance μ A ν G ≤ ε := (realCDFDistance_le_iff μ A ν G ε).mpr hApprox
  exact independent_shift_comparison μ ν A U G V hA hU hG hV hAU hGV hU2 hV2 hF hbounded ε hε hCDF t

end
end RectangleCLTArxivV1
