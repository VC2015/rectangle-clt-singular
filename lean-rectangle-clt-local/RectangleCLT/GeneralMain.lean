import RectangleCLT.UnequalMasterMain
import RectangleCLT.GeneralOptimization

/-! Proposition 2 with only a positive pairwise correlation gap. The
nonlinear branches and both sharp spectral alternatives are independently
selected by the proved master estimate and bandwidth optimizer. -/

open MeasureTheory

universe u

namespace RectangleCLT

noncomputable section

def generalCLTConstant : ℝ := max 1 (12 * unequalMasterConstant)

theorem generalCLTConstant_ge_one : 1 ≤ generalCLTConstant := le_max_left _ _

/-- The exact general bounded rectangle CLT, including singular local
three- and four-coordinate covariance matrices and aggregate cancellation. -/
theorem generalRectangleCLT : GeneralRectangleCLT.{u} generalCLTConstant := by
  intro Ω _ μ _ p n hp hn ξ δ A hdata hunit hc hA R
  change rectangleError μ (sumVector ξ) A R ≤ max 1 (12 * unequalMasterConstant) * min 1
    (generalCoefficientRate δ (gamma3 μ ξ) (gamma4 μ ξ) (dimensionLog p)
      (fullCovarianceScale (covariance μ (sumVector ξ)))
      (pairGap (covariance μ (sumVector ξ)))
      (a3 (covariance μ (sumVector ξ))) (a4 (covariance μ (sumVector ξ))))
  apply general_rate_of_master
    (hdata.delta_pos hp hunit) (gamma3_nonneg μ ξ) (gamma4_nonneg μ ξ)
    (log_exp_mul_nat_ge_one hp) hc
    (zero_le_one.trans unequalMasterConstant_ge_one)
    (rectangleError_le_one μ (sumVector ξ) A R)
  intro h hband
  have hdiag : ∀ j, (A * A.transpose) j j = 1 := by
    intro j
    rw [hA]
    exact hunit j
  have hgap : 0 < min (pairGap (covariance μ (sumVector ξ)))
      (pairGap (A * A.transpose)) := by
    rw [hA, min_self]
    exact hc
  have hm := unequalMasterEstimate μ p n hp hn ξ δ A hdata hunit hdiag hgap R h hband
  have hzero : proxyCovarianceDiscrepancy (covariance μ (sumVector ξ))
      (covariance μ (sumVector ξ)) = 0 := by
    apply le_antisymm _ (proxyCovarianceDiscrepancy_nonneg _ _)
    apply (Finset.fold_max_le _).mpr
    exact ⟨le_rfl, fun _ _ => by simp⟩
  convert hm using 1 <;>
    simp only [unequalMasterDataRate, unequalMasterRate, hA, hzero,
      min_self, zero_mul, zero_add, dimensionLog] <;> ring

theorem generalRectangleCLTExists : GeneralRectangleCLTExists.{u} :=
  ⟨generalCLTConstant, generalCLTConstant_ge_one, generalRectangleCLT⟩

end

end RectangleCLT
