import RectangleCLT.GlobalBoundedAssembly
import Mathlib.Data.Real.StarOrdered

/-! Consequences of the combined rectangle theorem. These implication
lemmas retain their combined-theorem premise explicitly. The factor
`fullCovarianceScale² = fullEigenvalue` is used throughout. -/

open MeasureTheory

universe u

namespace RectangleCLT

noncomputable section

private theorem min_one_nat_mul_le (a : ℝ) {m : ℝ} (hm : 1 ≤ m) :
    min 1 (m * a) ≤ m * min 1 a := by
  by_cases ha : a ≤ 1
  · rw [min_eq_right ha]
    exact min_le_right _ _
  · rw [min_eq_left (le_of_not_ge ha), mul_one]
    exact (min_le_left _ _).trans hm

/-- The full-eigenvalue form follows with the same universal constant.
The local covariance hypotheses are derived from the positive full value. -/
theorem rectangleError_le_eigenvalueRate_of_combined {C : ℝ} (hC : 0 ≤ C)
    (hcombined : CombinedRectangleCLT.{u} C)
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p n : ℕ} (hp : 1 ≤ p) (hn : 1 ≤ n) (ξ : Fin n → Ω → Vector p) {δ : ℝ}
    (hdata : BoundedIndependentHypotheses μ ξ δ)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = covariance μ (sumVector ξ))
    (hν : 0 < fullEigenvalue (covariance μ (sumVector ξ))) (R : Rect p) :
    rectangleError μ (sumVector ξ) A R ≤ C * min 1
      ((gamma3 μ ξ * dimensionLog p * Real.sqrt (dimensionLog p) +
        Real.sqrt (gamma4 μ ξ) * dimensionLog p + δ * Real.sqrt (dimensionLog p)) /
          fullEigenvalue (covariance μ (sumVector ξ))) := by
  let Q := covariance μ (sumVector ξ)
  have hQ : Q.PosSemidef := by
    rw [show Q = A * A.transpose from hA.symm]
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose A
  have hlocal := localCovarianceHypotheses_of_fullEigenvalue_pos (by omega) hQ hunit hν
  have hb : 0 < fullCovarianceScale Q := Real.sqrt_pos.mpr hν
  have hsquare := fullCovarianceScale_sq (by omega : 0 < p) hQ
  have hbc : fullCovarianceScale Q ^ 2 ≤ pairGap Q := by
    rw [hsquare]
    exact fullEigenvalue_le_pairGap (by omega) hQ hunit
  have hcoeff := combinedCoefficientRate_le_eigenvalueRate
    hdata.delta_nonneg (gamma3_nonneg μ ξ)
    (show 0 ≤ dimensionLog p from le_trans (by norm_num) (log_exp_mul_nat_ge_one hp)) hb hbc
      (a₃ := a3 Q) (a₄ := a4 Q) (γ₄ := gamma4 μ ξ)
  rw [hsquare] at hcoeff
  exact (hcombined μ p n hp hn ξ δ A hdata hlocal hA R).trans
    (mul_le_mul_of_nonneg_left (min_le_min le_rfl hcoeff) hC)

/-- Aronow--Lopatto recovery with envelope `δ`: the rate is
`δ*log(e*p)^(3/2)/fullEigenvalue`, up to one absolute constant. -/
theorem rectangleError_le_AronowLopattoRate_of_combined {C : ℝ} (hC : 0 ≤ C)
    (hcombined : CombinedRectangleCLT.{u} C)
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p n : ℕ} (hp : 1 ≤ p) (hn : 1 ≤ n) (ξ : Fin n → Ω → Vector p) {δ : ℝ}
    (hdata : BoundedIndependentHypotheses μ ξ δ)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = covariance μ (sumVector ξ))
    (hν : 0 < fullEigenvalue (covariance μ (sumVector ξ))) (R : Rect p) :
    rectangleError μ (sumVector ξ) A R ≤ (3 * C) * min 1
      (δ * dimensionLog p * Real.sqrt (dimensionLog p) /
        fullEigenvalue (covariance μ (sumVector ξ))) := by
  have hb := rectangleError_le_eigenvalueRate_of_combined hC hcombined μ hp hn ξ
    hdata hunit A hA hν R
  have hnum := rate_numerator_le_three_delta_log_sqrt hdata.delta_nonneg
    (hdata.gamma3_le_delta hunit) (hdata.gamma4_le_delta_sq hunit)
    (log_exp_mul_nat_ge_one hp)
  have hrate := div_le_div_of_nonneg_right hnum hν.le
  calc
    _ ≤ C * min 1 ((gamma3 μ ξ * dimensionLog p * Real.sqrt (dimensionLog p) +
        Real.sqrt (gamma4 μ ξ) * dimensionLog p + δ * Real.sqrt (dimensionLog p)) /
          fullEigenvalue (covariance μ (sumVector ξ))) := hb
    _ ≤ C * min 1 (3 * (δ * dimensionLog p * Real.sqrt (dimensionLog p) /
        fullEigenvalue (covariance μ (sumVector ξ)))) := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply min_le_min le_rfl
      exact hrate.trans_eq (by simp only [dimensionLog]; ring)
    _ ≤ C * (3 * min 1 (δ * dimensionLog p * Real.sqrt (dimensionLog p) /
        fullEigenvalue (covariance μ (sumVector ξ)))) :=
      mul_le_mul_of_nonneg_left (min_one_nat_mul_le _ (by norm_num : (1 : ℝ) ≤ 3)) hC
    _ = _ := by ring

/-- Vanishing aggregate signed third moments improve the logarithmic
factor from `L^(3/2)` to `L`. -/
theorem rectangleError_le_cancelledEigenvalueRate_of_combined {C : ℝ} (hC : 0 ≤ C)
    (hcombined : CombinedRectangleCLT.{u} C)
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p n : ℕ} (hp : 1 ≤ p) (hn : 1 ≤ n) (ξ : Fin n → Ω → Vector p) {δ : ℝ}
    (hdata : BoundedIndependentHypotheses μ ξ δ)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (hthird : gamma3 μ ξ = 0) (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = covariance μ (sumVector ξ))
    (hν : 0 < fullEigenvalue (covariance μ (sumVector ξ))) (R : Rect p) :
    rectangleError μ (sumVector ξ) A R ≤ (2 * C) * min 1
      (δ * dimensionLog p / fullEigenvalue (covariance μ (sumVector ξ))) := by
  have hb := rectangleError_le_eigenvalueRate_of_combined hC hcombined μ hp hn ξ
    hdata hunit A hA hν R
  have hnum := rate_numerator_le_two_delta_log_of_third_eq_zero hdata.delta_nonneg
    hthird (hdata.gamma4_le_delta_sq hunit) (log_exp_mul_nat_ge_one hp)
  have hrate := div_le_div_of_nonneg_right hnum hν.le
  calc
    _ ≤ C * min 1 ((gamma3 μ ξ * dimensionLog p * Real.sqrt (dimensionLog p) +
        Real.sqrt (gamma4 μ ξ) * dimensionLog p + δ * Real.sqrt (dimensionLog p)) /
          fullEigenvalue (covariance μ (sumVector ξ))) := hb
    _ ≤ C * min 1 (2 * (δ * dimensionLog p /
        fullEigenvalue (covariance μ (sumVector ξ)))) := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply min_le_min le_rfl
      exact hrate.trans_eq (by simp only [dimensionLog]; ring)
    _ ≤ C * (2 * min 1 (δ * dimensionLog p /
        fullEigenvalue (covariance μ (sumVector ξ)))) :=
      mul_le_mul_of_nonneg_left (min_one_nat_mul_le _ (by norm_num : (1 : ℝ) ≤ 2)) hC
    _ = _ := by ring

/-- The original bounded full-spectral statement follows as well, for any
lower scale `b` supplied by the substantive data hypotheses. -/
theorem boundedRectangleCLT_of_combined {C : ℝ} (hC : 0 ≤ C)
    (hcombined : CombinedRectangleCLT.{u} C) : BoundedRectangleCLT.{u} C := by
  intro Ω _ μ _ p n hp hn ξ δ b A hdata hA R
  have hfull : b ^ 2 ≤ fullEigenvalue (covariance μ (sumVector ξ)) :=
    le_fullEigenvalue (by omega) hdata.spectral_lower
  have hν : 0 < fullEigenvalue (covariance μ (sumVector ξ)) :=
    (sq_pos_of_pos hdata.b_pos).trans_le hfull
  have hb := rectangleError_le_eigenvalueRate_of_combined hC hcombined μ hp hn ξ
    hdata.toBoundedIndependentHypotheses hdata.unit_diagonal A hA hν R
  have hL : 0 < dimensionLog p :=
    lt_of_lt_of_le (by norm_num) (log_exp_mul_nat_ge_one hp)
  have hγ₃ := gamma3_nonneg μ ξ
  have hδ := hdata.delta_nonneg
  have hnum : 0 ≤ gamma3 μ ξ * dimensionLog p * Real.sqrt (dimensionLog p) +
      Real.sqrt (gamma4 μ ξ) * dimensionLog p + δ * Real.sqrt (dimensionLog p) := by
    positivity
  exact hb.trans (mul_le_mul_of_nonneg_left
    (min_le_min le_rfl
      (div_le_div_of_nonneg_left hnum (sq_pos_of_pos hdata.b_pos) hfull)) hC)

end

end RectangleCLT
