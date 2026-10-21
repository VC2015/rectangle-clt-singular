import RectangleCLT.GaussianComparisonGlobal

/-! The exact Gaussian comparison statement of the manuscript: independently
select the global-eigenvalue or pair-gap coefficient of the fixed reference
covariance, omitting the full-eigenvalue alternative when it vanishes. -/

open MeasureTheory

namespace RectangleCLT

noncomputable section

def gaussianComparisonGlobalConstant : ℝ := max 1 gaussianSecondGlobalConstant

theorem gaussianComparisonGlobalConstant_ge_one : 1 ≤ gaussianComparisonGlobalConstant :=
  le_max_left _ _

theorem gaussianComparison_probability_error_le_one {p : ℕ}
    (A B : Matrix (Fin p) (Fin p) ℝ) (R : Rect p) :
    |(gaussianLaw A).real R.carrier - (gaussianLaw B).real R.carrier| ≤ 1 := by
  have hA0 : 0 ≤ (gaussianLaw A).real R.carrier := measureReal_nonneg
  have hA1 : (gaussianLaw A).real R.carrier ≤ 1 := measureReal_le_one
  have hB0 : 0 ≤ (gaussianLaw B).real R.carrier := measureReal_nonneg
  have hB1 : (gaussianLaw B).real R.carrier ≤ 1 := measureReal_le_one
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The full-eigenvalue branch has denominator equal to the square root of
the reference covariance's least eigenvalue, with no condition on the true
covariance beyond unit coordinate variances. -/
theorem gaussianComparisonGlobal {p : ℕ} (hp : 1 ≤ p)
    (A B : Matrix (Fin p) (Fin p) ℝ)
    (hA : ∀ j, (A * A.transpose) j j = 1)
    (hB : ∀ j, (B * B.transpose) j j = 1)
    (hν : 0 < fullEigenvalue (B * B.transpose)) (R : Rect p) :
    |(gaussianLaw A).real R.carrier - (gaussianLaw B).real R.carrier| ≤
      gaussianComparisonGlobalConstant * min 1
        (proxyCovarianceDiscrepancy (A * A.transpose) (B * B.transpose) *
          dimensionLog p / fullCovarianceScale (B * B.transpose)) := by
  have hT : (B * B.transpose).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose B
  have hb : 0 < fullCovarianceScale (B * B.transpose) := Real.sqrt_pos.mpr hν
  have hrate : 0 ≤ proxyCovarianceDiscrepancy (A * A.transpose) (B * B.transpose) *
      dimensionLog p / fullCovarianceScale (B * B.transpose) :=
    div_nonneg (mul_nonneg (proxyCovarianceDiscrepancy_nonneg _ _)
      (zero_le_one.trans (log_exp_mul_nat_ge_one hp))) hb.le
  have hg := gaussianComparison_rectangle_global_le hp A B hA hB hν
    (fullEigenvalue_lower hT) R
  have hlinear : |(gaussianLaw A).real R.carrier - (gaussianLaw B).real R.carrier| ≤
      gaussianComparisonGlobalConstant *
        (proxyCovarianceDiscrepancy (A * A.transpose) (B * B.transpose) *
          dimensionLog p / fullCovarianceScale (B * B.transpose)) := by
    apply hg.trans
    change gaussianSecondGlobalConstant *
        proxyCovarianceDiscrepancy (A * A.transpose) (B * B.transpose) *
          dimensionLog p / fullCovarianceScale (B * B.transpose) ≤ _
    exact (by simpa only [mul_div_assoc, mul_assoc] using
      mul_le_mul_of_nonneg_right (le_max_right 1 gaussianSecondGlobalConstant) hrate)
  simpa only [max_eq_right gaussianComparisonGlobalConstant_ge_one] using
    le_max_mul_min_of_le_one hrate (gaussianComparison_probability_error_le_one A B R) hlinear

def gaussianComparisonFullConstant : ℝ :=
  max gaussianComparisonGlobalConstant gaussianComparisonLocalConstant

theorem gaussianComparisonFullConstant_ge_one : 1 ≤ gaussianComparisonFullConstant :=
  gaussianComparisonGlobalConstant_ge_one.trans (le_max_left _ _)

/-- The complete Gaussian comparison lemma, with exactly the manuscript's
minimum and zero-eigenvalue convention. Both Gaussian laws may be singular;
only the fixed reference covariance must have a positive pair gap. -/
theorem gaussianComparisonFull {p : ℕ} (hp : 1 ≤ p)
    (A B : Matrix (Fin p) (Fin p) ℝ)
    (hA : ∀ j, (A * A.transpose) j j = 1)
    (hB : ∀ j, (B * B.transpose) j j = 1)
    (hc : 0 < pairGap (B * B.transpose)) (R : Rect p) :
    |(gaussianLaw A).real R.carrier - (gaussianLaw B).real R.carrier| ≤
      gaussianComparisonFullConstant * min 1
        (proxyCovarianceDiscrepancy (A * A.transpose) (B * B.transpose) * dimensionLog p *
          gaussianComparisonCoefficient (fullCovarianceScale (B * B.transpose))
            (pairGap (B * B.transpose))) := by
  let b := fullCovarianceScale (B * B.transpose)
  let c := pairGap (B * B.transpose)
  let Δ := proxyCovarianceDiscrepancy (A * A.transpose) (B * B.transpose)
  let L := dimensionLog p
  change |(gaussianLaw A).real R.carrier - (gaussianLaw B).real R.carrier| ≤
    gaussianComparisonFullConstant * min 1 (Δ * L * gaussianComparisonCoefficient b c)
  have hrate : 0 ≤ Δ * L := mul_nonneg (proxyCovarianceDiscrepancy_nonneg _ _)
    (zero_le_one.trans (log_exp_mul_nat_ge_one hp))
  have hlocal : |(gaussianLaw A).real R.carrier - (gaussianLaw B).real R.carrier| ≤
      gaussianComparisonFullConstant * min 1 (Δ * L / c) := by
    apply (gaussianComparisonLocal hp A B hA hB hc R).trans
    exact mul_le_mul_of_nonneg_right (le_max_right _ _)
      (le_min zero_le_one (div_nonneg hrate hc.le))
  by_cases hb : 0 < b
  · have hν : 0 < fullEigenvalue (B * B.transpose) := Real.sqrt_pos.mp hb
    have hglobal : |(gaussianLaw A).real R.carrier - (gaussianLaw B).real R.carrier| ≤
        gaussianComparisonFullConstant * min 1 (Δ * L / b) := by
      apply (gaussianComparisonGlobal hp A B hA hB hν R).trans
      exact mul_le_mul_of_nonneg_right (le_max_left _ _)
        (le_min zero_le_one (div_nonneg hrate hb.le))
    by_cases hbc : 1 / b ≤ 1 / c
    · rw [gaussianComparisonCoefficient, if_pos hb, min_eq_left hbc]
      simpa only [div_eq_mul_inv, one_mul] using hglobal
    · have hcb : 1 / c ≤ 1 / b := le_of_not_ge hbc
      rw [gaussianComparisonCoefficient, if_pos hb, min_eq_right hcb]
      simpa only [div_eq_mul_inv, one_mul] using hlocal
  · rw [gaussianComparisonCoefficient, if_neg hb]
    simpa only [div_eq_mul_inv, one_mul] using hlocal

end

end RectangleCLT
