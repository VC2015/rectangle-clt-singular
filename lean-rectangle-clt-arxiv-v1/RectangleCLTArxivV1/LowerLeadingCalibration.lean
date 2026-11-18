import RectangleCLTCompanion.SplitV4.Printed.RademacherMaximumGlobal
import RectangleCLTCompanion.SplitV4.Printed.GaussianMaximumSmoothness
import RectangleCLTCompanion.SplitV4.SymmetricFamilyShifts

/-! Uniform leading-maximum inputs, including one leading coordinate. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set Filter RectangleCLT RectangleCLT.Companion
open RectangleCLT.Companion.SplitV4
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false

def lowerRademacherMaximumConstant : ℝ := max Printed.rademacherGlobalConstant scalarBerryEsseenConstant

theorem lowerRademacherMaximumConstant_pos : 0 < lowerRademacherMaximumConstant :=
  lt_of_lt_of_le Printed.rademacherGlobalConstant_pos (le_max_left _ _)

@[simp] theorem dimensionLog_one_lower : dimensionLog 1 = 1 := by simp [dimensionLog]

theorem familyRademacherMaximum_one_error {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    |(familySignArrayLaw n 1).real {z | familyRademacherMaximum z ≤ x} - normalMaximumCDF 1 x| ≤
      lowerRademacherMaximumConstant * Printed.rademacherGlobalError n 1 := by
  have he := Printed.familyRademacher_scalar_berryEsseen hn x
  have hC : scalarBerryEsseenConstant ≤ lowerRademacherMaximumConstant := le_max_right _ _
  have hrate : 1 / Real.sqrt (n : ℝ) ≤ Printed.rademacherGlobalError n 1 := by
    simp only [Printed.rademacherGlobalError, dimensionLog_one_lower, Real.sqrt_one, one_pow]
    exact le_add_of_nonneg_right (by positivity)
  rw [familyRademacherMaximum_cdf]
  simp only [pow_one, normalMaximumCDF] at *
  calc
    _ ≤ scalarBerryEsseenConstant / Real.sqrt n := he
    _ ≤ lowerRademacherMaximumConstant / Real.sqrt n := div_le_div_of_nonneg_right hC (Real.sqrt_nonneg _)
    _ = lowerRademacherMaximumConstant * (1 / Real.sqrt n) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hrate lowerRademacherMaximumConstant_pos.le

/-- The printed uniform maximum approximation holds for every positive
leading count, without assuming that count tends to infinity. -/
theorem eventually_lowerRademacherMaximum_global_error :
    ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, (hr : 1 ≤ r) →
      letI : NeZero r := ⟨by omega⟩
      dimensionLog r ≤ Printed.rademacherGlobalSmallConstant * Real.sqrt n →
      ∀ x : ℝ, |(familySignArrayLaw n r).real {z | familyRademacherMaximum z ≤ x} - normalMaximumCDF r x| ≤
        lowerRademacherMaximumConstant * Printed.rademacherGlobalError n r := by
  filter_upwards [Printed.eventually_familyRademacherMaximum_global_error, eventually_ge_atTop 1] with n hn hn1
  intro r hr
  letI : NeZero r := ⟨by omega⟩
  intro hL x
  by_cases hr1 : r = 1
  · subst r
    exact familyRademacherMaximum_one_error hn1 x
  · have hr2 : 2 ≤ r := by omega
    have hh := hn r hr2 hL x
    have hE : 0 ≤ Printed.rademacherGlobalError n r := by unfold Printed.rademacherGlobalError; positivity
    exact hh.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hE)

def lowerGaussianCurvatureConstant : ℝ :=
  max Printed.gaussianMaximumCurvatureConstant (standardNormalPDF 0)

theorem lowerGaussianCurvatureConstant_pos : 0 < lowerGaussianCurvatureConstant :=
  lt_of_lt_of_le Printed.gaussianMaximumCurvatureConstant_pos (le_max_left _ _)

theorem normalMaximumCDF_second_derivative_bound_positive_count {r : ℕ} (hr : 1 ≤ r) (x : ℝ) :
    |deriv (deriv (normalMaximumCDF r)) x| ≤ lowerGaussianCurvatureConstant * dimensionLog r := by
  by_cases hr1 : r = 1
  · subst r
    have hF : normalMaximumCDF 1 = standardNormalCDF := by funext t; simp [normalMaximumCDF]
    have hD : deriv standardNormalCDF = standardNormalPDF := funext (fun t => (hasDerivAt_standardNormalCDF t).deriv)
    rw [hF, hD, (hasDerivAt_standardNormalPDF x).deriv, dimensionLog_one_lower, mul_one]
    have hb : |(-x)*standardNormalPDF x| ≤ standardNormalPDF 0 := by
      simpa only [neg_mul, abs_neg, abs_mul, abs_of_pos (standardNormalPDF_pos x)] using
        Printed.abs_mul_standardNormalPDF_le_at_zero x
    exact hb.trans (le_max_right _ _)
  · have hh := Printed.normalMaximumCDF_second_derivative_global_bound (by omega : 2 ≤ r) x
    exact hh.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (zero_le_one.trans (log_exp_mul_nat_ge_one hr)))

end
end RectangleCLTArxivV1
