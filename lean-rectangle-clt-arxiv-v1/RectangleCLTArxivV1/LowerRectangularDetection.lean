import RectangleCLTArxivV1.LowerUnmaskedMoments

/-! Signed detection for the actual rectangular family. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set Filter RectangleCLT RectangleCLT.Companion
open RectangleCLT.Companion.SplitV4
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false

def lowerFamilyWidthScale (P : SymmetricFamilyParameters) (n r m : ℕ) : ℝ :=
  P.amplitude*Real.log (m : ℝ)*independentAbsGaussianMean r/Real.sqrt n

def lowerFamilyMasterRemainder (P : SymmetricFamilyParameters) (n r m : ℕ) [NeZero m] : ℝ :=
  lowerRademacherMaximumConstant*Printed.rademacherGlobalError n r+
    (lowerGaussianCurvatureConstant*dimensionLog r/2)*familyShiftSecondMoments P n m

theorem lowerFamilyWidthScale_pos (P : SymmetricFamilyParameters) {n r m : ℕ}
    (hn : 1 ≤ n) (hr : 1 ≤ r) (hm : 2 ≤ m) : 0 < lowerFamilyWidthScale P n r m := by
  unfold lowerFamilyWidthScale
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm0 : (1 : ℝ) < m := by exact_mod_cast hm
  exact div_pos (mul_pos (mul_pos P.amplitude_pos (Real.log_pos hm0))
    ((by positivity : 0 < Real.sqrt (2/Real.pi)).trans_le (independentAbsGaussianMean_lower hr)))
    (Real.sqrt_pos.mpr hn0)

/-- Once the scalar error calibration is verified, the actual orthant has a
positive signed discrepancy. The universal constant also covers `r=1`. -/
theorem exists_lowerFamily_unmasked_signed_detection_constant :
    ∃ c : ℝ, 0 < c ∧ ∀ (P : ℕ → SymmetricFamilyParameters) (r m : ℕ → ℕ)
      [∀ n, NeZero (r n)] [∀ n, NeZero (m n)],
      (∀ n, 1 ≤ r n) → (∀ n, 2 ≤ m n) → Tendsto m atTop atTop →
      (∀ᶠ n : ℕ in atTop, (n : ℝ)*(P n).theta = Real.log (m n : ℝ)/2) →
      (∀ᶠ n : ℕ in atTop, (P n).pi = 1) →
      Tendsto (fun n => (P n).variance) atTop (𝓝 0) →
      (∀ᶠ n : ℕ in atTop, dimensionLog (r n) ≤ Printed.rademacherGlobalSmallConstant*Real.sqrt n) →
      Tendsto (fun n => lowerFamilyMasterRemainder (P n) n (r n) (m n)/
        lowerFamilyWidthScale (P n) n (r n) (m n)) atTop (𝓝 0) →
      ∀ᶠ n : ℕ in atTop, c*lowerFamilyWidthScale (P n) n (r n) (m n) ≤
        lowerFamilyShiftedCDFDifference (P n) n (r n) (m n) (lowerLeadingThreshold (r n)) := by
  obtain ⟨c,hc,hD⟩ := exists_leadingDensity_width_lower
  refine ⟨c/8,by positivity,?_⟩
  intro P r m _ _ hr hm hmTop hcount hπ hv hRange hRem
  have hMean := (tendsto_unmasked_shiftMeanDifference_amplitude_ratio hm hmTop hcount hπ hv).eventually
    (eventually_ge_nhds (by norm_num : (1/2 : ℝ) < 1))
  have hErr := hRem.eventually (eventually_le_nhds (show (0 : ℝ) < c/8 by positivity))
  filter_upwards [hMean,hErr,hRange,eventually_lowerFamily_master_comparison,eventually_ge_atTop 1]
    with n hnMean hnErr hnRange hnMaster hn
  have hL : 0 < Real.log (m n : ℝ) := Real.log_pos (by exact_mod_cast hm n)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hbase : 0 < (P n).amplitude*boundedShiftScale n (m n) := by
    unfold boundedShiftScale
    exact mul_pos (P n).amplitude_pos (div_pos hL (mul_pos (by norm_num) (Real.sqrt_pos.mpr hn0)))
  have hgap := (le_div_iff₀ hbase).mp hnMean
  have hgap0 : 0 ≤ familyShiftMeanDifference (P n) n (m n) :=
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) hbase.le).trans hgap
  have hwidth := lowerFamilyWidthScale_pos (P n) hn (hr n) (hm n)
  have herr := (div_le_iff₀ hwidth).mp hnErr
  have hd := hD (r n) (hr n)
  have hprod := mul_le_mul_of_nonneg_right hd hgap0
  have hprod2 := mul_le_mul_of_nonneg_left hgap
    (mul_nonneg hc.le (independentAbsGaussianMean_nonneg (r n)))
  have hid : (c*independentAbsGaussianMean (r n))*(1/2*((P n).amplitude*boundedShiftScale n (m n))) =
      (c/4)*lowerFamilyWidthScale (P n) n (r n) (m n) := by
    unfold boundedShiftScale lowerFamilyWidthScale
    ring
  have hmain : c/4*lowerFamilyWidthScale (P n) n (r n) (m n) ≤
      normalMaximumDensity (r n) (lowerLeadingThreshold (r n))*familyShiftMeanDifference (P n) n (m n) := by
    rw [← hid]
    exact hprod2.trans hprod
  have hmaster := hnMaster (P n) (r n) (m n) (hr n) (by have := hm n; omega)
    hnRange (lowerLeadingThreshold (r n))
  change |lowerFamilyShiftedCDFDifference (P n) n (r n) (m n) (lowerLeadingThreshold (r n))-
    normalMaximumDensity (r n) (lowerLeadingThreshold (r n))*familyShiftMeanDifference (P n) n (m n)| ≤
      lowerFamilyMasterRemainder (P n) n (r n) (m n) at hmaster
  have hlo := (abs_le.mp hmaster).1
  linarith

end
end RectangleCLTArxivV1
