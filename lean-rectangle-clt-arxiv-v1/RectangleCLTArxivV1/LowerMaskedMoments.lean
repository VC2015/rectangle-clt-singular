import RectangleCLTArxivV1.LowerBoundedTheorem

/-! Actual masked rare-shift moments, with independent leading count. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set Filter RectangleCLT RectangleCLT.Companion
open RectangleCLT.Companion.SplitV4
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false

def lowerFamilyEffectiveAmplitude (P : SymmetricFamilyParameters) (n m : ℕ) : ℝ :=
  P.amplitude*((n : ℝ)*P.theta)/Real.log (m : ℝ)

def lowerFamilyRareWidthScale (P : SymmetricFamilyParameters) (n r : ℕ) : ℝ :=
  familyRareShiftScale P n*independentAbsGaussianMean r

theorem lowerFamilyEffectiveAmplitude_widthScale (P : SymmetricFamilyParameters) {n r m : ℕ}
    (hm : 2 ≤ m) : lowerWidthScale (lowerFamilyEffectiveAmplitude P n m) (Real.log (m : ℝ))
      (independentAbsGaussianMean r) n = lowerFamilyRareWidthScale P n r := by
  have hL : Real.log (m : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hm)).ne'
  unfold lowerWidthScale lowerFamilyEffectiveAmplitude lowerFamilyRareWidthScale familyRareShiftScale
  rw [div_mul_cancel₀ _ hL]
  ring

theorem lowerFamilyEffectiveAmplitude_square (P : SymmetricFamilyParameters) {n m : ℕ}
    (hm : 2 ≤ m) : P.amplitude^2*((n : ℝ)*P.theta)^2 =
      (lowerFamilyEffectiveAmplitude P n m)^2*Real.log (m : ℝ)^2 := by
  have hL : Real.log (m : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hm)).ne'
  conv_rhs => rw [← mul_pow]
  unfold lowerFamilyEffectiveAmplitude
  rw [div_mul_cancel₀ _ hL]
  ring

theorem lowerFamilyRareWidthScale_pos (P : SymmetricFamilyParameters) {n r : ℕ}
    (hn : 1 ≤ n) (hr : 1 ≤ r) : 0 < lowerFamilyRareWidthScale P n r := by
  exact mul_pos (familyRareShiftScale_pos P hn)
    ((by positivity : 0 < Real.sqrt (2/Real.pi)).trans_le (independentAbsGaussianMean_lower hr))

theorem lowerFamily_masked_shift_second_moment_budget (P : SymmetricFamilyParameters)
    {n m : ℕ} [NeZero m] (hn : 1 ≤ n) (hL : 1 ≤ Real.log (m : ℝ))
    (hk : 1 ≤ (n : ℝ)*P.theta) (hpi : P.pi*Real.log (m : ℝ) ≤ (n : ℝ)*P.theta) :
    familyShiftSecondMoments P n m ≤ (12+8*Real.exp (11/2))*
      P.amplitude^2*((n : ℝ)*P.theta)^2/n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hk0 : 0 ≤ (n : ℝ)*P.theta := by linarith
  have hdim : dimensionLog m ≤ 2*Real.log (m : ℝ) := by
    rw [dimensionLog_eq_one_add_log (Nat.one_le_iff_ne_zero.mpr (NeZero.ne m))]
    linarith
  let U := (1/(P.scale*Real.sqrt n))^2*(((n : ℝ)*P.theta)^2+(n : ℝ)*P.theta)
  have hUbase := bounded_shift_second_moment_budget (s := P.scale) (N := (n : ℝ))
    (ell := 2*((n : ℝ)*P.theta)) (θ := P.theta) (U2 := U) (V2 := 0) (C := 0)
    (lowerFamily_scale_ge_half P) hn0 (by linarith) P.theta_pos.le (by norm_num)
    (by ring) le_rfl (by positivity)
  have hU : (∫ z, familyObservationShift P z^2 ∂familyRestArrayLaw P n m) ≤
      12*P.amplitude^2*((n : ℝ)*P.theta)^2/n := by
    have hh := familyObservationShift_sq_integral_le P n m
    have hA := mul_le_mul_of_nonneg_left hUbase (sq_nonneg P.amplitude)
    apply hh.trans
    convert hA using 1 <;> dsimp only [U] <;> ring
  have hspos : 0 < P.scale^2 := sq_pos_of_pos P.scale_pos
  have hsinv : 1/P.scale^2 ≤ 4 := by
    apply (div_le_iff₀ hspos).mpr
    have hs := lowerFamily_scale_ge_half P
    nlinarith
  have hvell : P.variance*Real.log (m : ℝ) ≤ P.amplitude^2*((n : ℝ)*P.theta)^2/n := by
    apply (le_div_iff₀ hn0).mpr
    have hh := mul_le_mul_of_nonneg_left hpi (mul_nonneg (sq_nonneg P.amplitude) hk0)
    unfold SymmetricFamilyParameters.variance
    convert hh using 1 <;> ring
  have hV : (∫ z, familyGaussianShift P z^2 ∂standardGaussian m) ≤
      8*Real.exp (11/2)*(P.amplitude^2*((n : ℝ)*P.theta)^2/n) := by
    have hh := Printed.familyGaussianShift_sq_integral_le_printed P m
    rw [div_pow,Real.sq_sqrt P.variance_pos.le] at hh
    have h1 := mul_le_mul_of_nonneg_left hsinv P.variance_pos.le
    have h2 := mul_le_mul_of_nonneg_left hdim (Real.exp_pos (11/2)).le
    have h3 := mul_le_mul h1 h2 (mul_nonneg (Real.exp_pos _).le
      (zero_le_one.trans (log_exp_mul_nat_ge_one (Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)))))
      (mul_nonneg P.variance_pos.le (by norm_num : (0 : ℝ) ≤ 4))
    have h4 := mul_le_mul_of_nonneg_left hvell (show 0 ≤ 8*Real.exp (11/2) by positivity)
    apply hh.trans
    apply le_trans _ h4
    convert h3 using 1 <;> ring
  unfold familyShiftSecondMoments
  exact (add_le_add hU hV).trans_eq (by ring)

end
end RectangleCLTArxivV1
