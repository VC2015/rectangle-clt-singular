import RectangleCLTArxivV1.LowerUnmaskedCalibration

/-! Actual shift remainder bounds with the amplitude retained. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set Filter RectangleCLT RectangleCLT.Companion
open RectangleCLT.Companion.SplitV4
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false

theorem lowerFamily_scale_ge_half (P : SymmetricFamilyParameters) : 1/2 ≤ P.scale := by
  have hs := P.scale_sq
  have hv := P.variance_lt_half
  change P.variance < 1/2 at hv
  have hp := P.scale_pos
  nlinarith

theorem lowerFamily_unmasked_shift_second_moment_budget (P : SymmetricFamilyParameters)
    {n m : ℕ} [NeZero m] (hn : 1 ≤ n) (hL : 1 ≤ Real.log (m : ℝ))
    (hπ : P.pi = 1) (hcount : (n : ℝ)*P.theta = Real.log (m : ℝ)/2) :
    familyShiftSecondMoments P n m ≤
      (3+4*Real.exp (11/2))*P.amplitude^2*Real.log (m : ℝ)^2/n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  let U := (1/(P.scale*Real.sqrt n))^2 * (((n : ℝ)*P.theta)^2+(n : ℝ)*P.theta)
  let V := (Real.sqrt P.theta/P.scale)^2 * (Real.exp (11/2)*(1+Real.log (m : ℝ)))
  have hB : U+V ≤ (3+4*Real.exp (11/2))*Real.log (m : ℝ)^2/n :=
    bounded_shift_second_moment_budget (lowerFamily_scale_ge_half P) hn0 hL P.theta_pos.le
      (Real.exp_pos _).le hcount le_rfl le_rfl
  have hU : (∫ z, familyObservationShift P z^2 ∂familyRestArrayLaw P n m) ≤ P.amplitude^2*U := by
    convert familyObservationShift_sq_integral_le P n m using 1 <;> dsimp only [U] <;> ring
  have hV : (∫ z, familyGaussianShift P z^2 ∂standardGaussian m) ≤ P.amplitude^2*V := by
    have hh := Printed.familyGaussianShift_sq_integral_le_printed P m
    rw [div_pow,Real.sq_sqrt P.variance_pos.le,SymmetricFamilyParameters.variance,hπ,
      dimensionLog_eq_one_add_log (Nat.one_le_iff_ne_zero.mpr (NeZero.ne m))] at hh
    convert hh using 1
    dsimp only [V]
    rw [div_pow,Real.sq_sqrt P.theta_pos.le]
    ring
  calc
    familyShiftSecondMoments P n m ≤ P.amplitude^2*(U+V) := by
      unfold familyShiftSecondMoments
      nlinarith only [hU,hV]
    _ ≤ P.amplitude^2*((3+4*Real.exp (11/2))*Real.log (m : ℝ)^2/n) :=
      mul_le_mul_of_nonneg_left hB (sq_nonneg _)
    _ = _ := by ring

theorem eventually_lowerFamily_unmasked_shift_second_moment_budget
    {P : ℕ → SymmetricFamilyParameters} {m : ℕ → ℕ} [∀ n, NeZero (m n)]
    (hmTop : Tendsto m atTop atTop)
    (hπ : ∀ᶠ n : ℕ in atTop, (P n).pi = 1)
    (hcount : ∀ᶠ n : ℕ in atTop, (n : ℝ)*(P n).theta = Real.log (m n : ℝ)/2) :
    ∀ᶠ n : ℕ in atTop, familyShiftSecondMoments (P n) n (m n) ≤
      (3+4*Real.exp (11/2))*(P n).amplitude^2*Real.log (m n : ℝ)^2/n := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmTop)
  filter_upwards [hπ,hcount,hlog.eventually (eventually_ge_atTop 1),eventually_ge_atTop 1]
    with n hnπ hnc hnL hn
  exact lowerFamily_unmasked_shift_second_moment_budget (P n) hn hnL hnπ hnc

end
end RectangleCLTArxivV1
