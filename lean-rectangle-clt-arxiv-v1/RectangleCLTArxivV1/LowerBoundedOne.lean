import RectangleCLTArxivV1.LowerBoundedOneCalibration

/-! The explicit `1/8` bounded-width example at the end of F.5. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set Filter RectangleCLT RectangleCLT.Companion
open RectangleCLT.Companion.SplitV4
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false

theorem lowerBoundedOneTarget_pos {m : ℕ → ℕ} {n : ℕ} (hn : 1 ≤ n) (hm : 2 ≤ m n) :
    0 < lowerBoundedOneTarget m n := by
  let P := lowerBoundedOneParameters m n
  have hw := lowerFamilyGaussian_width_bounds P (r := 1) (m := m n) (by norm_num) (by omega)
    (lowerFamilyGaussianFactor P 1 (m n)) (lowerFamilyGaussianFactor_gram P 1 (m n))
  have hgpos : 0 < independentAbsGaussianMean 1 := by rw [independentAbsGaussianMean_one]; positivity
  have hGpos := (mul_pos P.scale_pos hgpos).trans_le hw.1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold lowerBoundedOneTarget
  exact mul_pos (mul_pos (div_pos (by norm_num) (Real.sqrt_pos.mpr hn0)) hGpos)
    (zero_lt_one.trans_le (log_exp_mul_nat_ge_one (by omega)))

theorem tendsto_lowerBoundedOne_target_div_widthScale {m : ℕ → ℕ}
    (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => lowerWidthScale 1 (Real.log (m n : ℝ)) (independentAbsGaussianMean 1) n)
      atTop (𝓝 0)) :
    Tendsto (fun n => lowerBoundedOneTarget m n/
      lowerFamilyWidthScale (lowerBoundedOneParameters m n) n 1 (m n)) atTop (𝓝 2) := by
  have ha : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ 1 := Eventually.of_forall (fun _ => le_rfl)
  have hw := lowerUnmaskedSequence_width_profile (r := fun _ => 1) (fun _ => by norm_num) hm hmTop ha hsmall
  have hh := (hw.mul (Printed.dimensionLog_nat_log_ratio.comp hmTop)).const_mul 2
  norm_num only [mul_one] at hh
  apply hh.congr'
  filter_upwards [eventually_lowerUnmaskedSequence_fields (r := fun _ => 1) (fun _ => by norm_num) hm hmTop ha hsmall,
    eventually_ge_atTop 1] with n hnFields hn
  have hamp : (lowerBoundedOneParameters m n).amplitude = 1 := hnFields.2.1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hL : 0 < Real.log (m n : ℝ) := Real.log_pos (by exact_mod_cast hm n)
  have hg : independentAbsGaussianMean 1 ≠ 0 := by rw [independentAbsGaussianMean_one]; positivity
  dsimp only [Pi.mul_apply,Function.comp_apply]
  change 2*(gaussianMaximumMean (lowerFamilyGaussianFactor (lowerBoundedOneParameters m n) 1 (m n))/
    independentAbsGaussianMean 1*(dimensionLog (m n)/Real.log (m n : ℝ))) = _
  unfold lowerBoundedOneTarget lowerFamilyWidthScale
  rw [hamp]
  field_simp [(Real.sqrt_pos.mpr hn0).ne',hL.ne',hg]
  ring

theorem tendsto_lowerBoundedOne_signed_div_target {m : ℕ → ℕ} [∀ n, NeZero (m n)]
    (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => lowerWidthScale 1 (Real.log (m n : ℝ)) (independentAbsGaussianMean 1) n)
      atTop (𝓝 0)) :
    Tendsto (fun n => lowerFamilyShiftedCDFDifference (lowerBoundedOneParameters m n) n 1 (m n) 0/
      lowerBoundedOneTarget m n) atTop (𝓝 (1/8)) := by
  have hh := (tendsto_lowerBoundedOne_signed_div_widthScale hm hmTop hsmall).div
    (tendsto_lowerBoundedOne_target_div_widthScale hm hmTop hsmall) (by norm_num : (2 : ℝ) ≠ 0)
  norm_num only [show (1/4 : ℝ)/2 = 1/8 by norm_num] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  dsimp only [Pi.div_apply]
  exact div_div_div_cancel_right₀
    (lowerFamilyWidthScale_pos (lowerBoundedOneParameters m n) (r := 1) (m := m n) hn (by norm_num) (hm n)).ne' _ _

theorem lowerBoundedOne_distance_ereal_liminf {m : ℕ → ℕ} [∀ n, NeZero (m n)]
    (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => lowerWidthScale 1 (Real.log (m n : ℝ)) (independentAbsGaussianMean 1) n)
      atTop (𝓝 0)) :
    ((1/8 : ℝ) : EReal) ≤ liminf (fun n : ℕ =>
      ((lowerFamilyComparisonDistance (lowerBoundedOneParameters m n) n 1 (m n)/lowerBoundedOneTarget m n : ℝ) : EReal)) atTop := by
  have hlim := continuous_coe_real_ereal.continuousAt.tendsto.comp
    (tendsto_lowerBoundedOne_signed_div_target hm hmTop hsmall)
  have hmono : ∀ᶠ n : ℕ in atTop,
      ((lowerFamilyShiftedCDFDifference (lowerBoundedOneParameters m n) n 1 (m n) 0/lowerBoundedOneTarget m n : ℝ) : EReal) ≤
      ((lowerFamilyComparisonDistance (lowerBoundedOneParameters m n) n 1 (m n)/lowerBoundedOneTarget m n : ℝ) : EReal) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hh := (le_abs_self _).trans
      (abs_lowerFamilyShiftedCDFDifference_le_distance (lowerBoundedOneParameters m n) n 1 (m n) 0)
    exact_mod_cast div_le_div_of_nonneg_right hh (lowerBoundedOneTarget_pos hn (hm n)).le
  have hh := liminf_le_liminf hmono
  have he := hlim.liminf_eq
  simp only [Function.comp_def] at he
  rw [he] at hh
  exact hh

/-- The actual bounded-width example has envelope two, limiting Gaussian
width `sqrt(2/pi)`, and the printed lower constant `1/8`. -/
theorem bounded_width_example_one_eighth {m : ℕ → ℕ} [∀ n, NeZero (m n)]
    (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => lowerWidthScale 1 (Real.log (m n : ℝ)) (independentAbsGaussianMean 1) n)
      atTop (𝓝 0)) :
    Tendsto (fun n => gaussianMaximumMean (lowerFamilyGaussianFactor (lowerBoundedOneParameters m n) 1 (m n)))
      atTop (𝓝 (Real.sqrt (2/Real.pi))) ∧
    (∀ᶠ n in atTop, LowerRectangularFamilyProperties (lowerBoundedOneParameters m n) n 1 (m n) ∧
      ∀ i : Fin n, ∀ z : Fin n → LowerFamilySeed 1 (m n), ‖lowerFamilyRawObservations (lowerBoundedOneParameters m n) i z‖ ≤ 2) ∧
    ((1/8 : ℝ) : EReal) ≤ liminf (fun n : ℕ =>
      ((lowerFamilyComparisonDistance (lowerBoundedOneParameters m n) n 1 (m n)/lowerBoundedOneTarget m n : ℝ) : EReal)) atTop := by
  have ha : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ 1 := Eventually.of_forall (fun _ => le_rfl)
  refine ⟨lowerUnmaskedSequence_one_width_tendsto hm hmTop ha hsmall,?_,lowerBoundedOne_distance_ereal_liminf hm hmTop hsmall⟩
  filter_upwards [eventually_lowerUnmaskedSequence_properties (r := fun _ => 1) (fun _ => 1) (fun _ => by norm_num) hm,
    eventually_lowerUnmaskedSequence_fields (r := fun _ => 1) (fun _ => by norm_num) hm hmTop ha hsmall] with n hnProp hnFields
  refine ⟨hnProp,?_⟩
  intro i z
  have hh := lowerFamilyObservation_envelope (lowerBoundedOneParameters m n) (z i)
  change ‖lowerFamilyObservation (lowerBoundedOneParameters m n) (z i)‖ ≤ 2
  have hAmp : (lowerBoundedOneParameters m n).amplitude = 1 := hnFields.2.1
  apply hh.trans
  rw [hAmp]
  have hs := familyScale_le_one (lowerBoundedOneParameters m n)
  linarith

/-- The explicit constant follows under Theorem 4's printed hypothesis
with one leading coordinate and the fixed envelope `B=2`. -/
theorem bounded_width_example_one_eighth_from_main_regime {m : ℕ → ℕ} [∀ n, NeZero (m n)]
    (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => 2*independentAbsGaussianMean 1*dimensionLog (m n)/Real.sqrt n)
      atTop (𝓝 0)) :
    Tendsto (fun n => gaussianMaximumMean (lowerFamilyGaussianFactor (lowerBoundedOneParameters m n) 1 (m n)))
      atTop (𝓝 (Real.sqrt (2/Real.pi))) ∧
    (∀ᶠ n in atTop, LowerRectangularFamilyProperties (lowerBoundedOneParameters m n) n 1 (m n) ∧
      ∀ i : Fin n, ∀ z : Fin n → LowerFamilySeed 1 (m n), ‖lowerFamilyRawObservations (lowerBoundedOneParameters m n) i z‖ ≤ 2) ∧
    ((1/8 : ℝ) : EReal) ≤ liminf (fun n : ℕ =>
      ((lowerFamilyComparisonDistance (lowerBoundedOneParameters m n) n 1 (m n)/lowerBoundedOneTarget m n : ℝ) : EReal)) atTop := by
  have hh := tendsto_lower_bounded_raw_width_scale (B := fun _ => 2) (r := fun _ => 1)
    (fun _ => le_rfl) (fun _ => by norm_num) hm (by simpa only [Nat.one_mul] using hsmall)
  have hraw : Tendsto (fun n : ℕ => lowerWidthScale 1 (Real.log (m n : ℝ))
      (independentAbsGaussianMean 1) n) atTop (𝓝 0) := by
    simpa only [show (2 : ℝ)-1=1 by norm_num] using hh
  exact bounded_width_example_one_eighth hm hmTop hraw

end
end RectangleCLTArxivV1
