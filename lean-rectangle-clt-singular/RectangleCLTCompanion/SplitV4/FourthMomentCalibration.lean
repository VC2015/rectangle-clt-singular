import RectangleCLTCompanion.SplitV4.FourthMomentFamily
import RectangleCLTCompanion.SplitV4.AmplifiedSymmetricLower

/-! Exact primitive parameter and rate calibration of the actual fourth-moment family. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology
namespace RectangleCLT.Companion.SplitV4
noncomputable section

def fourthMomentLowerRate (n m : ℕ) : ℝ :=
  dimensionLog (m*m)^(5/4 : ℝ)/(n : ℝ)^(1/4 : ℝ)

theorem fourthMomentLowerRate_eq (n m : ℕ) (hm : 2 ≤ m) :
    fourthMomentLowerRate n m = fourthLowerRate n (Real.log (m : ℝ)) := by
  rw [fourthMomentLowerRate, dimensionLog_square m (by omega), fourthLowerRate]

theorem amplified_rate_quotient {a b k r : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hk : k ≠ 0) :
    (r/(a*b))/(k/a) = r/(k*b) := by
  field_simp
  ring

theorem eventually_fourthFamily_parameters {m : ℕ → ℕ}
    (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hrate : Tendsto (fun n : ℕ => fourthMomentLowerRate n (m n)) atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop,
      (fourthFamilyParameters n (m n)).theta = fourthLowerTheta n (Real.log (m n : ℝ)) ∧
      (fourthFamilyParameters n (m n)).amplitude = fourthLowerAmplitude n (Real.log (m n : ℝ)) := by
  have hEll : Tendsto (fun n : ℕ => Real.log (m n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmTop)
  have hr : Tendsto (fun n : ℕ => fourthLowerRate n (Real.log (m n : ℝ))) atTop (𝓝 0) := by
    exact hrate.congr' (Eventually.of_forall (fun n => fourthMomentLowerRate_eq n (m n) (hm n)))
  have ht := tendsto_fourthLowerTheta _ hEll hr
  filter_upwards [eventually_ge_atTop 1, ht.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1/4))]
    with n hn hquarter
  have hθ := fourthLowerTheta_pos (by omega : 0 < n) (Real.log_pos (show (1 : ℝ) < m n by exact_mod_cast hm n))
  exact ⟨fourthFamilyParameters_theta hθ hquarter, fourthFamilyParameters_amplitude hθ hquarter⟩

theorem tendsto_fourthFamily_variance {m : ℕ → ℕ}
    (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hrate : Tendsto (fun n : ℕ => fourthMomentLowerRate n (m n)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (fourthFamilyParameters n (m n)).variance) atTop (𝓝 0) := by
  have hEll : Tendsto (fun n : ℕ => Real.log (m n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmTop)
  have hr : Tendsto (fun n : ℕ => fourthLowerRate n (Real.log (m n : ℝ))) atTop (𝓝 0) := by
    exact hrate.congr' (Eventually.of_forall (fun n => fourthMomentLowerRate_eq n (m n) (hm n)))
  apply (tendsto_fourthLowerAmplitude_square_theta _ hEll hr).congr'
  filter_upwards [eventually_fourthFamily_parameters hm hmTop hrate] with n hn
  unfold SymmetricFamilyParameters.variance
  rw [fourthFamilyParameters_pi, mul_one, hn.1, hn.2]

theorem tendsto_fourthFamily_scale {m : ℕ → ℕ}
    (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hrate : Tendsto (fun n : ℕ => fourthMomentLowerRate n (m n)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (fourthFamilyParameters n (m n)).scale) atTop (𝓝 1) := by
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp
    ((tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_fourthFamily_variance hm hmTop hrate))
  simpa only [sub_zero, Real.sqrt_one, SymmetricFamilyParameters.scale, Function.comp_apply] using hh

structure FourthFamilyCalibration (m : ℕ → ℕ) : Prop where
  small : Tendsto (fun n : ℕ => Real.log (m n : ℝ)^3/n) atTop (𝓝 0)
  thetaMatch : ∀ᶠ n : ℕ in atTop,
    (fourthFamilyParameters n (m n)).theta = (boundedFamilyParameters n (m n)).theta
  amplificationLarge : ∀ᶠ n : ℕ in atTop,
    1 ≤ familyShiftAmplification (fourthFamilyParameters n (m n)) (boundedFamilyParameters n (m n))
  amplificationSmall : Tendsto (fun n : ℕ =>
    familyShiftAmplification (fourthFamilyParameters n (m n)) (boundedFamilyParameters n (m n))*
      Real.sqrt (Real.log (m n : ℝ)^3/n)) atTop (𝓝 0)
  rateRatio : Tendsto (fun n : ℕ => fourthMomentLowerRate n (m n) /
    amplifiedSymmetricLowerScale (fourthFamilyParameters n (m n)) n (m n)) atTop (𝓝 4)

theorem fourthFamilyCalibration {m : ℕ → ℕ}
    (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hrate : Tendsto (fun n : ℕ => fourthMomentLowerRate n (m n)) atTop (𝓝 0)) :
    FourthFamilyCalibration m := by
  let ell := fun n : ℕ => Real.log (m n : ℝ)
  let a := fun n => fourthLowerAmplitude n (ell n)
  let k := fun n => familyShiftAmplification (fourthFamilyParameters n (m n)) (boundedFamilyParameters n (m n))
  have hEll : Tendsto ell atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmTop)
  have hr : Tendsto (fun n : ℕ => fourthLowerRate n (ell n)) atTop (𝓝 0) := by
    exact hrate.congr' (Eventually.of_forall (fun n => fourthMomentLowerRate_eq n (m n) (hm n)))
  have hsmall := tendsto_fourthLower_cube_div ell hEll hr
  have hgood := eventually_fourthFamily_parameters hm hmTop hrate
  have ha : ∀ᶠ n : ℕ in atTop, 0 < a n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact fourthLowerAmplitude_pos (by omega : 0 < n) (Real.log_pos (show (1 : ℝ) < m n by exact_mod_cast hm n))
  have hratio : Tendsto (fun n => k n / a n) atTop (𝓝 1) := by
    have hh := (tendsto_boundedFamily_scale hm hmTop hsmall).div
      (tendsto_fourthFamily_scale hm hmTop hrate) (by norm_num : (1 : ℝ) ≠ 0)
    simp only [div_one] at hh
    apply hh.congr'
    filter_upwards [hgood, ha] with n hn hna
    dsimp only [k, a]
    unfold familyShiftAmplification
    rw [boundedFamilyParameters_amplitude, hn.2, one_mul]
    dsimp only [ell] at hna ⊢
    field_simp [hna.ne', (fourthFamilyParameters n (m n)).scale_pos.ne']
    ring
  have hk : ∀ᶠ n : ℕ in atTop, 1 ≤ k n := by
    filter_upwards [hratio.eventually (eventually_ge_nhds (by norm_num : (1/2 : ℝ) < 1)),
      (tendsto_fourthLowerAmplitude ell hEll hr).eventually (eventually_ge_atTop 2), ha] with n hnratio hnamp hna
    have hh : (1/2 : ℝ)*a n ≤ k n := (le_div_iff₀ hna).mp hnratio
    linarith
  have hksmall : Tendsto (fun n => k n*Real.sqrt (ell n^3/n)) atTop (𝓝 0) := by
    have hh := hratio.mul (tendsto_fourthLowerAmplitude_sqrt_cube ell hEll hr)
    simp only [mul_zero] at hh
    apply hh.congr'
    filter_upwards [ha] with n hn
    change (k n/a n)*(a n*Real.sqrt (ell n^3/n)) = _
    rw [← mul_assoc, div_mul_cancel₀ _ hn.ne']
  refine ⟨hsmall, ?_, hk, hksmall, ?_⟩
  · filter_upwards [hgood, boundedFamilyParameters_eventually_theta hm hmTop hsmall] with n hn hnb
    rw [hn.1, hnb]
    rfl
  · have hh := (tendsto_fourthLowerRate_div_scale ell hEll).div hratio (by norm_num : (1 : ℝ) ≠ 0)
    simp only [div_one] at hh
    apply hh.congr'
    filter_upwards [ha, eventually_boundedLowerScale_pos hmTop] with n hna hd
    dsimp only [Pi.div_apply]
    rw [fourthMomentLowerRate_eq _ _ (hm n)]
    have hda : fourthLowerScale n (ell n) = a n * boundedLowerScale n (m n) := by
      dsimp only [fourthLowerScale, boundedLowerScale, a, ell]
      ring
    rw [hda]
    unfold amplifiedSymmetricLowerScale
    change (fourthLowerRate n (ell n)/(a n*boundedLowerScale n (m n)))/(k n/a n) =
      fourthLowerRate n (ell n)/(k n*boundedLowerScale n (m n))
    exact amplified_rate_quotient hna.ne' hd.ne'
      (familyShiftAmplification_pos (fourthFamilyParameters n (m n)) (boundedFamilyParameters n (m n))).ne'


end
end RectangleCLT.Companion.SplitV4
