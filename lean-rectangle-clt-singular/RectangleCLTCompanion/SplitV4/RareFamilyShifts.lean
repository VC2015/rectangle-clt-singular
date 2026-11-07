import RectangleCLTCompanion.SplitV4.SymmetricFamilyRareCalibration
import RectangleCLTCompanion.SplitV4.SymmetricFamilyMaster
import RectangleCLTCompanion.SplitV4.SymmetricBoundedRemainder

/-! Actual mean-shift calibration for sparse masked common families. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology
namespace RectangleCLT.Companion.SplitV4
noncomputable section

def familyRareShiftScale (P : SymmetricFamilyParameters) (n : ℕ) : ℝ :=
  P.amplitude*((n : ℝ)*P.theta)/Real.sqrt n

def familyRareLowerScale (P : SymmetricFamilyParameters) (n m : ℕ) : ℝ :=
  familyRareShiftScale P n*Real.sqrt (Real.log (m : ℝ))

theorem familyRareShiftScale_pos (P : SymmetricFamilyParameters) {n : ℕ} (hn : 1 ≤ n) :
    0 < familyRareShiftScale P n := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  unfold familyRareShiftScale
  exact div_pos (mul_pos P.amplitude_pos (mul_pos hN P.theta_pos)) (Real.sqrt_pos.mpr hN)

theorem familyRareLowerScale_pos (P : SymmetricFamilyParameters) {n m : ℕ} (hn : 1 ≤ n) (hm : 2 ≤ m) :
    0 < familyRareLowerScale P n m :=
  mul_pos (familyRareShiftScale_pos P hn) (Real.sqrt_pos.mpr (Real.log_pos (by exact_mod_cast hm)))

theorem familyScale_tendsto_one {P : ℕ → SymmetricFamilyParameters}
    (hv : Tendsto (fun n => (P n).variance) atTop (𝓝 0)) :
    Tendsto (fun n => (P n).scale) atTop (𝓝 1) := by
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp
    ((tendsto_const_nhds (x := (1 : ℝ))).sub hv)
  simpa only [sub_zero, Real.sqrt_one, SymmetricFamilyParameters.scale, Function.comp_apply] using hh

theorem rare_observation_ratio_identity {a s w k Q : ℝ} (ha : a ≠ 0) (hs : s ≠ 0)
    (hw : w ≠ 0) (hk : k ≠ 0) :
    ((a/(s*w))*Q)/(a*k/w) = (Q/k)/s := by
  field_simp
  ring

theorem rare_gaussian_ratio_identity {v s M lam w : ℝ} (hs : s ≠ 0)
    (hlam : lam ≠ 0) (hw : w ≠ 0) :
    ((Real.sqrt v/s)*M)/lam = ((Real.sqrt v*w/lam)*(M/w))/s := by
  field_simp
  ring

theorem tendsto_familyRare_observation_mean_ratio {P : ℕ → SymmetricFamilyParameters}
    {m : ℕ → ℕ} [∀ n, NeZero (m n)]
    (hk : Tendsto (fun n : ℕ => (n : ℝ)*(P n).theta) atTop atTop)
    (hcover : Tendsto (fun n : ℕ => (m n : ℝ)*((P n).pi/2)^Nat.ceil (2*((n : ℝ)*(P n).theta))) atTop atTop)
    (hv : Tendsto (fun n => (P n).variance) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (∫ z, familyObservationShift (P n) z ∂familyRestArrayLaw (P n) n (m n)) /
      familyRareShiftScale (P n) n) atTop (𝓝 1) := by
  have hh := (tendsto_familyMasked_maximum_mean_ratio P m hk hcover).div
    (familyScale_tendsto_one hv) (by norm_num : (1 : ℝ) ≠ 0)
  simp only [div_one] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  dsimp only [Pi.div_apply]
  rw [familyObservationShift_integral]
  exact (rare_observation_ratio_identity (P n).amplitude_pos.ne' (P n).scale_pos.ne'
    (Real.sqrt_pos.mpr hN).ne' (mul_pos hN (P n).theta_pos).ne').symm

theorem tendsto_familyRare_gaussian_mean_ratio {P : ℕ → SymmetricFamilyParameters}
    {m : ℕ → ℕ} [∀ n, NeZero (m n)] (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hv : Tendsto (fun n => (P n).variance) atTop (𝓝 0))
    (hcoef : Tendsto (fun n : ℕ => Real.sqrt (P n).variance*Real.sqrt (2*Real.log (m n : ℝ)) /
      familyRareShiftScale (P n) n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (∫ z, familyGaussianShift (P n) z ∂standardGaussian (m n)) /
      familyRareShiftScale (P n) n) atTop (𝓝 0) := by
  have hh := (hcoef.mul (tendsto_gaussianMaximumMean_div_sqrt_log.comp hmTop)).div
    (familyScale_tendsto_one hv) (by norm_num : (1 : ℝ) ≠ 0)
  simp only [zero_mul, zero_div] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  dsimp only [Pi.div_apply, Function.comp_apply]
  rw [familyGaussianShift_integral]
  have hL : 0 < 2*Real.log (m n : ℝ) := by
    have hh := Real.log_pos (show (1 : ℝ) < m n by exact_mod_cast hm n)
    linarith
  exact (rare_gaussian_ratio_identity (P n).scale_pos.ne' (familyRareShiftScale_pos (P n) hn).ne'
    (Real.sqrt_pos.mpr hL).ne').symm

theorem tendsto_familyRare_leading_comparison_ratio {P : ℕ → SymmetricFamilyParameters}
    {m : ℕ → ℕ} [∀ n, NeZero (m n)] (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hk : Tendsto (fun n : ℕ => (n : ℝ)*(P n).theta) atTop atTop)
    (hcover : Tendsto (fun n : ℕ => (m n : ℝ)*((P n).pi/2)^Nat.ceil (2*((n : ℝ)*(P n).theta))) atTop atTop)
    (hv : Tendsto (fun n => (P n).variance) atTop (𝓝 0))
    (hcoef : Tendsto (fun n : ℕ => Real.sqrt (P n).variance*Real.sqrt (2*Real.log (m n : ℝ)) /
      familyRareShiftScale (P n) n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => normalMaximumDensity (m n) (normalMaxThreshold (m n))*
      familyShiftMeanDifference (P n) n (m n)/familyRareLowerScale (P n) n (m n))
      atTop (𝓝 (-Real.sqrt 2*Real.exp (-1))) := by
  have hMean := (tendsto_familyRare_gaussian_mean_ratio hm hmTop hv hcoef).sub
    (tendsto_familyRare_observation_mean_ratio hk hcover hv)
  simp only [zero_sub] at hMean
  have hMean' : Tendsto (fun n => familyShiftMeanDifference (P n) n (m n)/familyRareShiftScale (P n) n)
      atTop (𝓝 (-1)) := by
    simpa only [familyShiftMeanDifference, sub_div] using hMean
  have hh := ((tendsto_normalMaximumDensity_at_threshold_div_sqrt_log.comp hmTop).mul hMean').const_mul (Real.sqrt 2)
  convert hh.congr' ?_ using 1
  · ring
  filter_upwards [eventually_ge_atTop 1] with n hn
  dsimp only [Function.comp_apply]
  unfold familyRareLowerScale
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hL : 0 < Real.log (m n : ℝ) := Real.log_pos (by exact_mod_cast hm n)
  field_simp [(familyRareShiftScale_pos (P n) hn).ne', (Real.sqrt_pos.mpr hL).ne',
    (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne']
  ring

end
end RectangleCLT.Companion.SplitV4
