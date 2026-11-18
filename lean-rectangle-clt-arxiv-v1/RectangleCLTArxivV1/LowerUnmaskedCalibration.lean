import RectangleCLTArxivV1.LowerRectangularFamily
import RectangleCLTCompanion.SplitV4.SymmetricBoundedMoments
import RectangleCLTCompanion.SplitV4.Printed.LowerGaussianShifts

/-! Actual rare-shift calibration under the weaker two-count regime. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set Filter RectangleCLT RectangleCLT.Companion
open RectangleCLT.Companion.SplitV4
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false

theorem tendsto_lowerFamily_scale {P : ℕ → SymmetricFamilyParameters}
    (hv : Tendsto (fun n => (P n).variance) atTop (𝓝 0)) :
    Tendsto (fun n => (P n).scale) atTop (𝓝 1) := by
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp
    ((tendsto_const_nhds (x := (1 : ℝ))).sub hv)
  simpa only [SymmetricFamilyParameters.scale,sub_zero,Real.sqrt_one,Function.comp_apply] using hh

theorem observationShift_amplitude_ratio_identity {s a ell N Q : ℝ}
    (hs : s ≠ 0) (ha : a ≠ 0) (hL : ell ≠ 0) (hN : 0 < N) :
    ((a/(s*Real.sqrt N))*Q)/(a*(ell/(2*Real.sqrt N))) = (Q/(ell/2))/s := by
  field_simp [(Real.sqrt_pos.mpr hN).ne']
  ring

theorem lowerFamily_theta_of_count (P : SymmetricFamilyParameters) {n : ℕ} {ell : ℝ}
    (hn : 1 ≤ n) (hcount : (n : ℝ)*P.theta = ell/2) : P.theta = ell/(2*n) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  apply (eq_div_iff (mul_ne_zero (by norm_num) hn0)).mpr
  nlinarith [hcount]

theorem tendsto_unmasked_observationShift_amplitude_ratio {P : ℕ → SymmetricFamilyParameters}
    {m : ℕ → ℕ} [∀ n, NeZero (m n)] (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hcount : ∀ᶠ n : ℕ in atTop, (n : ℝ)*(P n).theta = Real.log (m n : ℝ)/2)
    (hπ : ∀ᶠ n in atTop, (P n).pi = 1)
    (hv : Tendsto (fun n => (P n).variance) atTop (𝓝 0)) :
    Tendsto (fun n => (∫ z, familyObservationShift (P n) z ∂familyRestArrayLaw (P n) n (m n))/
      ((P n).amplitude*boundedShiftScale n (m n))) atTop (𝓝 1) := by
  have hQ := tendsto_familyUnmasked_maximum_mean_ratio P m hmTop hcount hπ
  have hh := hQ.div (tendsto_lowerFamily_scale hv) (by norm_num : (1 : ℝ) ≠ 0)
  simp only [div_one] at hh
  apply hh.congr'
  filter_upwards [hcount,eventually_ge_atTop 1] with n hnc hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hL : 0 < Real.log (m n : ℝ) := Real.log_pos (by exact_mod_cast hm n)
  dsimp only [Pi.div_apply]
  rw [familyObservationShift_integral,hnc]
  unfold boundedShiftScale
  exact (observationShift_amplitude_ratio_identity (P n).scale_pos.ne' (P n).amplitude_pos.ne' hL.ne' hn0).symm

theorem gaussianShift_amplitude_ratio_identity (P : SymmetricFamilyParameters) {n m : ℕ} [NeZero m]
    (hn : 1 ≤ n) (hm : 2 ≤ m) (hπ : P.pi = 1)
    (hcount : (n : ℝ)*P.theta = Real.log (m : ℝ)/2) :
    (∫ z, familyGaussianShift P z ∂standardGaussian m)/(P.amplitude*boundedShiftScale n m) =
      (2/P.scale)*(RectangleCLT.Companion.SplitV4.gaussianMaximumMean m/Real.sqrt (2*Real.log (m : ℝ))) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hL : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast hm)
  have hθ := lowerFamily_theta_of_count P hn hcount
  have hv : P.variance = P.amplitude^2*(Real.log (m : ℝ)/(2*n)) := by
    unfold SymmetricFamilyParameters.variance
    rw [hπ,hθ]
    ring
  rw [familyGaussianShift_integral,hv,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq P.amplitude_pos.le]
  have hid : ((P.amplitude*Real.sqrt (Real.log (m : ℝ)/(2*n))/P.scale)*
      RectangleCLT.Companion.SplitV4.gaussianMaximumMean m)/(P.amplitude*boundedShiftScale n m) =
      ((Real.sqrt (Real.log (m : ℝ)/(2*n))/P.scale)*
        RectangleCLT.Companion.SplitV4.gaussianMaximumMean m)/boundedShiftScale n m := by
    rw [show (P.amplitude * Real.sqrt (Real.log (m : ℝ) / (2 * n)) / P.scale) *
        RectangleCLT.Companion.SplitV4.gaussianMaximumMean m =
        P.amplitude * ((Real.sqrt (Real.log (m : ℝ) / (2 * n)) / P.scale) *
          RectangleCLT.Companion.SplitV4.gaussianMaximumMean m) by ring]
    exact mul_div_mul_left _ _ P.amplitude_pos.ne'
  rw [hid]
  exact gaussianShift_ratio_identity P.scale_pos.ne' hL hn0

theorem tendsto_unmasked_gaussianShift_amplitude_ratio {P : ℕ → SymmetricFamilyParameters}
    {m : ℕ → ℕ} [∀ n, NeZero (m n)] (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hcount : ∀ᶠ n : ℕ in atTop, (n : ℝ)*(P n).theta = Real.log (m n : ℝ)/2)
    (hπ : ∀ᶠ n in atTop, (P n).pi = 1)
    (hv : Tendsto (fun n => (P n).variance) atTop (𝓝 0)) :
    Tendsto (fun n => (∫ z, familyGaussianShift (P n) z ∂standardGaussian (m n))/
      ((P n).amplitude*boundedShiftScale n (m n))) atTop (𝓝 2) := by
  have hs := tendsto_lowerFamily_scale hv
  have hG := Printed.tendsto_gaussianMaximumMean_div_sqrt_log_via_uniform_integrability.comp hmTop
  have hh := ((tendsto_const_nhds (x := (2 : ℝ))).div hs (by norm_num : (1 : ℝ) ≠ 0)).mul hG
  norm_num only [div_one,mul_one] at hh
  apply hh.congr'
  filter_upwards [hcount,hπ,eventually_ge_atTop 1] with n hnc hnπ hn
  exact (gaussianShift_amplitude_ratio_identity (P n) hn (hm n) hnπ hnc).symm

theorem tendsto_unmasked_shiftMeanDifference_amplitude_ratio {P : ℕ → SymmetricFamilyParameters}
    {m : ℕ → ℕ} [∀ n, NeZero (m n)] (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hcount : ∀ᶠ n : ℕ in atTop, (n : ℝ)*(P n).theta = Real.log (m n : ℝ)/2)
    (hπ : ∀ᶠ n in atTop, (P n).pi = 1)
    (hv : Tendsto (fun n => (P n).variance) atTop (𝓝 0)) :
    Tendsto (fun n => familyShiftMeanDifference (P n) n (m n)/
      ((P n).amplitude*boundedShiftScale n (m n))) atTop (𝓝 1) := by
  have hh := (tendsto_unmasked_gaussianShift_amplitude_ratio hm hmTop hcount hπ hv).sub
    (tendsto_unmasked_observationShift_amplitude_ratio hm hmTop hcount hπ hv)
  norm_num only [show (2 : ℝ)-1=1 by norm_num] at hh
  simpa only [familyShiftMeanDifference,sub_div] using hh

end
end RectangleCLTArxivV1
