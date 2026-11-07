import RectangleCLTCompanion.SplitV4.DenseMomentFamily
import RectangleCLTCompanion.SplitV4.FourthMomentCalibration

/-! Actual fixed-envelope q>4 parameter, moment and lower-scale calibration. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology
namespace RectangleCLT.Companion.SplitV4
noncomputable section

def denseLowerRateConversion (q B : ℝ) : ℝ := (B/(B-1))*2^(5/2-2/q)
def denseLowerConstant (q B : ℝ) : ℝ := Real.sqrt 2*Real.exp (-1)/denseLowerRateConversion q B

theorem denseLowerRateConversion_pos {q B : ℝ} (hB : 2 ≤ B) : 0 < denseLowerRateConversion q B := by
  unfold denseLowerRateConversion
  exact mul_pos (div_pos (by linarith) (by linarith)) (Real.rpow_pos_of_pos (by norm_num) _)

theorem denseLowerConstant_pos {q B : ℝ} (hB : 2 ≤ B) : 0 < denseLowerConstant q B := by
  unfold denseLowerConstant
  exact div_pos (by positivity) (denseLowerRateConversion_pos hB)

theorem eventually_denseFamily_parameters {m : ℕ → ℕ} {q B : ℝ}
    (hq : 4 < q) (hB : 2 ≤ B) (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hrate : Tendsto (fun n : ℕ => denseMomentLowerRate n (m n) q B) atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop,
      (denseFamilyParameters q B n (m n)).theta = fourthLowerTheta n (Real.log (m n : ℝ)) ∧
      (denseFamilyParameters q B n (m n)).amplitude = denseLowerAmplitude n (Real.log (m n : ℝ)) q B := by
  let ell := fun n : ℕ => Real.log (m n : ℝ)
  have hEll : Tendsto ell atTop atTop := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmTop)
  have hr : Tendsto (fun n : ℕ => denseLowerEnvelopeRate n (ell n) q B) atTop (𝓝 0) :=
    hrate.congr' (Eventually.of_forall (fun n => denseMomentLowerRate_eq n (m n) (hm n) q B))
  have ht := tendsto_denseLowerTheta ell hEll hq (by linarith : 1 < B) hr
  have hv := tendsto_denseLowerAmplitude_square_theta ell hEll hq (by linarith : 1 < B) hr
  filter_upwards [eventually_ge_atTop 1,
    ht.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1)),
    hv.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1/2))] with n hn hnθ hnv
  have hn0 : 0 < n := by omega
  have hL : 0 < ell n := Real.log_pos (by exact_mod_cast hm n)
  exact denseFamilyParameters_of_good q B n (m n)
    ⟨fourthLowerTheta_pos hn0 hL, hnθ, denseLowerAmplitude_pos hn0 hL (by linarith), hnv⟩

theorem tendsto_denseFamily_variance {m : ℕ → ℕ} {q B : ℝ}
    (hq : 4 < q) (hB : 2 ≤ B) (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hrate : Tendsto (fun n : ℕ => denseMomentLowerRate n (m n) q B) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (denseFamilyParameters q B n (m n)).variance) atTop (𝓝 0) := by
  have hEll : Tendsto (fun n : ℕ => Real.log (m n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmTop)
  have hr : Tendsto (fun n : ℕ => denseLowerEnvelopeRate n (Real.log (m n : ℝ)) q B) atTop (𝓝 0) :=
    hrate.congr' (Eventually.of_forall (fun n => denseMomentLowerRate_eq n (m n) (hm n) q B))
  apply (tendsto_denseLowerAmplitude_square_theta _ hEll hq (by linarith : 1 < B) hr).congr'
  filter_upwards [eventually_denseFamily_parameters hq hB hm hmTop hrate] with n hn
  unfold SymmetricFamilyParameters.variance
  rw [denseFamilyParameters_pi, mul_one, hn.1, hn.2]

theorem tendsto_denseFamily_scale {m : ℕ → ℕ} {q B : ℝ}
    (hq : 4 < q) (hB : 2 ≤ B) (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hrate : Tendsto (fun n : ℕ => denseMomentLowerRate n (m n) q B) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (denseFamilyParameters q B n (m n)).scale) atTop (𝓝 1) := by
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp
    ((tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_denseFamily_variance hq hB hm hmTop hrate))
  simpa only [sub_zero, Real.sqrt_one, SymmetricFamilyParameters.scale, Function.comp_apply] using hh

theorem eventually_denseFamily_polynomialIndependent {m : ℕ → ℕ} {q B : ℝ}
    (hq : 4 < q) (hB : 2 ≤ B) (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hrate : Tendsto (fun n : ℕ => denseMomentLowerRate n (m n) q B) atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop,
      PolynomialIndependentHypotheses (familyArrayLaw (denseFamilyParameters q B n (m n)) n (m n))
        (familyRawObservations (denseFamilyParameters q B n (m n))) q B := by
  have hEll : Tendsto (fun n : ℕ => Real.log (m n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmTop)
  have hr : Tendsto (fun n : ℕ => denseLowerEnvelopeRate n (Real.log (m n : ℝ)) q B) atTop (𝓝 0) :=
    hrate.congr' (Eventually.of_forall (fun n => denseMomentLowerRate_eq n (m n) (hm n) q B))
  have hfactor : Tendsto (fun n : ℕ =>
      (denseFamilyParameters q B n (m n)).theta*(denseFamilyParameters q B n (m n)).pi*
        (denseFamilyParameters q B n (m n)).amplitude^4) atTop (𝓝 0) := by
    apply (tendsto_denseLowerAmplitude_fourth_theta _ hEll hq (by linarith : 1 < B) hr).congr'
    filter_upwards [eventually_denseFamily_parameters hq hB hm hmTop hrate] with n hn
    rw [denseFamilyParameters_pi, mul_one, hn.1, hn.2]
  have hv := tendsto_denseFamily_variance hq hB hm hmTop hrate
  have hfourth := (((tendsto_const_nhds (x := (1 : ℝ))).add (hv.const_mul 4)).sub
    ((hv.pow 2).const_mul 5)).add hfactor
  norm_num only [mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero, sub_zero] at hfourth
  filter_upwards [eventually_denseFamily_parameters hq hB hm hmTop hrate, eventually_ge_atTop 1,
    hfourth.eventually (eventually_le_nhds (by norm_num : (1 : ℝ) < 2))] with n hn hnn hnFourth
  apply symmetricFamily_polynomialIndependent _ hnn (by linarith : 1 ≤ q)
  · have ht : 0 < fourthLowerTheta n (Real.log (m n : ℝ)) := fourthLowerTheta_pos (by omega)
      (Real.log_pos (by exact_mod_cast hm n))
    have ha := dense_amplitude_inverse_identity ht q B
    have hs := familyScale_le_one (denseFamilyParameters q B n (m n))
    rw [hn.1, hn.2]
    unfold denseLowerAmplitude
    rw [ha]
    linarith
  · exact hnFourth.trans (by nlinarith only [hB, sq_nonneg (B-2)])

structure DenseFamilyCalibration (q B : ℝ) (m : ℕ → ℕ) : Prop where
  small : Tendsto (fun n : ℕ => Real.log (m n : ℝ)^3/n) atTop (𝓝 0)
  thetaMatch : ∀ᶠ n : ℕ in atTop,
    (denseFamilyParameters q B n (m n)).theta = (boundedFamilyParameters n (m n)).theta
  amplificationLarge : ∀ᶠ n : ℕ in atTop,
    1 ≤ familyShiftAmplification (denseFamilyParameters q B n (m n)) (boundedFamilyParameters n (m n))
  amplificationSmall : Tendsto (fun n : ℕ =>
    familyShiftAmplification (denseFamilyParameters q B n (m n)) (boundedFamilyParameters n (m n))*
      Real.sqrt (Real.log (m n : ℝ)^3/n)) atTop (𝓝 0)
  rateRatio : Tendsto (fun n : ℕ => denseMomentLowerRate n (m n) q B /
    amplifiedSymmetricLowerScale (denseFamilyParameters q B n (m n)) n (m n)) atTop (𝓝 (denseLowerRateConversion q B))

theorem denseFamilyCalibration {m : ℕ → ℕ} {q B : ℝ}
    (hq : 4 < q) (hB : 2 ≤ B) (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hrate : Tendsto (fun n : ℕ => denseMomentLowerRate n (m n) q B) atTop (𝓝 0)) :
    DenseFamilyCalibration q B m := by
  let ell := fun n : ℕ => Real.log (m n : ℝ)
  let a := fun n => denseLowerAmplitude n (ell n) q B
  let k := fun n => familyShiftAmplification (denseFamilyParameters q B n (m n)) (boundedFamilyParameters n (m n))
  have hEll : Tendsto ell atTop atTop := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmTop)
  have hr : Tendsto (fun n : ℕ => denseLowerEnvelopeRate n (ell n) q B) atTop (𝓝 0) :=
    hrate.congr' (Eventually.of_forall (fun n => denseMomentLowerRate_eq n (m n) (hm n) q B))
  have hsmall := tendsto_denseLower_cube_div ell hEll hq (by linarith : 1 < B) hr
  have hgood := eventually_denseFamily_parameters hq hB hm hmTop hrate
  have ha : ∀ᶠ n : ℕ in atTop, 0 < a n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact denseLowerAmplitude_pos (by omega) (Real.log_pos (by exact_mod_cast hm n)) (by linarith)
  have hratio : Tendsto (fun n => k n/a n) atTop (𝓝 1) := by
    have hh := (tendsto_boundedFamily_scale hm hmTop hsmall).div
      (tendsto_denseFamily_scale hq hB hm hmTop hrate) (by norm_num : (1 : ℝ) ≠ 0)
    simp only [div_one] at hh
    apply hh.congr'
    filter_upwards [hgood, ha] with n hn hna
    dsimp only [k, a]
    unfold familyShiftAmplification
    rw [boundedFamilyParameters_amplitude, hn.2, one_mul]
    dsimp only [ell] at hna ⊢
    field_simp [hna.ne', (denseFamilyParameters q B n (m n)).scale_pos.ne']
    ring
  have hk : ∀ᶠ n : ℕ in atTop, 1 ≤ k n := by
    filter_upwards [hratio.eventually (eventually_ge_nhds (by norm_num : (1/2 : ℝ) < 1)),
      (tendsto_denseLowerAmplitude ell hEll hq (by linarith : 1 < B) hr).eventually (eventually_ge_atTop 2), ha]
      with n hnratio hnamp hna
    have hh : (1/2 : ℝ)*a n ≤ k n := (le_div_iff₀ hna).mp hnratio
    linarith
  have hksmall : Tendsto (fun n => k n*Real.sqrt (ell n^3/n)) atTop (𝓝 0) := by
    have hh := hratio.mul (tendsto_denseLowerAmplitude_sqrt_cube ell hEll hq (by linarith : 1 < B) hr)
    simp only [mul_zero] at hh
    apply hh.congr'
    filter_upwards [ha] with n hn
    change (k n/a n)*(a n*Real.sqrt (ell n^3/n)) = _
    rw [← mul_assoc, div_mul_cancel₀ _ hn.ne']
  refine ⟨hsmall, ?_, hk, hksmall, ?_⟩
  · filter_upwards [hgood, boundedFamilyParameters_eventually_theta hm hmTop hsmall] with n hn hnb
    rw [hn.1, hnb]
    rfl
  · have hh := (tendsto_denseLowerEnvelopeRate_div_scale ell hEll q (by linarith : 1 < B)).div hratio (by norm_num : (1 : ℝ) ≠ 0)
    simp only [div_one] at hh
    apply hh.congr'
    filter_upwards [ha, eventually_boundedLowerScale_pos hmTop] with n hna hd
    dsimp only [Pi.div_apply]
    rw [denseMomentLowerRate_eq _ _ (hm n) q B]
    have hda : denseLowerScale n (ell n) q B = a n*boundedLowerScale n (m n) := by
      dsimp only [denseLowerScale, boundedLowerScale, a, ell]
      ring
    rw [hda]
    unfold amplifiedSymmetricLowerScale
    change (denseLowerEnvelopeRate n (ell n) q B/(a n*boundedLowerScale n (m n)))/(k n/a n) =
      denseLowerEnvelopeRate n (ell n) q B/(k n*boundedLowerScale n (m n))
    exact amplified_rate_quotient hna.ne' hd.ne'
      (familyShiftAmplification_pos (denseFamilyParameters q B n (m n)) (boundedFamilyParameters n (m n))).ne'

end
end RectangleCLT.Companion.SplitV4
