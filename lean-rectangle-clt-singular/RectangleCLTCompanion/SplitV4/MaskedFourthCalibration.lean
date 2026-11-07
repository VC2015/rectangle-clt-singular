import RectangleCLTCompanion.SplitV4.MaskedFourthFamily
import RectangleCLTCompanion.SplitV4.RareFamilyComparison

/-! Actual-law instantiation of all masked fourth-moment primitive limits. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology
namespace RectangleCLT.Companion.SplitV4
noncomputable section

theorem eventually_maskedFourthFamily_parameters {B : ℕ → ℝ} {m : ℕ → ℕ}
    (hmTop : Tendsto m atTop atTop) (hBTop : Tendsto B atTop atTop)
    (hrate : Tendsto (fun n : ℕ => maskedFourthMomentLowerRate n (m n) (B n)) atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop,
      (maskedFourthFamilyParameters n (m n) (B n)).theta = maskedFourthTheta n (Real.log (m n : ℝ)) (B n) ∧
      (maskedFourthFamilyParameters n (m n) (B n)).pi = maskedFourthPi (B n) ∧
      (maskedFourthFamilyParameters n (m n) (B n)).amplitude = maskedFourthAmplitude n (Real.log (m n : ℝ)) (B n) := by
  let ell := fun n : ℕ => Real.log (m n : ℝ)
  have he : Tendsto ell atTop atTop := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmTop)
  filter_upwards [eventually_maskedFourth_probabilities ell B he hBTop hrate,
    eventually_ge_atTop 1, he.eventually (eventually_gt_atTop 0), hBTop.eventually (eventually_ge_atTop 2)]
    with n hn hn1 hnL hnB
  exact maskedFourthFamilyParameters_of_good _ _ _
    ⟨hn.1, hn.2.1.le, hn.2.2.1, hn.2.2.2.1.le, maskedFourthAmplitude_pos (by omega) hnL hnB, hn.2.2.2.2.2⟩

theorem maskedFourthFamily_identities {n m : ℕ} {B : ℝ} (hn : 1 ≤ n)
    (h : (maskedFourthFamilyParameters n m B).theta = maskedFourthTheta n (Real.log (m : ℝ)) B ∧
      (maskedFourthFamilyParameters n m B).pi = maskedFourthPi B ∧
      (maskedFourthFamilyParameters n m B).amplitude = maskedFourthAmplitude n (Real.log (m : ℝ)) B) :
    (maskedFourthFamilyParameters n m B).variance = maskedFourthVariance n (Real.log (m : ℝ)) B ∧
      (n : ℝ)*(maskedFourthFamilyParameters n m B).theta = maskedFourthCount (Real.log (m : ℝ)) B ∧
      familyRareShiftScale (maskedFourthFamilyParameters n m B) n =
        maskedFourthAmplitude n (Real.log (m : ℝ)) B*maskedFourthCount (Real.log (m : ℝ)) B/Real.sqrt n ∧
      familyRareLowerScale (maskedFourthFamilyParameters n m B) n m = maskedFourthScale n (Real.log (m : ℝ)) B := by
  have hcount : (n : ℝ)*(maskedFourthFamilyParameters n m B).theta = maskedFourthCount (Real.log (m : ℝ)) B := by
    rw [h.1, maskedFourthTheta_count (by omega : 0 < n)]
  refine ⟨?_, hcount, ?_, ?_⟩
  · unfold SymmetricFamilyParameters.variance
    rw [h.1, h.2.1, h.2.2]
    rfl
  · unfold familyRareShiftScale
    rw [h.2.2, hcount]
  · unfold familyRareLowerScale familyRareShiftScale maskedFourthScale
    rw [h.2.2, hcount]
    ring

theorem eventually_maskedFourthFamily_polynomialIndependent {B : ℕ → ℝ} {m : ℕ → ℕ}
    (hmTop : Tendsto m atTop atTop) (hBTop : Tendsto B atTop atTop)
    (hrate : Tendsto (fun n : ℕ => maskedFourthMomentLowerRate n (m n) (B n)) atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop,
      PolynomialIndependentHypotheses (familyArrayLaw (maskedFourthFamilyParameters n (m n) (B n)) n (m n))
        (familyRawObservations (maskedFourthFamilyParameters n (m n) (B n))) 4 (B n) := by
  filter_upwards [eventually_maskedFourthFamily_parameters hmTop hBTop hrate, eventually_ge_atTop 1,
    hmTop.eventually (eventually_ge_atTop 2), hBTop.eventually (eventually_ge_atTop 2)] with n hn hn1 hnM hnB
  have hn0 : 0 < n := by omega
  have hL : 0 < Real.log (m n : ℝ) := Real.log_pos (by exact_mod_cast hnM)
  let P := maskedFourthFamilyParameters n (m n) (B n)
  apply symmetricFamily_polynomialIndependent P hn1 (by norm_num : (1 : ℝ) ≤ 4)
  · have hs := familyScale_le_one P
    have ha : P.amplitude*P.theta^(1/4 : ℝ) = B n/2 := by
      change (maskedFourthFamilyParameters n (m n) (B n)).amplitude*
        (maskedFourthFamilyParameters n (m n) (B n)).theta^(1/4 : ℝ) = _
      rw [hn.1, hn.2.2]
      exact maskedFourth_envelope_identity hn0 hL hnB
    rw [ha]
    linarith
  · have hf := maskedFourth_fourth_identity hn0 hL hnB
    have hF : P.theta*P.pi*P.amplitude^4 = (B n)^2/16 := by
      change (maskedFourthFamilyParameters n (m n) (B n)).theta*
        (maskedFourthFamilyParameters n (m n) (B n)).pi*
        (maskedFourthFamilyParameters n (m n) (B n)).amplitude^4 = _
      rw [hn.1, hn.2.1, hn.2.2]
      exact hf
    rw [hF]
    have hv := P.variance_lt_half
    change P.variance < 1/2 at hv
    nlinarith only [hv, hnB, sq_nonneg P.variance, sq_nonneg (B n-2)]

structure MaskedFourthFamilyCalibration (B : ℕ → ℝ) (m : ℕ → ℕ) : Prop where
  count : Tendsto (fun n : ℕ => (n : ℝ)*(maskedFourthFamilyParameters n (m n) (B n)).theta) atTop atTop
  cover : Tendsto (fun n : ℕ => (m n : ℝ)*((maskedFourthFamilyParameters n (m n) (B n)).pi/2)^
    Nat.ceil (2*((n : ℝ)*(maskedFourthFamilyParameters n (m n) (B n)).theta))) atTop atTop
  variance : Tendsto (fun n => (maskedFourthFamilyParameters n (m n) (B n)).variance) atTop (𝓝 0)
  coefficient : Tendsto (fun n : ℕ => Real.sqrt (maskedFourthFamilyParameters n (m n) (B n)).variance*
    Real.sqrt (2*Real.log (m n : ℝ))/familyRareShiftScale (maskedFourthFamilyParameters n (m n) (B n)) n) atTop (𝓝 0)
  small : Tendsto (fun n : ℕ => Real.log (m n : ℝ)^3/n) atTop (𝓝 0)
  scale : Tendsto (fun n : ℕ => familyRareLowerScale (maskedFourthFamilyParameters n (m n) (B n)) n (m n)/
    boundedLowerScale n (m n)) atTop atTop
  countCost : Tendsto (fun n : ℕ => Real.log (m n : ℝ)*(maskedFourthFamilyParameters n (m n) (B n)).amplitude^2*
    (((n : ℝ)*(maskedFourthFamilyParameters n (m n) (B n)).theta)^2+(n : ℝ)*(maskedFourthFamilyParameters n (m n) (B n)).theta)/n/
      familyRareLowerScale (maskedFourthFamilyParameters n (m n) (B n)) n (m n)) atTop (𝓝 0)
  gaussianCost : Tendsto (fun n : ℕ => Real.log (m n : ℝ)*(maskedFourthFamilyParameters n (m n) (B n)).variance*
    (1+Real.log (m n : ℝ))/familyRareLowerScale (maskedFourthFamilyParameters n (m n) (B n)) n (m n)) atTop (𝓝 0)
  rateRatio : Tendsto (fun n : ℕ => maskedFourthMomentLowerRate n (m n) (B n)/
    familyRareLowerScale (maskedFourthFamilyParameters n (m n) (B n)) n (m n)) atTop (𝓝 (4*Real.sqrt 2))

theorem maskedFourthFamilyCalibration {B : ℕ → ℝ} {m : ℕ → ℕ}
    (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop) (hBTop : Tendsto B atTop atTop)
    (hΛ : Tendsto (fun n : ℕ => maskedFourthLog (B n)/Real.log (m n : ℝ)) atTop (𝓝 0))
    (hrate : Tendsto (fun n : ℕ => maskedFourthMomentLowerRate n (m n) (B n)) atTop (𝓝 0)) :
    MaskedFourthFamilyCalibration B m := by
  let ell := fun n : ℕ => Real.log (m n : ℝ)
  have he : Tendsto ell atTop atTop := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmTop)
  have hgood := eventually_maskedFourthFamily_parameters hmTop hBTop hrate
  have hIDs : ∀ᶠ n : ℕ in atTop,
      (maskedFourthFamilyParameters n (m n) (B n)).variance = maskedFourthVariance n (ell n) (B n) ∧
      (n : ℝ)*(maskedFourthFamilyParameters n (m n) (B n)).theta = maskedFourthCount (ell n) (B n) ∧
      familyRareShiftScale (maskedFourthFamilyParameters n (m n) (B n)) n =
        maskedFourthAmplitude n (ell n) (B n)*maskedFourthCount (ell n) (B n)/Real.sqrt n ∧
      familyRareLowerScale (maskedFourthFamilyParameters n (m n) (B n)) n (m n) = maskedFourthScale n (ell n) (B n) := by
    filter_upwards [hgood, eventually_ge_atTop 1] with n hn hn1
    exact maskedFourthFamily_identities hn1 hn
  refine ⟨?_, ?_, ?_, ?_, tendsto_maskedFourth_cube_div ell B he hBTop hrate, ?_, ?_, ?_, ?_⟩
  · apply (tendsto_maskedFourthCount ell B he hBTop hΛ).congr'
    filter_upwards [hIDs] with n hn
    exact hn.2.1.symm
  · apply (tendsto_maskedFourth_coverage ell B he hBTop hΛ).congr'
    filter_upwards [hIDs, hgood, eventually_ge_atTop 1] with n hn hnG hn1
    rw [hn.2.1, hnG.2.1]
    dsimp only [ell, maskedFourthCutoff]
    rw [Real.exp_log (show (0 : ℝ) < m n by exact_mod_cast (show 0 < m n by have := hm n; omega)),
      maskedFourthTheta_count (by omega : 0 < n)]

  · apply (tendsto_maskedFourthVariance ell B he hBTop hrate).congr'
    filter_upwards [hIDs] with n hn
    exact hn.1.symm
  · apply (tendsto_maskedFourth_gaussian_coefficient ell B he hBTop).congr'
    filter_upwards [hIDs] with n hn
    rw [hn.1, hn.2.2.1]
  · apply (tendsto_maskedFourth_scale_bounded_ratio ell B he hBTop hrate).congr'
    filter_upwards [hIDs] with n hn
    rw [hn.2.2.2]
    rfl
  · apply (tendsto_maskedFourth_count_cost ell B he hBTop hΛ hrate).congr'
    filter_upwards [hIDs, hgood] with n hn hnG
    rw [hn.2.1, hn.2.2.2, hnG.2.2]
  · apply (tendsto_maskedFourth_gaussian_cost ell B he hBTop hrate).congr'
    filter_upwards [hIDs] with n hn
    rw [hn.1, hn.2.2.2]
  · apply tendsto_const_nhds.congr'
    filter_upwards [hIDs, eventually_ge_atTop 1, hBTop.eventually (eventually_ge_atTop 2)] with n hn hn1 hnB
    rw [hn.2.2.2]
    unfold maskedFourthMomentLowerRate
    rw [maskedFourth_rate_conversion (by omega) (Real.log_pos (by exact_mod_cast hm n)) hnB,
      mul_div_cancel_right₀ _ (maskedFourthScale_pos (by omega) (Real.log_pos (by exact_mod_cast hm n)) hnB).ne']

end
end RectangleCLT.Companion.SplitV4
