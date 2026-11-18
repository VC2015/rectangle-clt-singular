import RectangleCLTArxivV1.LowerMaskedFourthLimits

/-! Actual-law primitive calibration for the growing fourth-moment model. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set Filter RectangleCLT RectangleCLT.Companion
open RectangleCLT.Companion.SplitV4
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false

def lowerMaskedFourthSequence (B : ℕ → ℝ) (m : ℕ → ℕ) (n : ℕ) : SymmetricFamilyParameters :=
  maskedFourthFamilyParameters n (m n) (B n)

theorem eventually_lowerMaskedFourthSequence_fields {B : ℕ → ℝ} {r m : ℕ → ℕ}
    (hB : ∀ n, 2 ≤ B n) (hBTop : Tendsto B atTop atTop) (hr : ∀ n, 1 ≤ r n)
    (hmTop : Tendsto m atTop atTop)
    (hΛ : Tendsto (fun n => maskedFourthLog (B n)/Real.log (m n : ℝ)) atTop (𝓝 0))
    (hsmall : Tendsto (fun n => lowerMaskedFourthRawWidth n (Real.log (m n : ℝ))
      (B n) (independentAbsGaussianMean (r n))) atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop,
      (lowerMaskedFourthSequence B m n).theta = maskedFourthTheta n (Real.log (m n : ℝ)) (B n) ∧
      (lowerMaskedFourthSequence B m n).pi = maskedFourthPi (B n) ∧
      (lowerMaskedFourthSequence B m n).amplitude = maskedFourthAmplitude n (Real.log (m n : ℝ)) (B n) := by
  have hθ := (tendsto_lowerMaskedFourthTheta hB hBTop hr hmTop hΛ hsmall).eventually
    (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))
  have hv := (tendsto_lowerMaskedFourthVariance hB hBTop hr hmTop hΛ hsmall).eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1/2))
  filter_upwards [hθ,hv,eventually_ge_atTop 1,hmTop.eventually (eventually_ge_atTop 2)] with n hnθ hnv hn hnm
  have hn0 : 0 < n := by omega
  have hL : 0 < Real.log (m n : ℝ) := Real.log_pos (by exact_mod_cast hnm)
  have hPi0 : 0 < maskedFourthPi (B n) := by
    unfold maskedFourthPi
    have hBn : 0 < B n := by linarith [hB n]
    positivity
  have hPi1 : maskedFourthPi (B n) ≤ 1 := by
    unfold maskedFourthPi
    apply (div_le_one (by have := hB n; positivity : (0 : ℝ) < (B n)^2)).mpr
    nlinarith [hB n]
  exact maskedFourthFamilyParameters_of_good n (m n) (B n)
    ⟨maskedFourthTheta_pos hn0 hL (hB n),hnθ,hPi0,hPi1,
      maskedFourthAmplitude_pos hn0 hL (hB n),hnv⟩

/-- All fields are proved numerical consequences for the explicitly
constructed parameter sequence; this is a constructor theorem's output. -/
structure LowerMaskedFourthCalibration (B : ℕ → ℝ) (r m : ℕ → ℕ) : Prop where
  fields : ∀ᶠ n : ℕ in atTop,
    (lowerMaskedFourthSequence B m n).theta = maskedFourthTheta n (Real.log (m n : ℝ)) (B n) ∧
    (lowerMaskedFourthSequence B m n).pi = maskedFourthPi (B n) ∧
    (lowerMaskedFourthSequence B m n).amplitude = maskedFourthAmplitude n (Real.log (m n : ℝ)) (B n)
  variance : Tendsto (fun n => (lowerMaskedFourthSequence B m n).variance) atTop (𝓝 0)
  count : Tendsto (fun n : ℕ => (n : ℝ)*(lowerMaskedFourthSequence B m n).theta) atTop atTop
  cover : Tendsto (fun n : ℕ => (m n : ℝ)*((lowerMaskedFourthSequence B m n).pi/2)^
    Nat.ceil (2*((n : ℝ)*(lowerMaskedFourthSequence B m n).theta))) atTop atTop
  coefficient : Tendsto (fun n : ℕ => Real.sqrt (lowerMaskedFourthSequence B m n).variance*
    Real.sqrt (2*Real.log (m n : ℝ))/familyRareShiftScale (lowerMaskedFourthSequence B m n) n) atTop (𝓝 0)
  effective : ∀ᶠ n in atTop, 1 ≤ lowerFamilyEffectiveAmplitude (lowerMaskedFourthSequence B m n) n (m n)
  mask_budget : ∀ᶠ n : ℕ in atTop, (lowerMaskedFourthSequence B m n).pi*Real.log (m n : ℝ) ≤
    (n : ℝ)*(lowerMaskedFourthSequence B m n).theta
  small : Tendsto (fun n => lowerFamilyRareWidthScale (lowerMaskedFourthSequence B m n) n (r n)) atTop (𝓝 0)

theorem lowerMaskedFourthCalibration {B : ℕ → ℝ} {r m : ℕ → ℕ}
    (hB : ∀ n, 2 ≤ B n) (hBTop : Tendsto B atTop atTop) (hr : ∀ n, 1 ≤ r n)
    (hmTop : Tendsto m atTop atTop)
    (hΛ : Tendsto (fun n => maskedFourthLog (B n)/Real.log (m n : ℝ)) atTop (𝓝 0))
    (hsmall : Tendsto (fun n => lowerMaskedFourthRawWidth n (Real.log (m n : ℝ))
      (B n) (independentAbsGaussianMean (r n))) atTop (𝓝 0)) : LowerMaskedFourthCalibration B r m := by
  have hlog : Tendsto (fun n => Real.log (m n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmTop)
  have hfields := eventually_lowerMaskedFourthSequence_fields hB hBTop hr hmTop hΛ hsmall
  have hIDs : ∀ᶠ n : ℕ in atTop,
      (lowerMaskedFourthSequence B m n).variance = maskedFourthVariance n (Real.log (m n : ℝ)) (B n) ∧
      (n : ℝ)*(lowerMaskedFourthSequence B m n).theta = maskedFourthCount (Real.log (m n : ℝ)) (B n) ∧
      familyRareShiftScale (lowerMaskedFourthSequence B m n) n =
        maskedFourthAmplitude n (Real.log (m n : ℝ)) (B n)*maskedFourthCount (Real.log (m n : ℝ)) (B n)/Real.sqrt n ∧
      familyRareLowerScale (lowerMaskedFourthSequence B m n) n (m n) = maskedFourthScale n (Real.log (m n : ℝ)) (B n) := by
    filter_upwards [hfields,eventually_ge_atTop 1] with n hn hn1
    exact maskedFourthFamily_identities hn1 hn
  refine ⟨hfields,?_,?_,?_,?_,?_,?_,?_⟩
  · apply (tendsto_lowerMaskedFourthVariance hB hBTop hr hmTop hΛ hsmall).congr'
    filter_upwards [hIDs] with n hn
    exact hn.1.symm
  · apply (tendsto_maskedFourthCount (fun n => Real.log (m n : ℝ)) B hlog hBTop hΛ).congr'
    filter_upwards [hIDs] with n hn
    exact hn.2.1.symm
  · apply (tendsto_maskedFourth_coverage (fun n => Real.log (m n : ℝ)) B hlog hBTop hΛ).congr'
    filter_upwards [hfields,hmTop.eventually (eventually_ge_atTop 2)] with n hn hnm
    rw [hn.1,hn.2.1]
    rw [Real.exp_log (by exact_mod_cast (by omega : 0 < m n) : (0 : ℝ) < m n)]
    rfl
  · apply (tendsto_maskedFourth_gaussian_coefficient (fun n => Real.log (m n : ℝ)) B hlog hBTop).congr'
    filter_upwards [hIDs] with n hn
    rw [hn.1,hn.2.2.1]
  · have hEff := (tendsto_lowerMaskedFourthEffectiveAmplitude hB hmTop
      (tendsto_lowerMaskedFourthTheta hB hBTop hr hmTop hΛ hsmall)).eventually (eventually_ge_atTop 1)
    filter_upwards [hEff,hfields,hIDs] with n hnEff hnFields hnIDs
    unfold lowerFamilyEffectiveAmplitude
    rwa [hnFields.2.2,hnIDs.2.1]
  · have hPi := (tendsto_maskedFourthPi_log B hBTop).eventually
      (eventually_le_nhds (by norm_num : (0 : ℝ) < 1/4))
    filter_upwards [hPi,hfields,hIDs,hlog.eventually (eventually_gt_atTop 0)] with n hnPi hnFields hnIDs hnL
    rw [hnFields.2.1,hnIDs.2.1]
    unfold maskedFourthCount
    have hΛpos : 0 < maskedFourthLog (B n) := lt_of_lt_of_le (by norm_num) (maskedFourthLog_bounds (hB n)).1
    apply (le_div_iff₀ (mul_pos (by norm_num) hΛpos)).mpr
    have hh := mul_le_mul_of_nonneg_right hnPi hnL.le
    nlinarith only [hh]
  · apply hsmall.congr'
    filter_upwards [hIDs] with n hn
    unfold lowerFamilyRareWidthScale lowerMaskedFourthRawWidth
    rw [hn.2.2.1]
    ring

end
end RectangleCLTArxivV1
