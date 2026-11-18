import RectangleCLTArxivV1.LowerSparseWidthScales

/-! Actual-law calibration for the sparse polynomial construction. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set Filter RectangleCLT RectangleCLT.Companion
open RectangleCLT.Companion.SplitV4
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false

def lowerSparseSequence (q : ℝ) (B : ℕ → ℝ) (m : ℕ → ℕ) (n : ℕ) : SymmetricFamilyParameters :=
  sparseFamilyParameters q n (m n) (B n)

theorem eventually_lowerSparseSequence_fields (q : ℝ) {B : ℕ → ℝ} {m : ℕ → ℕ}
    (hB : ∀ n, 2 ≤ B n) (hmTop : Tendsto m atTop atTop)
    (hK : Tendsto (fun n => sparseLowerKhat n (Real.log (m n : ℝ)) q (B n)) atTop atTop)
    (hθ : Tendsto (fun n => sparseLowerTheta n (Real.log (m n : ℝ)) q (B n)) atTop (𝓝 0))
    (hv : Tendsto (fun n => sparseLowerVariance n (Real.log (m n : ℝ)) q (B n)) atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop,
      (lowerSparseSequence q B m n).theta = sparseLowerTheta n (Real.log (m n : ℝ)) q (B n) ∧
      (lowerSparseSequence q B m n).pi = sparseLowerPi n (Real.log (m n : ℝ)) q (B n) ∧
      (lowerSparseSequence q B m n).amplitude = sparseLowerAmplitude n (Real.log (m n : ℝ)) q (B n) := by
  have hlog : Tendsto (fun n => Real.log (m n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmTop)
  have hPi := tendsto_sparseLowerPi (fun n => Real.log (m n : ℝ)) B q hlog hB hK
  filter_upwards [hθ.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1)),
    hv.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1/2)),
    hPi.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1)),
    hlog.eventually (eventually_gt_atTop 0),hK.eventually (eventually_ge_atTop 2),eventually_ge_atTop 1]
    with n hnθ hnv hnPi hnL hnK hn
  have hn0 : 0 < n := by omega
  have hBn : 0 < B n := by linarith [hB n]
  have hPi0 : 0 < sparseLowerPi n (Real.log (m n : ℝ)) q (B n) := by
    rw [sparseLowerPi_eq_mask hn0 hnL hBn hnK]
    exact sparseMaskPi_pos hnK _
  exact sparseFamilyParameters_of_good q n (m n) (B n)
    ⟨sparseLowerTheta_pos hn0 hnL hnK,hnθ,hPi0,hnPi,sparseLowerAmplitude_pos hn0 hnL hBn hnK,hnv⟩

/-- This output records proved primitive numerical properties of the
explicit actual parameter sequence, with no comparison conclusion as an input. -/
structure LowerSparseCalibration (q : ℝ) (B : ℕ → ℝ) (r m : ℕ → ℕ) : Prop where
  fields : ∀ᶠ n : ℕ in atTop,
    (lowerSparseSequence q B m n).theta = sparseLowerTheta n (Real.log (m n : ℝ)) q (B n) ∧
    (lowerSparseSequence q B m n).pi = sparseLowerPi n (Real.log (m n : ℝ)) q (B n) ∧
    (lowerSparseSequence q B m n).amplitude = sparseLowerAmplitude n (Real.log (m n : ℝ)) q (B n)
  variance : Tendsto (fun n => (lowerSparseSequence q B m n).variance) atTop (𝓝 0)
  count : Tendsto (fun n : ℕ => (n : ℝ)*(lowerSparseSequence q B m n).theta) atTop atTop
  cover : Tendsto (fun n : ℕ => (m n : ℝ)*((lowerSparseSequence q B m n).pi/2)^
    Nat.ceil (2*((n : ℝ)*(lowerSparseSequence q B m n).theta))) atTop atTop
  coefficient : Tendsto (fun n : ℕ => Real.sqrt (lowerSparseSequence q B m n).variance*
    Real.sqrt (2*Real.log (m n : ℝ))/familyRareShiftScale (lowerSparseSequence q B m n) n) atTop (𝓝 0)
  effective : ∀ᶠ n in atTop, 1 ≤ lowerFamilyEffectiveAmplitude (lowerSparseSequence q B m n) n (m n)
  mask_budget : ∀ᶠ n : ℕ in atTop, (lowerSparseSequence q B m n).pi*Real.log (m n : ℝ) ≤
    (n : ℝ)*(lowerSparseSequence q B m n).theta
  small : Tendsto (fun n => lowerFamilyRareWidthScale (lowerSparseSequence q B m n) n (r n)) atTop (𝓝 0)

theorem lowerSparseCalibration_of_scalar_limits (q : ℝ) {B : ℕ → ℝ} {r m : ℕ → ℕ}
    (hB : ∀ n, 2 ≤ B n) (hmTop : Tendsto m atTop atTop)
    (hK : Tendsto (fun n => sparseLowerKhat n (Real.log (m n : ℝ)) q (B n)) atTop atTop)
    (hΛ : Tendsto (fun n => sparseLowerLog n (Real.log (m n : ℝ)) q (B n)/Real.log (m n : ℝ)) atTop (𝓝 0))
    (hθ : Tendsto (fun n => sparseLowerTheta n (Real.log (m n : ℝ)) q (B n)) atTop (𝓝 0))
    (hv : Tendsto (fun n => sparseLowerVariance n (Real.log (m n : ℝ)) q (B n)) atTop (𝓝 0))
    (hEff : Tendsto (fun n => sparseLowerAmplitude n (Real.log (m n : ℝ)) q (B n)*
      sparseLowerCount n (Real.log (m n : ℝ)) q (B n)/Real.log (m n : ℝ)) atTop atTop)
    (hsmall : Tendsto (fun n => lowerSparseRawWidth n (Real.log (m n : ℝ)) q (B n)
      (independentAbsGaussianMean (r n))) atTop (𝓝 0)) : LowerSparseCalibration q B r m := by
  have hlog : Tendsto (fun n => Real.log (m n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmTop)
  have hfields := eventually_lowerSparseSequence_fields q hB hmTop hK hθ hv
  have hIDs : ∀ᶠ n : ℕ in atTop,
      (lowerSparseSequence q B m n).variance = sparseLowerVariance n (Real.log (m n : ℝ)) q (B n) ∧
      (n : ℝ)*(lowerSparseSequence q B m n).theta = sparseLowerCount n (Real.log (m n : ℝ)) q (B n) ∧
      familyRareShiftScale (lowerSparseSequence q B m n) n =
        sparseLowerAmplitude n (Real.log (m n : ℝ)) q (B n)*sparseLowerCount n (Real.log (m n : ℝ)) q (B n)/Real.sqrt n ∧
      familyRareLowerScale (lowerSparseSequence q B m n) n (m n) = sparseLowerScale n (Real.log (m n : ℝ)) q (B n) := by
    filter_upwards [hfields,eventually_ge_atTop 1] with n hn hn1
    exact sparseFamily_identities hn1 hn
  refine ⟨hfields,?_,?_,?_,?_,?_,?_,?_⟩
  · apply hv.congr'
    filter_upwards [hIDs] with n hn
    exact hn.1.symm
  · apply (tendsto_sparseLowerCount (fun n => Real.log (m n : ℝ)) B q hlog hK hΛ).congr'
    filter_upwards [hIDs] with n hn
    exact hn.2.1.symm
  · apply (tendsto_sparseLower_coverage (fun n => Real.log (m n : ℝ)) B q hlog hB hK hΛ).congr'
    filter_upwards [hfields,eventually_ge_atTop 1,hmTop.eventually (eventually_ge_atTop 2)] with n hn hn1 hnm
    rw [hn.1,hn.2.1]
    unfold sparseLowerCutoff
    rw [Real.exp_log (by exact_mod_cast (by omega : 0 < m n) : (0 : ℝ) < m n)]
  · apply (tendsto_sparseLower_gaussian_coefficient (fun n => Real.log (m n : ℝ)) B q hlog hB hK).congr'
    filter_upwards [hIDs] with n hn
    rw [hn.1,hn.2.2.1]
  · filter_upwards [hEff.eventually (eventually_ge_atTop 1),hfields,hIDs] with n hnEff hnFields hnIDs
    unfold lowerFamilyEffectiveAmplitude
    rwa [hnFields.2.2,hnIDs.2.1]
  · have hPi := (tendsto_sparseLowerPi_log (fun n => Real.log (m n : ℝ)) B q hlog hB hK).eventually
      (eventually_le_nhds (by norm_num : (0 : ℝ) < 1/4))
    filter_upwards [hPi,hfields,hIDs,hlog.eventually (eventually_gt_atTop 0),hK.eventually (eventually_ge_atTop 2)]
      with n hnPi hnFields hnIDs hnL hnK
    rw [hnFields.2.1,hnIDs.2.1]
    unfold sparseLowerCount
    have hΛpos : 0 < sparseLowerLog n (Real.log (m n : ℝ)) q (B n) :=
      lt_of_lt_of_le (by norm_num) (maskedFourthLog_bounds hnK).1
    apply (le_div_iff₀ (mul_pos (by norm_num) hΛpos)).mpr
    have hh := mul_le_mul_of_nonneg_right hnPi hnL.le
    nlinarith only [hh]
  · apply hsmall.congr'
    filter_upwards [hIDs] with n hn
    unfold lowerFamilyRareWidthScale lowerSparseRawWidth
    rw [hn.2.2.1]
    ring

end
end RectangleCLTArxivV1
