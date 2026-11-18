import RectangleCLTArxivV1.LowerMaskedFourthCalibration
import RectangleCLTArxivV1.LowerDenseParameters

/-! Theorem 6 for the actual growing fourth-envelope observations. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set Filter RectangleCLT RectangleCLT.Companion
open RectangleCLT.Companion.SplitV4
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false

theorem eventually_lowerMaskedFourth_membership {B : ℕ → ℝ} {r m : ℕ → ℕ}
    (hB : ∀ n, 2 ≤ B n) (hm : ∀ n, 2 ≤ m n)
    (hcal : LowerMaskedFourthCalibration B r m) :
    ∀ᶠ n in atTop, PolynomialFourthHypotheses
      (lowerFamilyArrayLaw (lowerMaskedFourthSequence B m n) n (r n) (m n))
      (lowerFamilyRawObservations (lowerMaskedFourthSequence B m n)) 4 (B n) := by
  filter_upwards [hcal.fields,eventually_ge_atTop 1] with n hnFields hn
  let P := lowerMaskedFourthSequence B m n
  have hn0 : 0 < n := by omega
  have hL : 0 < Real.log (m n : ℝ) := Real.log_pos (by exact_mod_cast hm n)
  have henv : PolynomialEnvelopeHypotheses (lowerFamilyArrayLaw P n (r n) (m n))
      (lowerFamilyRawObservations P) 4 (B n) := by
    apply lowerFamily_polynomialEnvelope_of_factor P hn (by norm_num : (1 : ℝ) ≤ 4)
    have ha : P.amplitude*P.theta^(1/4 : ℝ) = B n/2 := by
      change (lowerMaskedFourthSequence B m n).amplitude*(lowerMaskedFourthSequence B m n).theta^(1/4 : ℝ) = _
      rw [hnFields.2.2,hnFields.1]
      exact maskedFourth_envelope_identity hn0 hL (hB n)
    rw [ha]
    have hs := familyScale_le_one P
    linarith [hB n]
  apply lowerFamily_polynomialFourth_of_moments P hn henv
  have hf : P.theta*P.pi*P.amplitude^4 = (B n)^2/16 := by
    change (lowerMaskedFourthSequence B m n).theta*(lowerMaskedFourthSequence B m n).pi*
      (lowerMaskedFourthSequence B m n).amplitude^4 = _
    rw [hnFields.1,hnFields.2.1,hnFields.2.2]
    exact maskedFourth_fourth_identity hn0 hL (hB n)
  rw [hf]
  have hbase : 1+4*P.variance-5*P.variance^2 ≤ 9/5 := by nlinarith [sq_nonneg (P.variance-2/5)]
  have hB2 : (4 : ℝ) ≤ (B n)^2 := by nlinarith [hB n]
  linarith

/-- One absolute positive constant precedes the growing envelope and both
coordinate counts. Every probability, moment and width is that of the
explicitly constructed actual laws. -/
theorem theorem_6_growing_fourth_moment_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ (B : ℕ → ℝ) (r m : ℕ → ℕ)
      [∀ n, NeZero (r n)] [∀ n, NeZero (m n)],
      (∀ n, 2 ≤ B n) → (∀ n, 1 ≤ r n) → (∀ n, 2 ≤ m n) → (∀ n, r n ≤ m n) →
      Tendsto m atTop atTop → Tendsto B atTop atTop →
      Tendsto (fun n => Real.log (B n)/dimensionLog (r n*m n)) atTop (𝓝 0) →
      Tendsto (fun n => lowerMaskedFourthIntrinsicRate n (dimensionLog (r n*m n))
        (B n) (independentAbsGaussianMean (r n))) atTop (𝓝 0) →
      Tendsto (fun n => gaussianMaximumMean (lowerFamilyGaussianFactor (lowerMaskedFourthSequence B m n)
        (r n) (m n))/independentAbsGaussianMean (r n)) atTop (𝓝 1) ∧
      ∀ᶠ n in atTop,
        LowerRectangularFamilyProperties (lowerMaskedFourthSequence B m n) n (r n) (m n) ∧
        PolynomialFourthHypotheses (lowerFamilyArrayLaw (lowerMaskedFourthSequence B m n) n (r n) (m n))
          (lowerFamilyRawObservations (lowerMaskedFourthSequence B m n)) 4 (B n) ∧
        c*lowerMaskedFourthIntrinsicRate n (dimensionLog (r n*m n)) (B n)
          (gaussianMaximumMean (lowerFamilyGaussianFactor (lowerMaskedFourthSequence B m n) (r n) (m n))) ≤
          -lowerFamilyShiftedCDFDifference (lowerMaskedFourthSequence B m n) n (r n) (m n) (lowerLeadingThreshold (r n)) ∧
        c*lowerMaskedFourthIntrinsicRate n (dimensionLog (r n*m n)) (B n)
          (gaussianMaximumMean (lowerFamilyGaussianFactor (lowerMaskedFourthSequence B m n) (r n) (m n))) ≤
          lowerFamilyComparisonDistance (lowerMaskedFourthSequence B m n) n (r n) (m n) := by
  obtain ⟨c,hc,hDetect⟩ := exists_lowerFamily_masked_width_detection_constant
  refine ⟨c/128,by positivity,?_⟩
  intro B r m _ _ hB hr hm hrm hmTop hBTop hlogSmall hsmall
  have hraw := tendsto_lowerMaskedFourthRawWidth hB hr hm hsmall
  have hΛ := tendsto_lowerMaskedFourthLog_div_rareLog hB hr hrm hmTop hlogSmall
  have hcal := lowerMaskedFourthCalibration hB hBTop hr hmTop hΛ hraw
  have hprofile := lowerFamilyMasked_width_profile hr hm hmTop hcal.variance hcal.small hcal.coefficient
  have hdet := hDetect (lowerMaskedFourthSequence B m) r m hr hm hrm hmTop hcal.effective
    hcal.count hcal.mask_budget hcal.cover hcal.variance hcal.coefficient hcal.small
  refine ⟨hprofile,?_⟩
  have hlog : Tendsto (fun n => Real.log (m n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmTop)
  filter_upwards [hdet,hcal.fields,eventually_lowerMaskedFourth_membership hB hm hcal,
    hprofile.eventually (eventually_le_nhds (by norm_num : (1 : ℝ) < 2)),
    hlog.eventually (eventually_ge_atTop 1),eventually_ge_atTop 1]
    with n hnDet hnFields hnMom hnUpper hnL hn
  have hgpos : 0 < independentAbsGaussianMean (r n) :=
    (by positivity : 0 < Real.sqrt (2/Real.pi)).trans_le (independentAbsGaussianMean_lower (hr n))
  have hG := (div_le_iff₀ hgpos).mp hnUpper
  have htarget := lowerMaskedFourthIntrinsicRate_le_raw (by omega : 0 < n) (zero_lt_one.trans_le hnL)
    (zero_le_one.trans (log_exp_mul_nat_ge_one (by nlinarith [hr n,hm n] : 1 ≤ r n*m n)))
    (lower_dimensionLog_le_three_rareLog (hr n) (hrm n) hnL) (hB n)
    (gaussianMaximumMean_nonneg _) hgpos.le hG
  have hIDs := maskedFourthFamily_identities hn hnFields
  have hD : lowerFamilyRareWidthScale (lowerMaskedFourthSequence B m n) n (r n) =
      lowerMaskedFourthRawWidth n (Real.log (m n : ℝ)) (B n) (independentAbsGaussianMean (r n)) := by
    unfold lowerFamilyRareWidthScale lowerMaskedFourthRawWidth lowerMaskedFourthSequence
    rw [hIDs.2.2.1]
    ring
  rw [hD] at hnDet
  have hscaled := mul_le_mul_of_nonneg_left htarget (show 0 ≤ c/128 by positivity)
  have hscaled' : c/128*lowerMaskedFourthIntrinsicRate n (dimensionLog (r n*m n)) (B n)
      (gaussianMaximumMean (lowerFamilyGaussianFactor (lowerMaskedFourthSequence B m n) (r n) (m n))) ≤
      c*lowerMaskedFourthRawWidth n (Real.log (m n : ℝ)) (B n) (independentAbsGaussianMean (r n)) := by
    convert hscaled using 1 <;> ring
  exact ⟨lemma_lower_family_properties _ hn (hr n) (hm n),hnMom,
    hscaled'.trans hnDet.1,hscaled'.trans hnDet.2⟩

end
end RectangleCLTArxivV1
