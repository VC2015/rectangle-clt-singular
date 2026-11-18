import RectangleCLTArxivV1.LowerSparseCalibration
import RectangleCLTArxivV1.LowerSparseWidthLimits
import RectangleCLTArxivV1.LowerSparseUpperRate
import RectangleCLTArxivV1.PairedIntrinsicBennett

/-! Actual sparse polynomial observations and their detecting rectangles. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set Filter RectangleCLT RectangleCLT.Companion
open RectangleCLT.Companion.SplitV4
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false

theorem eventually_lowerSparse_membership {q : ℝ} (hq : 2 < q) {B : ℕ → ℝ} {r m : ℕ → ℕ}
    (hB : ∀ n, 2 ≤ B n) (hm : ∀ n, 2 ≤ m n)
    (hK : Tendsto (fun n => sparseLowerKhat n (Real.log (m n : ℝ)) q (B n)) atTop atTop)
    (hcal : LowerSparseCalibration q B r m) :
    ∀ᶠ n in atTop, PolynomialFourthHypotheses
      (lowerFamilyArrayLaw (lowerSparseSequence q B m n) n (r n) (m n))
      (lowerFamilyRawObservations (lowerSparseSequence q B m n)) q (B n) := by
  filter_upwards [hcal.fields,hK.eventually (eventually_ge_atTop 2),eventually_ge_atTop 1]
    with n hnFields hnK hn
  let P := lowerSparseSequence q B m n
  have hn0 : 0 < n := by omega
  have hBn : 0 < B n := by linarith [hB n]
  have hL : 0 < Real.log (m n : ℝ) := Real.log_pos (by exact_mod_cast hm n)
  have henv : PolynomialEnvelopeHypotheses (lowerFamilyArrayLaw P n (r n) (m n))
      (lowerFamilyRawObservations P) q (B n) := by
    apply lowerFamily_polynomialEnvelope_of_factor P hn (by linarith : 1 ≤ q)
    have ha : P.amplitude*P.theta^(1/q) = B n/2 := by
      change (lowerSparseSequence q B m n).amplitude*(lowerSparseSequence q B m n).theta^(1/q) = _
      rw [hnFields.2.2,hnFields.1]
      exact sparseLower_envelope_identity hn0 hL hnK
    rw [ha]
    have hs := familyScale_le_one P
    linarith [hB n]
  apply lowerFamily_polynomialFourth_of_moments P hn henv
  have hf : P.theta*P.pi*P.amplitude^4 = (B n)^2/16 := by
    change (lowerSparseSequence q B m n).theta*(lowerSparseSequence q B m n).pi*
      (lowerSparseSequence q B m n).amplitude^4 = _
    rw [hnFields.1,hnFields.2.1,hnFields.2.2]
    exact sparseLower_fourth_identity hn0 hL hBn hnK
  rw [hf]
  have hbase : 1+4*P.variance-5*P.variance^2 ≤ 9/5 := by nlinarith [sq_nonneg (P.variance-2/5)]
  have hB2 : (4 : ℝ) ≤ (B n)^2 := by nlinarith [hB n]
  linarith

/-- All scalar parameter calibrations are checked before the actual
law is used. This reduction has no assumed probability comparison. -/
theorem exists_lowerSparse_actual_detection_constant (q : ℝ) (hq : 2 < q) :
    ∃ c : ℝ, 0 < c ∧ ∀ (B : ℕ → ℝ) (r m : ℕ → ℕ)
      [∀ n, NeZero (r n)] [∀ n, NeZero (m n)],
      (∀ n, 2 ≤ B n) → (∀ n, 1 ≤ r n) → (∀ n, 2 ≤ m n) → (∀ n, r n ≤ m n) →
      Tendsto m atTop atTop →
      Tendsto (fun n => sparseLowerKhat n (Real.log (m n : ℝ)) q (B n)) atTop atTop →
      Tendsto (fun n => sparseLowerLog n (Real.log (m n : ℝ)) q (B n)/Real.log (m n : ℝ)) atTop (𝓝 0) →
      Tendsto (fun n => sparseLowerTheta n (Real.log (m n : ℝ)) q (B n)) atTop (𝓝 0) →
      Tendsto (fun n => sparseLowerVariance n (Real.log (m n : ℝ)) q (B n)) atTop (𝓝 0) →
      Tendsto (fun n => sparseLowerAmplitude n (Real.log (m n : ℝ)) q (B n)*
        sparseLowerCount n (Real.log (m n : ℝ)) q (B n)/Real.log (m n : ℝ)) atTop atTop →
      Tendsto (fun n => lowerSparseRawWidth n (Real.log (m n : ℝ)) q (B n)
        (independentAbsGaussianMean (r n))) atTop (𝓝 0) →
      Tendsto (fun n => gaussianMaximumMean (lowerFamilyGaussianFactor (lowerSparseSequence q B m n)
        (r n) (m n))/independentAbsGaussianMean (r n)) atTop (𝓝 1) ∧
      ∀ᶠ n in atTop,
        LowerRectangularFamilyProperties (lowerSparseSequence q B m n) n (r n) (m n) ∧
        PolynomialFourthHypotheses (lowerFamilyArrayLaw (lowerSparseSequence q B m n) n (r n) (m n))
          (lowerFamilyRawObservations (lowerSparseSequence q B m n)) q (B n) ∧
        c*lowerSparseRawWidth n (Real.log (m n : ℝ)) q (B n) (independentAbsGaussianMean (r n)) ≤
          -lowerFamilyShiftedCDFDifference (lowerSparseSequence q B m n) n (r n) (m n) (lowerLeadingThreshold (r n)) ∧
        c*lowerSparseRawWidth n (Real.log (m n : ℝ)) q (B n) (independentAbsGaussianMean (r n)) ≤
          lowerFamilyComparisonDistance (lowerSparseSequence q B m n) n (r n) (m n) := by
  obtain ⟨c,hc,hDetect⟩ := exists_lowerFamily_masked_width_detection_constant
  refine ⟨c,hc,?_⟩
  intro B r m _ _ hB hr hm hrm hmTop hK hΛ hθ hv hEff hraw
  have hcal := lowerSparseCalibration_of_scalar_limits q hB hmTop hK hΛ hθ hv hEff hraw
  have hprofile := lowerFamilyMasked_width_profile hr hm hmTop hcal.variance hcal.small hcal.coefficient
  have hdet := hDetect (lowerSparseSequence q B m) r m hr hm hrm hmTop hcal.effective
    hcal.count hcal.mask_budget hcal.cover hcal.variance hcal.coefficient hcal.small
  refine ⟨hprofile,?_⟩
  filter_upwards [hdet,hcal.fields,eventually_lowerSparse_membership hq hB hm hK hcal,eventually_ge_atTop 1]
    with n hnDet hnFields hnMom hn
  have hIDs := sparseFamily_identities hn hnFields
  have hD : lowerFamilyRareWidthScale (lowerSparseSequence q B m n) n (r n) =
      lowerSparseRawWidth n (Real.log (m n : ℝ)) q (B n) (independentAbsGaussianMean (r n)) := by
    unfold lowerFamilyRareWidthScale lowerSparseRawWidth lowerSparseSequence
    rw [hIDs.2.2.1]
    ring
  rw [hD] at hnDet
  exact ⟨lemma_lower_family_properties _ hn (hr n) (hm n),hnMom,hnDet⟩

/-- In the sparse regime the actual new Theorem 2(ii) upper bound has
the order of the displayed sparse envelope term. -/
theorem exists_lowerSparse_upper_constant (q : ℝ) (hq : 2 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ → ℝ) (r m : ℕ → ℕ)
      (P : ℕ → SymmetricFamilyParameters),
      (∀ n, 2 ≤ B n) → (∀ n, 1 ≤ r n) → (∀ n, 1 ≤ m n) →
      Tendsto (fun n => lowerSparseIntrinsicK n (dimensionLog (r n*m n)) q (B n)) atTop atTop →
      (∀ᶠ n in atTop, PolynomialFourthHypotheses (lowerFamilyArrayLaw (P n) n (r n) (m n))
        (lowerFamilyRawObservations (P n)) q (B n)) →
      ∀ᶠ n in atTop, lowerFamilyComparisonDistance (P n) n (r n) (m n) ≤
        C*lowerSparseIntrinsicRate n (dimensionLog (r n*m n)) q (B n)
          (gaussianMaximumMean (lowerFamilyGaussianFactor (P n) (r n) (m n))) := by
  obtain ⟨C,hC,hBound⟩ := theorem_2_ii_intrinsic q hq
  refine ⟨2*C,by positivity,?_⟩
  intro B r m P hB hr hm hK hX
  have hRate := eventually_lowerSparse_width_rate_le_twice (p := fun n => r n*m n)
    (g := fun n => gaussianMaximumMean (lowerFamilyGaussianFactor (P n) (r n) (m n))) hB
    (fun n => by nlinarith [hr n,hm n]) (fun n => gaussianMaximumMean_nonneg _) hK
  filter_upwards [hX,hRate,eventually_ge_atTop 1] with n hnX hnRate hn
  have hp : 1 ≤ r n*m n := by nlinarith [hr n,hm n]
  have hW : normalizedObservationSum (lowerFamilyRawObservations (P n) : Fin n →
      (Fin n → LowerFamilySeed (r n) (m n)) → Vector (r n*m n)) =
      sumVector (lowerFamilyNormalizedObservations (P n)) := by
    funext z
    simp only [normalizedObservationSum,sumVector,lowerFamilyNormalizedObservations,Finset.smul_sum,one_div]
  have hA : lowerFamilyGaussianFactor (P n) (r n) (m n)*(lowerFamilyGaussianFactor (P n) (r n) (m n)).transpose =
      covariance (lowerFamilyArrayLaw (P n) n (r n) (m n)) (normalizedObservationSum (lowerFamilyRawObservations (P n))) := by
    rw [hW,lowerFamilyNormalizedObservations_covariance (P n) hn]
    exact lowerFamilyGaussianFactor_gram (P n) (r n) (m n)
  have hh := hBound (r n*m n) n hp hn (B n) (by linarith [hB n])
    (lowerFamilyArrayLaw (P n) n (r n) (m n)) (lowerFamilyRawObservations (P n)) hnX
    (lowerFamilyGaussianFactor (P n) (r n) (m n)) hA
  rw [hW] at hh
  apply hh.trans
  have hMin := mul_le_mul_of_nonneg_left (min_le_right (1 : ℝ)
    (polynomialFourthWidthRate n (r n*m n) (B n) q
      (gaussianMaximumMean (lowerFamilyGaussianFactor (P n) (r n) (m n))))) hC.le
  have hScale := mul_le_mul_of_nonneg_left hnRate hC.le
  exact (hMin.trans hScale).trans_eq (by ring)

/-- Theorem 8 with the exact width-sensitive sparse regime and the actual
constructed finite iid centrally symmetric observations in `C_q(B_n)`. -/
theorem theorem_8_sparse_polynomial_moment_lower (q : ℝ) (hq : 2 < q) :
    ∃ c : ℝ, 0 < c ∧ ∀ (B : ℕ → ℝ) (r m : ℕ → ℕ)
      [∀ n, NeZero (r n)] [∀ n, NeZero (m n)],
      (∀ n, 2 ≤ B n) → (∀ n, 1 ≤ r n) → (∀ n, 2 ≤ m n) → (∀ n, r n ≤ m n) →
      Tendsto m atTop atTop →
      Tendsto (fun n => lowerSparseIntrinsicK n (dimensionLog (r n*m n)) q (B n)) atTop atTop →
      Tendsto (fun n => Real.log (lowerSparseIntrinsicK n (dimensionLog (r n*m n)) q (B n))/dimensionLog (r n*m n))
        atTop (𝓝 0) →
      Tendsto (fun n => lowerSparseIntrinsicRate n (dimensionLog (r n*m n)) q (B n)
        (independentAbsGaussianMean (r n))) atTop (𝓝 0) →
      Tendsto (fun n => gaussianMaximumMean (lowerFamilyGaussianFactor (lowerSparseSequence q B m n)
        (r n) (m n))/independentAbsGaussianMean (r n)) atTop (𝓝 1) ∧
      ∀ᶠ n in atTop,
        LowerRectangularFamilyProperties (lowerSparseSequence q B m n) n (r n) (m n) ∧
        PolynomialFourthHypotheses (lowerFamilyArrayLaw (lowerSparseSequence q B m n) n (r n) (m n))
          (lowerFamilyRawObservations (lowerSparseSequence q B m n)) q (B n) ∧
        c*lowerSparseIntrinsicRate n (dimensionLog (r n*m n)) q (B n)
          (gaussianMaximumMean (lowerFamilyGaussianFactor (lowerSparseSequence q B m n) (r n) (m n))) ≤
          -lowerFamilyShiftedCDFDifference (lowerSparseSequence q B m n) n (r n) (m n) (lowerLeadingThreshold (r n)) ∧
        c*lowerSparseIntrinsicRate n (dimensionLog (r n*m n)) q (B n)
          (gaussianMaximumMean (lowerFamilyGaussianFactor (lowerSparseSequence q B m n) (r n) (m n))) ≤
          lowerFamilyComparisonDistance (lowerSparseSequence q B m n) n (r n) (m n) := by
  obtain ⟨c,hc,hActual⟩ := exists_lowerSparse_actual_detection_constant q hq
  refine ⟨c/256,by positivity,?_⟩
  intro B r m _ _ hB hr hm hrm hmTop hK hlogSmall hsmall
  have hKh := tendsto_lowerSparseKhat hB hr hrm hmTop hK
  have hΛ := tendsto_lowerSparseLog_div_rareLog hB hr hrm hmTop hK hlogSmall
  have hraw := tendsto_lowerSparseRawWidth hq hB hr hrm hmTop hK hsmall
  have hθ := tendsto_lowerSparseTheta hB hr hmTop hKh hraw
  have hv := tendsto_lowerSparseVariance hq hB hr hmTop hKh hraw
  have hEff := tendsto_lowerSparseEffectiveAmplitude hB hr hmTop hKh hraw
  obtain ⟨hprofile,hevent⟩ := hActual B r m hB hr hm hrm hmTop hKh hΛ hθ hv hEff hraw
  refine ⟨hprofile,?_⟩
  have hlog : Tendsto (fun n => Real.log (m n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmTop)
  filter_upwards [hevent,hprofile.eventually (eventually_le_nhds (by norm_num : (1 : ℝ) < 2)),
    eventually_lowerSparseLog_bounds hB hr hrm hmTop hK,hKh.eventually (eventually_ge_atTop 2),
    hlog.eventually (eventually_ge_atTop 1),eventually_ge_atTop 1]
    with n hnEvent hnUpper hnLogs hnKh hnL hn
  have hgpos : 0 < independentAbsGaussianMean (r n) :=
    (by positivity : 0 < Real.sqrt (2/Real.pi)).trans_le (independentAbsGaussianMean_lower (hr n))
  have hG := (div_le_iff₀ hgpos).mp hnUpper
  have hp : 1 ≤ r n*m n := by nlinarith [hr n,hm n]
  have htarget := lowerSparseIntrinsicRate_le_raw hq (by omega : 0 < n) (zero_lt_one.trans_le hnL)
    (zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp)) (lower_dimensionLog_le_three_rareLog (hr n) (hrm n) hnL)
    (show 0 < B n by linarith [hB n]) hG hgpos.le hnKh hnLogs.2
  have hscaled := mul_le_mul_of_nonneg_left htarget (show 0 ≤ c/256 by positivity)
  have hscaled' : c/256*lowerSparseIntrinsicRate n (dimensionLog (r n*m n)) q (B n)
      (gaussianMaximumMean (lowerFamilyGaussianFactor (lowerSparseSequence q B m n) (r n) (m n))) ≤
      c*lowerSparseRawWidth n (Real.log (m n : ℝ)) q (B n) (independentAbsGaussianMean (r n)) := by
    convert hscaled using 1 <;> ring
  exact ⟨hnEvent.1,hnEvent.2.1,hscaled'.trans hnEvent.2.2.1,hscaled'.trans hnEvent.2.2.2⟩

/-- The final upper comparison in Theorem 8 is proved for these same
actual observations using the new Theorem 2(ii). -/
theorem theorem_8_sparse_polynomial_moment_two_sided (q : ℝ) (hq : 2 < q) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (B : ℕ → ℝ) (r m : ℕ → ℕ)
      [∀ n, NeZero (r n)] [∀ n, NeZero (m n)],
      (∀ n, 2 ≤ B n) → (∀ n, 1 ≤ r n) → (∀ n, 2 ≤ m n) → (∀ n, r n ≤ m n) →
      Tendsto m atTop atTop →
      Tendsto (fun n => lowerSparseIntrinsicK n (dimensionLog (r n*m n)) q (B n)) atTop atTop →
      Tendsto (fun n => Real.log (lowerSparseIntrinsicK n (dimensionLog (r n*m n)) q (B n))/dimensionLog (r n*m n))
        atTop (𝓝 0) →
      Tendsto (fun n => lowerSparseIntrinsicRate n (dimensionLog (r n*m n)) q (B n)
        (independentAbsGaussianMean (r n))) atTop (𝓝 0) →
      Tendsto (fun n => gaussianMaximumMean (lowerFamilyGaussianFactor (lowerSparseSequence q B m n)
        (r n) (m n))/independentAbsGaussianMean (r n)) atTop (𝓝 1) ∧
      ∀ᶠ n in atTop,
        LowerRectangularFamilyProperties (lowerSparseSequence q B m n) n (r n) (m n) ∧
        PolynomialFourthHypotheses (lowerFamilyArrayLaw (lowerSparseSequence q B m n) n (r n) (m n))
          (lowerFamilyRawObservations (lowerSparseSequence q B m n)) q (B n) ∧
        c*lowerSparseIntrinsicRate n (dimensionLog (r n*m n)) q (B n)
          (gaussianMaximumMean (lowerFamilyGaussianFactor (lowerSparseSequence q B m n) (r n) (m n))) ≤
          lowerFamilyComparisonDistance (lowerSparseSequence q B m n) n (r n) (m n) ∧
        lowerFamilyComparisonDistance (lowerSparseSequence q B m n) n (r n) (m n) ≤
          C*lowerSparseIntrinsicRate n (dimensionLog (r n*m n)) q (B n)
            (gaussianMaximumMean (lowerFamilyGaussianFactor (lowerSparseSequence q B m n) (r n) (m n))) := by
  obtain ⟨c,hc,hLower⟩ := theorem_8_sparse_polynomial_moment_lower q hq
  obtain ⟨C,hC,hUpper⟩ := exists_lowerSparse_upper_constant q hq
  refine ⟨c,C,hc,hC,?_⟩
  intro B r m _ _ hB hr hm hrm hmTop hK hlogSmall hsmall
  obtain ⟨hw,hevent⟩ := hLower B r m hB hr hm hrm hmTop hK hlogSmall hsmall
  have hUpperEvent := hUpper B r m (lowerSparseSequence q B m) hB hr (fun n => by have := hm n; omega) hK
    (hevent.mono (fun _ hn => hn.2.1))
  refine ⟨hw,?_⟩
  filter_upwards [hevent,hUpperEvent] with n hn hnUpper
  exact ⟨hn.1,hn.2.1,hn.2.2.2,hnUpper⟩

end
end RectangleCLTArxivV1
