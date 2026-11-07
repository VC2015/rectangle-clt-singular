import RectangleCLTCompanion.SplitV4.Printed.DenseCalibration
import RectangleCLTCompanion.SplitV4.FourthMomentLower
import RectangleCLTCompanion.SplitV4.Printed.LowerPrintedThreshold

/-! The dense lower construction at the manuscript's exact `B/2`
amplitude, assembled from the calibrated genuine common-family comparison.
No previously proved dense final lower bound is an input. -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

theorem printedDenseRateConversion_pos (q : ℝ) : 0<printedDenseRateConversion q :=
  Real.rpow_pos_of_pos (by norm_num) _

theorem printedDenseConstant_pos (q : ℝ) : 0<printedDenseConstant q :=
  div_pos (by positivity) (printedDenseRateConversion_pos q)

theorem printed_dense_rate_pos {n m : ℕ} {q B : ℝ} (hn : 1≤n) (hm : 2≤m) (hB : 2≤B) :
    0<denseMomentLowerRate n m q B := by
  rw [denseMomentLowerRate_eq n m hm q B]
  exact denseLowerEnvelopeRate_pos (by omega) (Real.log_pos (by exact_mod_cast hm)) (by linarith)

theorem printed_dense_rate_conversion_identity {B : ℝ} (hB : 2≤B) (q : ℝ) :
    (B/printedDenseBudget B)*denseLowerRateConversion q (printedDenseBudget B)=
      printedDenseRateConversion q := by
  have hD : printedDenseBudget B≠0 := (by have := (printedDenseBudget_bounds hB).1; linarith : 0<printedDenseBudget B).ne'
  have hB0 : B≠0 := by linarith
  unfold printedDenseRateConversion denseLowerRateConversion
  rw [show (7/2-2/q : ℝ)=(5/2-2/q)+1 by ring,Real.rpow_add (by norm_num : (0:ℝ)<2),Real.rpow_one]
  unfold printedDenseBudget
  unfold printedDenseBudget at hD
  field_simp [hD,hB0]
  <;> ring

/-- Exact conversion from the printed envelope rate to the actual
amplified comparison scale. Its limit is independent of fixed B. -/
theorem tendsto_printedDense_rate_div_scale {m : ℕ → ℕ} {q B : ℝ}
    (hq : 4<q) (hB : 2≤B) (hm : ∀ n,2≤m n) (hmTop : Tendsto m atTop atTop)
    (hrate : Tendsto (fun n => denseMomentLowerRate n (m n) q B) atTop (𝓝 0)) :
    Tendsto (fun n => denseMomentLowerRate n (m n) q B/
      amplifiedSymmetricLowerScale (printedDenseParameters q B n (m n)) n (m n))
      atTop (𝓝 (printedDenseRateConversion q)) := by
  have hD := (printedDenseBudget_bounds hB).1
  have hc := denseFamilyCalibration hq hD hm hmTop (printed_dense_auxiliary_rate_tendsto hB hrate)
  have hh := hc.rateRatio.const_mul (B/printedDenseBudget B)
  rw [printed_dense_rate_conversion_identity hB q] at hh
  apply hh.congr
  intro n
  change (B/printedDenseBudget B)*(denseMomentLowerRate n (m n) q (printedDenseBudget B)/_)=_
  rw [dense_rate_budget_rescale n (m n) q (by linarith : B≠0)]
  have hD0 : printedDenseBudget B≠0 := by linarith
  have hB0 : B≠0 := by linarith
  have hf : (B/printedDenseBudget B)*(printedDenseBudget B/B)=1 := by field_simp
  calc
    _ = ((B/printedDenseBudget B)*(printedDenseBudget B/B))*
      (denseMomentLowerRate n (m n) q B/
        amplifiedSymmetricLowerScale (printedDenseParameters q B n (m n)) n (m n)) := by dsimp [printedDenseParameters]; ring
    _ = _ := by rw [hf,one_mul]

theorem tendsto_printedDense_discrepancy_div_rate {m : ℕ → ℕ} [∀ n,NeZero (m n)] {q B : ℝ}
    (hq : 4<q) (hB : 2≤B) (hm : ∀ n,2≤m n) (hmTop : Tendsto m atTop atTop)
    (hrate : Tendsto (fun n => denseMomentLowerRate n (m n) q B) atTop (𝓝 0)) :
    Tendsto (fun n => familyShiftedCDFDifference (printedDenseParameters q B n (m n)) n (m n)
      (printedNormalMaxThreshold (m n))/denseMomentLowerRate n (m n) q B)
      atTop (𝓝 (printedDenseConstant q)) := by
  have hc := denseFamilyCalibration hq (printedDenseBudget_bounds hB).1 hm hmTop
    (printed_dense_auxiliary_rate_tendsto hB hrate)
  have hπ : ∀ᶠ n in atTop,(printedDenseParameters q B n (m n)).pi=(boundedFamilyParameters n (m n)).pi :=
    Eventually.of_forall (fun n => by rw [printedDenseParameters,denseFamilyParameters_pi,boundedFamilyParameters_pi])
  have hl := tendsto_amplifiedFamily_discrepancy_printed hm hmTop hc.small hc.thetaMatch hπ
    hc.amplificationLarge hc.amplificationSmall
  have hh := hl.div (tendsto_printedDense_rate_div_scale hq hB hm hmTop hrate)
    (printedDenseRateConversion_pos q).ne'
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  dsimp only [Pi.div_apply]
  exact discrepancy_rate_quotient (amplifiedSymmetricLowerScale_pos _ hn (hm n)).ne'
    (printed_dense_rate_pos hn (hm n) hB).ne'

theorem tendsto_printedDense_orthantError_div_rate {m : ℕ → ℕ} [∀ n,NeZero (m n)] {q B : ℝ}
    (hq : 4<q) (hB : 2≤B) (hm : ∀ n,2≤m n) (hmTop : Tendsto m atTop atTop)
    (hrate : Tendsto (fun n => denseMomentLowerRate n (m n) q B) atTop (𝓝 0)) :
    Tendsto (fun n => rectangleError (familyArrayLaw (printedDenseParameters q B n (m n)) n (m n))
      (sumVector (familyNormalizedObservations (printedDenseParameters q B n (m n))))
      (familyGaussianSquareFactor (printedDenseParameters q B n (m n)) (m n))
      (familyOrthant (m n*m n) ((printedDenseParameters q B n (m n)).scale*printedNormalMaxThreshold (m n)))/
        denseMomentLowerRate n (m n) q B) atTop (𝓝 (printedDenseConstant q)) := by
  have hh := (tendsto_printedDense_discrepancy_div_rate hq hB hm hmTop hrate).abs
  rw [abs_of_pos (printedDenseConstant_pos q)] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [familyShiftedCDFDifference_rectangleError _ _ _ _ (familyGaussianSquareFactor_gram _ _),
    abs_div,abs_of_pos (printed_dense_rate_pos hn (hm n) hB)]

theorem printedDense_distance_ereal_liminf {m : ℕ → ℕ} [∀ n,NeZero (m n)] {q B : ℝ}
    (hq : 4<q) (hB : 2≤B) (hm : ∀ n,2≤m n) (hmTop : Tendsto m atTop atTop)
    (hrate : Tendsto (fun n => denseMomentLowerRate n (m n) q B) atTop (𝓝 0)) :
    ((printedDenseConstant q : ℝ) : EReal)≤liminf (fun n =>
      ((familyComparisonDistance (printedDenseParameters q B n (m n)) n (m n)/
        denseMomentLowerRate n (m n) q B : ℝ) : EReal)) atTop := by
  have hl := continuous_coe_real_ereal.continuousAt.tendsto.comp
    (tendsto_printedDense_discrepancy_div_rate hq hB hm hmTop hrate)
  have hm' : ∀ᶠ n in atTop,
      ((familyShiftedCDFDifference (printedDenseParameters q B n (m n)) n (m n)
        (printedNormalMaxThreshold (m n))/denseMomentLowerRate n (m n) q B : ℝ) : EReal)≤
      ((familyComparisonDistance (printedDenseParameters q B n (m n)) n (m n)/
        denseMomentLowerRate n (m n) q B : ℝ) : EReal) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact_mod_cast div_le_div_of_nonneg_right (familyShiftedCDFDifference_le_distance _ _ _ _)
      (printed_dense_rate_pos hn (hm n) hB).le
  have hh := liminf_le_liminf hm'
  have hEq := hl.liminf_eq
  simp only [Function.comp_def] at hEq
  rw [hEq] at hh
  exact hh

structure PrintedDenseLowerConstruction (q B : ℝ) (m : ℕ → ℕ) : Prop where
  parametersMatch : ∀ᶠ n in atTop,
    (printedDenseParameters q B n (m n)).theta=fourthLowerTheta n (Real.log (m n : ℝ)) ∧
    (printedDenseParameters q B n (m n)).amplitude=printedDenseAmplitude n (Real.log (m n : ℝ)) q B
  properties : ∀ᶠ n in atTop,CommonSymmetricFamilyProperties (printedDenseParameters q B n (m n)) n (m n)
  polynomialClass : ∀ᶠ n in atTop,PolynomialIndependentHypotheses
    (familyArrayLaw (printedDenseParameters q B n (m n)) n (m n))
    (familyRawObservations (printedDenseParameters q B n (m n))) q B
  matchingGaussianCovariance : ∀ᶠ n in atTop,
    familyGaussianSquareFactor (printedDenseParameters q B n (m n)) (m n)*
      (familyGaussianSquareFactor (printedDenseParameters q B n (m n)) (m n)).transpose=
    covariance (familyArrayLaw (printedDenseParameters q B n (m n)) n (m n))
      (sumVector (familyNormalizedObservations (printedDenseParameters q B n (m n))))
  orthantLimit : Tendsto (fun n => rectangleError (familyArrayLaw (printedDenseParameters q B n (m n)) n (m n))
    (sumVector (familyNormalizedObservations (printedDenseParameters q B n (m n))))
    (familyGaussianSquareFactor (printedDenseParameters q B n (m n)) (m n))
    (familyOrthant (m n*m n) ((printedDenseParameters q B n (m n)).scale*printedNormalMaxThreshold (m n)))/
      denseMomentLowerRate n (m n) q B) atTop (𝓝 (printedDenseConstant q))
  positiveConstant : 0<printedDenseConstant q
  distanceLiminf : ((printedDenseConstant q : ℝ) : EReal)≤liminf (fun n =>
    ((familyComparisonDistance (printedDenseParameters q B n (m n)) n (m n)/
      denseMomentLowerRate n (m n) q B : ℝ) : EReal)) atTop

theorem printedDenseLower_of_two_le {m : ℕ → ℕ} {q B : ℝ}
    (hq : 4<q) (hB : 2≤B) (hm : ∀ n,2≤m n) (hmTop : Tendsto m atTop atTop)
    (hrate : Tendsto (fun n => denseMomentLowerRate n (m n) q B) atTop (𝓝 0)) :
    PrintedDenseLowerConstruction q B m := by
  letI : ∀ n,NeZero (m n) := fun n => ⟨by have := hm n; omega⟩
  refine ⟨eventually_printedDense_parameters hq hB hm hmTop hrate,?_,
    eventually_printedDense_polynomialIndependent hq hB hm hmTop hrate,?_,
    tendsto_printedDense_orthantError_div_rate hq hB hm hmTop hrate,
    printedDenseConstant_pos q,printedDense_distance_ereal_liminf hq hB hm hmTop hrate⟩
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact symmetricFamilyProperties _ hn (hm n)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    rw [familyGaussianSquareFactor_gram,familyNormalizedObservations_covariance _ hn]

/-- The exact printed dense construction under the literal asymptotic
dimension assumptions; finite initial dimensions impose no extra condition. -/
theorem printedDenseLower {m : ℕ → ℕ} {q B : ℝ}
    (hq : 4<q) (hB : 2≤B) (hmTop : Tendsto m atTop atTop)
    (hrate : Tendsto (fun n => denseMomentLowerRate n (m n) q B) atTop (𝓝 0)) :
    PrintedDenseLowerConstruction q B m := by
  let m' := fun n => max 2 (m n)
  have heq : ∀ᶠ n in atTop,max 2 (m n)=m n := by
    filter_upwards [hmTop.eventually (eventually_ge_atTop 2)] with n hn
    exact max_eq_right hn
  have hm'Top : Tendsto m' atTop atTop := tendsto_atTop_mono (fun n => le_max_right 2 (m n)) hmTop
  have hr' : Tendsto (fun n => denseMomentLowerRate n (m' n) q B) atTop (𝓝 0) := by
    apply hrate.congr'
    filter_upwards [heq] with n hn
    dsimp only [m']
    rw [hn]
  have h := printedDenseLower_of_two_le hq hB (fun n => le_max_left 2 (m n)) hm'Top hr'
  refine ⟨?_,?_,?_,?_,?_,h.positiveConstant,?_⟩
  · filter_upwards [h.parametersMatch,heq] with n hn he
    exact he ▸ hn
  · filter_upwards [h.properties,heq] with n hn he
    exact he ▸ hn
  · filter_upwards [h.polynomialClass,heq] with n hn he
    exact he ▸ hn
  · filter_upwards [h.matchingGaussianCovariance,heq] with n hn he
    exact he ▸ hn
  · apply h.orthantLimit.congr'
    filter_upwards [heq] with n hn
    rw [hn]
  · apply h.distanceLiminf.trans_eq
    apply liminf_congr
    filter_upwards [heq] with n hn
    rw [hn]

end
end RectangleCLT.Companion.SplitV4.Printed
