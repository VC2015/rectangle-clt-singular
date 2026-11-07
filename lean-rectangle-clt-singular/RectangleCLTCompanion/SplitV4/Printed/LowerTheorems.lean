import RectangleCLTCompanion.SplitV4.Printed.LowerPrintedThreshold
import RectangleCLTCompanion.SplitV4.SymmetricBoundedLower
import RectangleCLTCompanion.SplitV4.FourthMomentLower
import RectangleCLTCompanion.SplitV4.MaskedFourthLower
import RectangleCLTCompanion.SplitV4.SparseMomentLower

/-! Actual detecting-orthant rate asymptotics for the printed T4, T5,
T6 and T8 constructions, via global F2 at the exact m*tail=1 threshold.
Model properties and scalar rate conversions are the unchanged printed
ones; no old probability-discrepancy limit is used. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

theorem tendsto_boundedFamily_discrepancy_div_rate_printed {m : ℕ → ℕ} [∀ n, NeZero (m n)]
    (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => Real.log (m n : ℝ) ^ 3 / n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => familyShiftedCDFDifference (boundedFamilyParameters n (m n)) n (m n)
      (printedNormalMaxThreshold (m n)) / boundedSymmetricLowerRate n (m n)) atTop (𝓝 (1 / (8 * Real.exp 1))) := by
  have hh := (boundedFamily_printed_discrepancy_div_scale hm hmTop hsmall).div
    (tendsto_boundedSymmetricLowerRate_div_scale hm hmTop) (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).ne'
  rw [bounded_lower_constant_identity] at hh
  apply hh.congr'
  filter_upwards [eventually_boundedLowerScale_pos hmTop, eventually_boundedSymmetricLowerRate_pos hm] with n hd hr
  field_simp [hd.ne', hr.ne']


/-- The actual orthant in the construction has the sharp paper constant. -/
theorem tendsto_boundedFamily_orthantError_div_rate_printed {m : ℕ → ℕ} [∀ n, NeZero (m n)]
    (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => Real.log (m n : ℝ) ^ 3 / n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      rectangleError (familyArrayLaw (boundedFamilyParameters n (m n)) n (m n))
        (sumVector (familyNormalizedObservations (boundedFamilyParameters n (m n))))
        (familyGaussianSquareFactor (boundedFamilyParameters n (m n)) (m n))
        (familyOrthant (m n * m n)
          ((boundedFamilyParameters n (m n)).scale * printedNormalMaxThreshold (m n))) /
        boundedSymmetricLowerRate n (m n)) atTop (𝓝 (1 / (8 * Real.exp 1))) := by
  have hh := (continuous_abs.tendsto (1 / (8 * Real.exp 1))).comp
    (tendsto_boundedFamily_discrepancy_div_rate_printed hm hmTop hsmall)
  rw [abs_of_pos (by positivity : (0 : ℝ) < 1 / (8 * Real.exp 1))] at hh
  apply hh.congr'
  filter_upwards [eventually_boundedSymmetricLowerRate_pos hm] with n hn
  dsimp only [Function.comp_apply]
  rw [familyShiftedCDFDifference_rectangleError _ _ _ _ (familyGaussianSquareFactor_gram _ _),
    abs_div, abs_of_pos hn]

/-- An equivalent real formulation of the full-distance lower limit. -/
theorem tendsto_fourthFamily_discrepancy_div_rate_printed {m : ℕ → ℕ} [∀ n, NeZero (m n)]
    (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hrate : Tendsto (fun n : ℕ => fourthMomentLowerRate n (m n)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => familyShiftedCDFDifference (fourthFamilyParameters n (m n)) n (m n)
      (printedNormalMaxThreshold (m n))/fourthMomentLowerRate n (m n)) atTop
      (𝓝 (1/(2*Real.sqrt 2*Real.exp 1))) := by
  have hcal := fourthFamilyCalibration hm hmTop hrate
  have hπ : ∀ᶠ n : ℕ in atTop,
      (fourthFamilyParameters n (m n)).pi = (boundedFamilyParameters n (m n)).pi :=
    Eventually.of_forall (fun n => by rw [fourthFamilyParameters_pi, boundedFamilyParameters_pi])
  have hlim := tendsto_amplifiedFamily_discrepancy_printed hm hmTop hcal.small hcal.thetaMatch hπ
    hcal.amplificationLarge hcal.amplificationSmall
  have hh := hlim.div hcal.rateRatio (by norm_num : (4 : ℝ) ≠ 0)
  rw [fourth_lower_constant_identity] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  dsimp only [Pi.div_apply]
  exact discrepancy_rate_quotient (amplifiedSymmetricLowerScale_pos _ hn (hm n)).ne'
    (fourthMomentLowerRate_pos hn (hm n)).ne'

theorem tendsto_fourthFamily_orthantError_div_rate_printed {m : ℕ → ℕ} [∀ n, NeZero (m n)]
    (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hrate : Tendsto (fun n : ℕ => fourthMomentLowerRate n (m n)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      rectangleError (familyArrayLaw (fourthFamilyParameters n (m n)) n (m n))
        (sumVector (familyNormalizedObservations (fourthFamilyParameters n (m n))))
        (familyGaussianSquareFactor (fourthFamilyParameters n (m n)) (m n))
        (familyOrthant (m n*m n) ((fourthFamilyParameters n (m n)).scale*printedNormalMaxThreshold (m n))) /
        fourthMomentLowerRate n (m n)) atTop (𝓝 (1/(2*Real.sqrt 2*Real.exp 1))) := by
  have hh := (continuous_abs.tendsto (1/(2*Real.sqrt 2*Real.exp 1))).comp
    (tendsto_fourthFamily_discrepancy_div_rate_printed hm hmTop hrate)
  rw [abs_of_pos (by positivity : (0 : ℝ) < 1/(2*Real.sqrt 2*Real.exp 1))] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  dsimp only [Function.comp_apply]
  rw [familyShiftedCDFDifference_rectangleError _ _ _ _ (familyGaussianSquareFactor_gram _ _),
    abs_div, abs_of_pos (fourthMomentLowerRate_pos hn (hm n))]

theorem tendsto_maskedFourthFamily_discrepancy_div_rate_printed {B : ℕ → ℝ} {m : ℕ → ℕ} [∀ n, NeZero (m n)]
    (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop) (hBTop : Tendsto B atTop atTop)
    (hΛ : Tendsto (fun n : ℕ => maskedFourthLog (B n)/Real.log (m n : ℝ)) atTop (𝓝 0))
    (hrate : Tendsto (fun n : ℕ => maskedFourthMomentLowerRate n (m n) (B n)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => familyShiftedCDFDifference (maskedFourthFamilyParameters n (m n) (B n)) n (m n)
      (printedNormalMaxThreshold (m n))/maskedFourthMomentLowerRate n (m n) (B n)) atTop (𝓝 (-(1/(4*Real.exp 1)))) := by
  have hcal := maskedFourthFamilyCalibration hm hmTop hBTop hΛ hrate
  have hlim := tendsto_rareFamily_discrepancy_printed hm hmTop hcal.count hcal.cover hcal.variance
    hcal.coefficient hcal.small hcal.scale hcal.countCost hcal.gaussianCost
  have hh := hlim.div hcal.rateRatio (by positivity : (4*Real.sqrt 2 : ℝ) ≠ 0)
  rw [masked_fourth_lower_constant_identity] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1, hBTop.eventually (eventually_ge_atTop 2)] with n hn hnB
  dsimp only [Pi.div_apply]
  exact discrepancy_rate_quotient (familyRareLowerScale_pos _ hn (hm n)).ne'
    (maskedFourthMomentLowerRate_pos hn (hm n) hnB).ne'

theorem tendsto_maskedFourthFamily_orthantError_div_rate_printed {B : ℕ → ℝ} {m : ℕ → ℕ} [∀ n, NeZero (m n)]
    (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop) (hBTop : Tendsto B atTop atTop)
    (hΛ : Tendsto (fun n : ℕ => maskedFourthLog (B n)/Real.log (m n : ℝ)) atTop (𝓝 0))
    (hrate : Tendsto (fun n : ℕ => maskedFourthMomentLowerRate n (m n) (B n)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      rectangleError (familyArrayLaw (maskedFourthFamilyParameters n (m n) (B n)) n (m n))
        (sumVector (familyNormalizedObservations (maskedFourthFamilyParameters n (m n) (B n))))
        (familyGaussianSquareFactor (maskedFourthFamilyParameters n (m n) (B n)) (m n))
        (familyOrthant (m n*m n) ((maskedFourthFamilyParameters n (m n) (B n)).scale*printedNormalMaxThreshold (m n))) /
        maskedFourthMomentLowerRate n (m n) (B n)) atTop (𝓝 (1/(4*Real.exp 1))) := by
  have hh := (continuous_abs.tendsto (-(1/(4*Real.exp 1)))).comp
    (tendsto_maskedFourthFamily_discrepancy_div_rate_printed hm hmTop hBTop hΛ hrate)
  rw [abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 1/(4*Real.exp 1))] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1, hBTop.eventually (eventually_ge_atTop 2)] with n hn hnB
  dsimp only [Function.comp_apply]
  rw [familyShiftedCDFDifference_rectangleError _ _ _ _ (familyGaussianSquareFactor_gram _ _),
    abs_div, abs_of_pos (maskedFourthMomentLowerRate_pos hn (hm n) hnB)]

theorem tendsto_sparseFamily_discrepancy_div_rate_printed {B : ℕ → ℝ} {m : ℕ → ℕ} {q : ℝ} [∀ n, NeZero (m n)]
    (hq : 2 < q) (hB : ∀ n, 2 ≤ B n) (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hK : Tendsto (fun n => sparseMomentK n (m n) q (B n)) atTop atTop)
    (hLog : Tendsto (fun n => Real.log (sparseMomentK n (m n) q (B n))/dimensionLog (m n*m n)) atTop (𝓝 0))
    (hrate : Tendsto (fun n : ℕ => sparseMomentLowerRate n (m n) q (B n)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => familyShiftedCDFDifference (sparseFamilyParameters q n (m n) (B n)) n (m n)
      (printedNormalMaxThreshold (m n))/sparseMomentLowerRate n (m n) q (B n)) atTop (𝓝 (-(sparseMomentLowerConstant q))) := by
  have hPaper := sparsePaperCalibration hq hB hm hmTop hK hLog hrate
  have hcal := hPaper.family
  have hlim := tendsto_rareFamily_discrepancy_printed hm hmTop hcal.count hcal.cover hcal.variance
    hcal.coefficient hcal.small hcal.scale hcal.countCost hcal.gaussianCost
  have hh := hlim.div hPaper.rateRatio (sparseMomentRateConversion_pos q).ne'
  have hc : (-Real.sqrt 2*Real.exp (-1))/sparseMomentRateConversion q = -sparseMomentLowerConstant q := by
    unfold sparseMomentLowerConstant
    ring
  rw [hc] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  dsimp only [Pi.div_apply]
  exact discrepancy_rate_quotient (familyRareLowerScale_pos _ hn (hm n)).ne'
    (sparseMomentLowerRate_pos hn (hm n) (hB n)).ne'

theorem tendsto_sparseFamily_orthantError_div_rate_printed {B : ℕ → ℝ} {m : ℕ → ℕ} {q : ℝ} [∀ n, NeZero (m n)]
    (hq : 2 < q) (hB : ∀ n, 2 ≤ B n) (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hK : Tendsto (fun n => sparseMomentK n (m n) q (B n)) atTop atTop)
    (hLog : Tendsto (fun n => Real.log (sparseMomentK n (m n) q (B n))/dimensionLog (m n*m n)) atTop (𝓝 0))
    (hrate : Tendsto (fun n : ℕ => sparseMomentLowerRate n (m n) q (B n)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      rectangleError (familyArrayLaw (sparseFamilyParameters q n (m n) (B n)) n (m n))
        (sumVector (familyNormalizedObservations (sparseFamilyParameters q n (m n) (B n))))
        (familyGaussianSquareFactor (sparseFamilyParameters q n (m n) (B n)) (m n))
        (familyOrthant (m n*m n) ((sparseFamilyParameters q n (m n) (B n)).scale*printedNormalMaxThreshold (m n))) /
        sparseMomentLowerRate n (m n) q (B n)) atTop (𝓝 (sparseMomentLowerConstant q)) := by
  have hh := (continuous_abs.tendsto (-(sparseMomentLowerConstant q))).comp
    (tendsto_sparseFamily_discrepancy_div_rate_printed hq hB hm hmTop hK hLog hrate)
  rw [abs_neg, abs_of_pos (sparseMomentLowerConstant_pos q)] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  dsimp only [Function.comp_apply]
  rw [familyShiftedCDFDifference_rectangleError _ _ _ _ (familyGaussianSquareFactor_gram _ _),
    abs_div, abs_of_pos (sparseMomentLowerRate_pos hn (hm n) (hB n))]

end
end RectangleCLT.Companion.SplitV4.Printed
