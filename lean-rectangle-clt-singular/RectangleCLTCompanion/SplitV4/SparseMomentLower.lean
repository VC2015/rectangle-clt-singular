import RectangleCLTCompanion.SplitV4.SparsePaperCalibration
import RectangleCLTCompanion.SplitV4.FourthMomentLower

/-! The actual general sparse polynomial-moment lower construction (Theorem 8). -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology
namespace RectangleCLT.Companion.SplitV4
noncomputable section

theorem tendsto_sparseFamily_discrepancy_div_rate {B : ℕ → ℝ} {m : ℕ → ℕ} {q : ℝ} [∀ n, NeZero (m n)]
    (hq : 2 < q) (hB : ∀ n, 2 ≤ B n) (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hK : Tendsto (fun n => sparseMomentK n (m n) q (B n)) atTop atTop)
    (hLog : Tendsto (fun n => Real.log (sparseMomentK n (m n) q (B n))/dimensionLog (m n*m n)) atTop (𝓝 0))
    (hrate : Tendsto (fun n : ℕ => sparseMomentLowerRate n (m n) q (B n)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => familyShiftedCDFDifference (sparseFamilyParameters q n (m n) (B n)) n (m n)
      (normalMaxThreshold (m n))/sparseMomentLowerRate n (m n) q (B n)) atTop (𝓝 (-(sparseMomentLowerConstant q))) := by
  have hPaper := sparsePaperCalibration hq hB hm hmTop hK hLog hrate
  have hcal := hPaper.family
  have hlim := tendsto_familyRare_discrepancy_div_scale hm hmTop hcal.count hcal.cover hcal.variance
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

theorem tendsto_sparseFamily_orthantError_div_rate {B : ℕ → ℝ} {m : ℕ → ℕ} {q : ℝ} [∀ n, NeZero (m n)]
    (hq : 2 < q) (hB : ∀ n, 2 ≤ B n) (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hK : Tendsto (fun n => sparseMomentK n (m n) q (B n)) atTop atTop)
    (hLog : Tendsto (fun n => Real.log (sparseMomentK n (m n) q (B n))/dimensionLog (m n*m n)) atTop (𝓝 0))
    (hrate : Tendsto (fun n : ℕ => sparseMomentLowerRate n (m n) q (B n)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      rectangleError (familyArrayLaw (sparseFamilyParameters q n (m n) (B n)) n (m n))
        (sumVector (familyNormalizedObservations (sparseFamilyParameters q n (m n) (B n))))
        (familyGaussianSquareFactor (sparseFamilyParameters q n (m n) (B n)) (m n))
        (familyOrthant (m n*m n) ((sparseFamilyParameters q n (m n) (B n)).scale*normalMaxThreshold (m n))) /
        sparseMomentLowerRate n (m n) q (B n)) atTop (𝓝 (sparseMomentLowerConstant q)) := by
  have hh := (continuous_abs.tendsto (-(sparseMomentLowerConstant q))).comp
    (tendsto_sparseFamily_discrepancy_div_rate hq hB hm hmTop hK hLog hrate)
  rw [abs_neg, abs_of_pos (sparseMomentLowerConstant_pos q)] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  dsimp only [Function.comp_apply]
  rw [familyShiftedCDFDifference_rectangleError _ _ _ _ (familyGaussianSquareFactor_gram _ _),
    abs_div, abs_of_pos (sparseMomentLowerRate_pos hn (hm n) (hB n))]

theorem sparseFamily_distance_ereal_liminf {B : ℕ → ℝ} {m : ℕ → ℕ} {q : ℝ} [∀ n, NeZero (m n)]
    (hq : 2 < q) (hB : ∀ n, 2 ≤ B n) (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hK : Tendsto (fun n => sparseMomentK n (m n) q (B n)) atTop atTop)
    (hLog : Tendsto (fun n => Real.log (sparseMomentK n (m n) q (B n))/dimensionLog (m n*m n)) atTop (𝓝 0))
    (hrate : Tendsto (fun n : ℕ => sparseMomentLowerRate n (m n) q (B n)) atTop (𝓝 0)) :
    ((sparseMomentLowerConstant q : ℝ) : EReal) ≤
      liminf (fun n : ℕ => ((familyComparisonDistance (sparseFamilyParameters q n (m n) (B n)) n (m n) /
        sparseMomentLowerRate n (m n) q (B n) : ℝ) : EReal)) atTop := by
  have hlim := continuous_coe_real_ereal.continuousAt.tendsto.comp
    (tendsto_sparseFamily_orthantError_div_rate hq hB hm hmTop hK hLog hrate)
  have hmono : ∀ᶠ n : ℕ in atTop,
      ((rectangleError (familyArrayLaw (sparseFamilyParameters q n (m n) (B n)) n (m n))
        (sumVector (familyNormalizedObservations (sparseFamilyParameters q n (m n) (B n))))
        (familyGaussianSquareFactor (sparseFamilyParameters q n (m n) (B n)) (m n))
        (familyOrthant (m n*m n) ((sparseFamilyParameters q n (m n) (B n)).scale*normalMaxThreshold (m n))) /
        sparseMomentLowerRate n (m n) q (B n) : ℝ) : EReal) ≤
      ((familyComparisonDistance (sparseFamilyParameters q n (m n) (B n)) n (m n) /
        sparseMomentLowerRate n (m n) q (B n) : ℝ) : EReal) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact_mod_cast div_le_div_of_nonneg_right (rectangleError_le_rectangleDistance _ _ _ _)
      (sparseMomentLowerRate_pos hn (hm n) (hB n)).le
  have hh := liminf_le_liminf hmono
  have hEq := hlim.liminf_eq
  simp only [Function.comp_def] at hEq
  rw [hEq] at hh
  exact hh

structure SparseMomentLowerConstruction (q : ℝ) (B : ℕ → ℝ) (m : ℕ → ℕ) : Prop where
  properties : ∀ᶠ n : ℕ in atTop, CommonSymmetricFamilyProperties (sparseFamilyParameters q n (m n) (B n)) n (m n)
  polynomialClass : ∀ᶠ n : ℕ in atTop,
    PolynomialIndependentHypotheses (familyArrayLaw (sparseFamilyParameters q n (m n) (B n)) n (m n))
      (familyRawObservations (sparseFamilyParameters q n (m n) (B n))) q (B n)
  matchingGaussianCovariance : ∀ᶠ n : ℕ in atTop,
    familyGaussianSquareFactor (sparseFamilyParameters q n (m n) (B n)) (m n) *
      (familyGaussianSquareFactor (sparseFamilyParameters q n (m n) (B n)) (m n)).transpose =
    covariance (familyArrayLaw (sparseFamilyParameters q n (m n) (B n)) n (m n))
      (sumVector (familyNormalizedObservations (sparseFamilyParameters q n (m n) (B n))))
  orthantLimit : Tendsto (fun n : ℕ =>
    rectangleError (familyArrayLaw (sparseFamilyParameters q n (m n) (B n)) n (m n))
      (sumVector (familyNormalizedObservations (sparseFamilyParameters q n (m n) (B n))))
      (familyGaussianSquareFactor (sparseFamilyParameters q n (m n) (B n)) (m n))
      (familyOrthant (m n*m n) ((sparseFamilyParameters q n (m n) (B n)).scale*normalMaxThreshold (m n))) /
      sparseMomentLowerRate n (m n) q (B n)) atTop (𝓝 (sparseMomentLowerConstant q))
  positiveConstant : 0 < sparseMomentLowerConstant q
  distanceLiminf : ((sparseMomentLowerConstant q : ℝ) : EReal) ≤
    liminf (fun n : ℕ => ((familyComparisonDistance (sparseFamilyParameters q n (m n) (B n)) n (m n) /
      sparseMomentLowerRate n (m n) q (B n) : ℝ) : EReal)) atTop

theorem sparseMomentLower_of_two_le {B : ℕ → ℝ} {m : ℕ → ℕ} {q : ℝ}
    (hq : 2 < q) (hB : ∀ n, 2 ≤ B n) (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hK : Tendsto (fun n => sparseMomentK n (m n) q (B n)) atTop atTop)
    (hLog : Tendsto (fun n => Real.log (sparseMomentK n (m n) q (B n))/dimensionLog (m n*m n)) atTop (𝓝 0))
    (hrate : Tendsto (fun n : ℕ => sparseMomentLowerRate n (m n) q (B n)) atTop (𝓝 0)) :
    SparseMomentLowerConstruction q B m := by
  letI : ∀ n, NeZero (m n) := fun n => ⟨by have := hm n; omega⟩
  have hprops : ∀ᶠ n : ℕ in atTop, CommonSymmetricFamilyProperties (sparseFamilyParameters q n (m n) (B n)) n (m n) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact symmetricFamilyProperties _ hn (hm n)
  have hPaper := sparsePaperCalibration hq hB hm hmTop hK hLog hrate
  refine ⟨hprops, hPaper.polynomialClass, ?_,
    tendsto_sparseFamily_orthantError_div_rate hq hB hm hmTop hK hLog hrate,
    sparseMomentLowerConstant_pos q, sparseFamily_distance_ereal_liminf hq hB hm hmTop hK hLog hrate⟩
  filter_upwards [hprops] with n hn
  rw [familyGaussianSquareFactor_gram, hn.sumCovariance]

/-- The actual sparse model under the paper's literal hypotheses. -/
theorem sparseMomentLower {B : ℕ → ℝ} {m : ℕ → ℕ} {q : ℝ}
    (hq : 2 < q) (hB : ∀ n, 2 ≤ B n) (hmTop : Tendsto m atTop atTop)
    (hK : Tendsto (fun n => sparseMomentK n (m n) q (B n)) atTop atTop)
    (hLog : Tendsto (fun n => Real.log (sparseMomentK n (m n) q (B n))/dimensionLog (m n*m n)) atTop (𝓝 0))
    (hrate : Tendsto (fun n => sparseMomentLowerRate n (m n) q (B n)) atTop (𝓝 0)) :
    SparseMomentLowerConstruction q B m := by
  let m' := fun n => max 2 (m n)
  have heq : ∀ᶠ n : ℕ in atTop, max 2 (m n) = m n := by
    filter_upwards [hmTop.eventually (eventually_ge_atTop 2)] with n hn
    exact max_eq_right hn
  have hm'Top : Tendsto m' atTop atTop := tendsto_atTop_mono (fun n => le_max_right 2 (m n)) hmTop
  have hK' : Tendsto (fun n => sparseMomentK n (m' n) q (B n)) atTop atTop := by
    apply hK.congr'
    filter_upwards [heq] with n hn
    dsimp only [m']
    rw [hn]
  have hLog' : Tendsto (fun n => Real.log (sparseMomentK n (m' n) q (B n))/dimensionLog (m' n*m' n)) atTop (𝓝 0) := by
    apply hLog.congr'
    filter_upwards [heq] with n hn
    dsimp only [m']
    rw [hn]
  have hr' : Tendsto (fun n => sparseMomentLowerRate n (m' n) q (B n)) atTop (𝓝 0) := by
    apply hrate.congr'
    filter_upwards [heq] with n hn
    dsimp only [m']
    rw [hn]
  have h := sparseMomentLower_of_two_le hq hB (fun n => le_max_left 2 (m n)) hm'Top hK' hLog' hr'
  refine ⟨?_, ?_, ?_, ?_, h.positiveConstant, ?_⟩
  · filter_upwards [h.properties, heq] with n hn he
    exact he ▸ hn
  · filter_upwards [h.polynomialClass, heq] with n hn he
    exact he ▸ hn
  · filter_upwards [h.matchingGaussianCovariance, heq] with n hn he
    exact he ▸ hn
  · apply h.orthantLimit.congr'
    filter_upwards [heq] with n hn
    rw [hn]
  · apply h.distanceLiminf.trans_eq
    apply liminf_congr
    filter_upwards [heq] with n hn
    rw [hn]

end
end RectangleCLT.Companion.SplitV4
