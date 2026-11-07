import RectangleCLTCompanion.SplitV4.DenseMomentCalibration
import RectangleCLTCompanion.SplitV4.FourthMomentLower

/-! The genuine fixed-envelope q>4 lower construction and its actual detecting orthant. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology
namespace RectangleCLT.Companion.SplitV4
noncomputable section

theorem denseMomentLowerRate_pos {n m : ℕ} {q B : ℝ} (hn : 1 ≤ n) (hm : 2 ≤ m) (hB : 2 ≤ B) :
    0 < denseMomentLowerRate n m q B := by
  rw [denseMomentLowerRate_eq n m hm q B]
  exact denseLowerEnvelopeRate_pos (by omega) (Real.log_pos (by exact_mod_cast hm)) (by linarith)

theorem tendsto_denseFamily_discrepancy_div_rate {m : ℕ → ℕ} [∀ n, NeZero (m n)] {q B : ℝ}
    (hq : 4 < q) (hB : 2 ≤ B) (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hrate : Tendsto (fun n : ℕ => denseMomentLowerRate n (m n) q B) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => familyShiftedCDFDifference (denseFamilyParameters q B n (m n)) n (m n)
      (normalMaxThreshold (m n))/denseMomentLowerRate n (m n) q B) atTop
      (𝓝 (denseLowerConstant q B)) := by
  have hcal := denseFamilyCalibration hq hB hm hmTop hrate
  have hπ : ∀ᶠ n : ℕ in atTop,
      (denseFamilyParameters q B n (m n)).pi = (boundedFamilyParameters n (m n)).pi :=
    Eventually.of_forall (fun n => by rw [denseFamilyParameters_pi, boundedFamilyParameters_pi])
  have hlim := tendsto_amplifiedFamily_discrepancy_div_scale hm hmTop hcal.small hcal.thetaMatch hπ
    hcal.amplificationLarge hcal.amplificationSmall
  have hh := hlim.div hcal.rateRatio ((denseLowerRateConversion_pos hB).ne')
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  dsimp only [Pi.div_apply]
  exact discrepancy_rate_quotient (amplifiedSymmetricLowerScale_pos _ hn (hm n)).ne'
    (denseMomentLowerRate_pos hn (hm n) hB).ne'

theorem tendsto_denseFamily_orthantError_div_rate {m : ℕ → ℕ} [∀ n, NeZero (m n)] {q B : ℝ}
    (hq : 4 < q) (hB : 2 ≤ B) (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hrate : Tendsto (fun n : ℕ => denseMomentLowerRate n (m n) q B) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      rectangleError (familyArrayLaw (denseFamilyParameters q B n (m n)) n (m n))
        (sumVector (familyNormalizedObservations (denseFamilyParameters q B n (m n))))
        (familyGaussianSquareFactor (denseFamilyParameters q B n (m n)) (m n))
        (familyOrthant (m n*m n) ((denseFamilyParameters q B n (m n)).scale*normalMaxThreshold (m n))) /
        denseMomentLowerRate n (m n) q B) atTop (𝓝 (denseLowerConstant q B)) := by
  have hh := (continuous_abs.tendsto (denseLowerConstant q B)).comp
    (tendsto_denseFamily_discrepancy_div_rate hq hB hm hmTop hrate)
  rw [abs_of_pos (denseLowerConstant_pos hB)] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  dsimp only [Function.comp_apply]
  rw [familyShiftedCDFDifference_rectangleError _ _ _ _ (familyGaussianSquareFactor_gram _ _),
    abs_div, abs_of_pos (denseMomentLowerRate_pos hn (hm n) hB)]

theorem denseFamily_distance_ereal_liminf {m : ℕ → ℕ} [∀ n, NeZero (m n)] {q B : ℝ}
    (hq : 4 < q) (hB : 2 ≤ B) (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hrate : Tendsto (fun n : ℕ => denseMomentLowerRate n (m n) q B) atTop (𝓝 0)) :
    ((denseLowerConstant q B : ℝ) : EReal) ≤
      liminf (fun n : ℕ =>
        ((familyComparisonDistance (denseFamilyParameters q B n (m n)) n (m n) /
          denseMomentLowerRate n (m n) q B : ℝ) : EReal)) atTop := by
  have hlim := continuous_coe_real_ereal.continuousAt.tendsto.comp
    (tendsto_denseFamily_discrepancy_div_rate hq hB hm hmTop hrate)
  have hmono : ∀ᶠ n : ℕ in atTop,
      ((familyShiftedCDFDifference (denseFamilyParameters q B n (m n)) n (m n)
        (normalMaxThreshold (m n))/denseMomentLowerRate n (m n) q B : ℝ) : EReal) ≤
      ((familyComparisonDistance (denseFamilyParameters q B n (m n)) n (m n) /
        denseMomentLowerRate n (m n) q B : ℝ) : EReal) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact_mod_cast div_le_div_of_nonneg_right
      (familyShiftedCDFDifference_le_distance _ _ _ _) (denseMomentLowerRate_pos hn (hm n) hB).le
  have hh := liminf_le_liminf hmono
  have hEq := hlim.liminf_eq
  simp only [Function.comp_def] at hEq
  rw [hEq] at hh
  exact hh

structure DenseMomentLowerConstruction (q B : ℝ) (m : ℕ → ℕ) : Prop where
  properties : ∀ᶠ n : ℕ in atTop,
    CommonSymmetricFamilyProperties (denseFamilyParameters q B n (m n)) n (m n)
  polynomialClass : ∀ᶠ n : ℕ in atTop,
    PolynomialIndependentHypotheses (familyArrayLaw (denseFamilyParameters q B n (m n)) n (m n))
      (familyRawObservations (denseFamilyParameters q B n (m n))) q B
  matchingGaussianCovariance : ∀ᶠ n : ℕ in atTop,
    familyGaussianSquareFactor (denseFamilyParameters q B n (m n)) (m n) *
      (familyGaussianSquareFactor (denseFamilyParameters q B n (m n)) (m n)).transpose =
    covariance (familyArrayLaw (denseFamilyParameters q B n (m n)) n (m n))
      (sumVector (familyNormalizedObservations (denseFamilyParameters q B n (m n))))
  orthantLimit : Tendsto (fun n : ℕ =>
    rectangleError (familyArrayLaw (denseFamilyParameters q B n (m n)) n (m n))
      (sumVector (familyNormalizedObservations (denseFamilyParameters q B n (m n))))
      (familyGaussianSquareFactor (denseFamilyParameters q B n (m n)) (m n))
      (familyOrthant (m n*m n) ((denseFamilyParameters q B n (m n)).scale*normalMaxThreshold (m n))) /
      denseMomentLowerRate n (m n) q B) atTop (𝓝 (denseLowerConstant q B))
  positiveConstant : 0 < denseLowerConstant q B
  distanceLiminf : ((denseLowerConstant q B : ℝ) : EReal) ≤
    liminf (fun n : ℕ =>
      ((familyComparisonDistance (denseFamilyParameters q B n (m n)) n (m n) /
        denseMomentLowerRate n (m n) q B : ℝ) : EReal)) atTop

theorem denseMomentLower_of_two_le {m : ℕ → ℕ} {q B : ℝ} (hq : 4 < q) (hB : 2 ≤ B) (hm : ∀ n, 2 ≤ m n)
    (hmTop : Tendsto m atTop atTop)
    (hrate : Tendsto (fun n : ℕ => denseMomentLowerRate n (m n) q B) atTop (𝓝 0)) :
    DenseMomentLowerConstruction q B m := by
  letI : ∀ n, NeZero (m n) := fun n => ⟨by have := hm n; omega⟩
  have hprops : ∀ᶠ n : ℕ in atTop,
      CommonSymmetricFamilyProperties (denseFamilyParameters q B n (m n)) n (m n) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact symmetricFamilyProperties _ hn (hm n)
  refine ⟨hprops, ?_, ?_, tendsto_denseFamily_orthantError_div_rate hq hB hm hmTop hrate,
    denseLowerConstant_pos hB, denseFamily_distance_ereal_liminf hq hB hm hmTop hrate⟩
  · exact eventually_denseFamily_polynomialIndependent hq hB hm hmTop hrate
  · filter_upwards [hprops] with n hn
    rw [familyGaussianSquareFactor_gram, hn.sumCovariance]

/-- The fixed-envelope q>4 lower construction under the literal dimension
sequence assumptions; no lower bound on finitely many initial dimensions is imposed. -/
theorem denseMomentLower {m : ℕ → ℕ} {q B : ℝ} (hq : 4 < q) (hB : 2 ≤ B) (hmTop : Tendsto m atTop atTop)
    (hrate : Tendsto (fun n : ℕ => denseMomentLowerRate n (m n) q B) atTop (𝓝 0)) :
    DenseMomentLowerConstruction q B m := by
  let m' := fun n => max 2 (m n)
  have heq : ∀ᶠ n : ℕ in atTop, max 2 (m n) = m n := by
    filter_upwards [hmTop.eventually (eventually_ge_atTop 2)] with n hn
    exact max_eq_right hn
  have hm'Top : Tendsto m' atTop atTop := tendsto_atTop_mono (fun n => le_max_right 2 (m n)) hmTop
  have hr' : Tendsto (fun n : ℕ => denseMomentLowerRate n (m' n) q B) atTop (𝓝 0) := by
    apply hrate.congr'
    filter_upwards [heq] with n hn
    dsimp only [m']
    rw [hn]
  have h := denseMomentLower_of_two_le hq hB (fun n => le_max_left 2 (m n)) hm'Top hr'
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
