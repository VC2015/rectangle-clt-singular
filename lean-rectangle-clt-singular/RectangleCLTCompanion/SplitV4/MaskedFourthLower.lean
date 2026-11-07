import RectangleCLTCompanion.SplitV4.MaskedFourthCalibration
import RectangleCLTCompanion.SplitV4.FourthMomentLower

/-! The actual growing fourth-moment envelope lower construction (Theorem 6). -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology
namespace RectangleCLT.Companion.SplitV4
noncomputable section

theorem maskedFourthMomentLowerRate_pos {n m : ℕ} {B : ℝ} (hn : 1 ≤ n) (hm : 2 ≤ m) (hB : 2 ≤ B) :
    0 < maskedFourthMomentLowerRate n m B := by
  unfold maskedFourthMomentLowerRate
  rw [maskedFourth_rate_conversion (by omega) (Real.log_pos (by exact_mod_cast hm)) hB]
  exact mul_pos (by positivity) (maskedFourthScale_pos (by omega) (Real.log_pos (by exact_mod_cast hm)) hB)

theorem masked_fourth_lower_constant_identity :
    (-Real.sqrt 2*Real.exp (-1))/(4*Real.sqrt 2) = -(1/(4*Real.exp 1)) := by
  rw [Real.exp_neg]
  field_simp [(Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne', (Real.exp_pos 1).ne']
  ring

theorem tendsto_maskedFourthFamily_discrepancy_div_rate {B : ℕ → ℝ} {m : ℕ → ℕ} [∀ n, NeZero (m n)]
    (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop) (hBTop : Tendsto B atTop atTop)
    (hΛ : Tendsto (fun n : ℕ => maskedFourthLog (B n)/Real.log (m n : ℝ)) atTop (𝓝 0))
    (hrate : Tendsto (fun n : ℕ => maskedFourthMomentLowerRate n (m n) (B n)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => familyShiftedCDFDifference (maskedFourthFamilyParameters n (m n) (B n)) n (m n)
      (normalMaxThreshold (m n))/maskedFourthMomentLowerRate n (m n) (B n)) atTop (𝓝 (-(1/(4*Real.exp 1)))) := by
  have hcal := maskedFourthFamilyCalibration hm hmTop hBTop hΛ hrate
  have hlim := tendsto_familyRare_discrepancy_div_scale hm hmTop hcal.count hcal.cover hcal.variance
    hcal.coefficient hcal.small hcal.scale hcal.countCost hcal.gaussianCost
  have hh := hlim.div hcal.rateRatio (by positivity : (4*Real.sqrt 2 : ℝ) ≠ 0)
  rw [masked_fourth_lower_constant_identity] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1, hBTop.eventually (eventually_ge_atTop 2)] with n hn hnB
  dsimp only [Pi.div_apply]
  exact discrepancy_rate_quotient (familyRareLowerScale_pos _ hn (hm n)).ne'
    (maskedFourthMomentLowerRate_pos hn (hm n) hnB).ne'

theorem tendsto_maskedFourthFamily_orthantError_div_rate {B : ℕ → ℝ} {m : ℕ → ℕ} [∀ n, NeZero (m n)]
    (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop) (hBTop : Tendsto B atTop atTop)
    (hΛ : Tendsto (fun n : ℕ => maskedFourthLog (B n)/Real.log (m n : ℝ)) atTop (𝓝 0))
    (hrate : Tendsto (fun n : ℕ => maskedFourthMomentLowerRate n (m n) (B n)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      rectangleError (familyArrayLaw (maskedFourthFamilyParameters n (m n) (B n)) n (m n))
        (sumVector (familyNormalizedObservations (maskedFourthFamilyParameters n (m n) (B n))))
        (familyGaussianSquareFactor (maskedFourthFamilyParameters n (m n) (B n)) (m n))
        (familyOrthant (m n*m n) ((maskedFourthFamilyParameters n (m n) (B n)).scale*normalMaxThreshold (m n))) /
        maskedFourthMomentLowerRate n (m n) (B n)) atTop (𝓝 (1/(4*Real.exp 1))) := by
  have hh := (continuous_abs.tendsto (-(1/(4*Real.exp 1)))).comp
    (tendsto_maskedFourthFamily_discrepancy_div_rate hm hmTop hBTop hΛ hrate)
  rw [abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 1/(4*Real.exp 1))] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1, hBTop.eventually (eventually_ge_atTop 2)] with n hn hnB
  dsimp only [Function.comp_apply]
  rw [familyShiftedCDFDifference_rectangleError _ _ _ _ (familyGaussianSquareFactor_gram _ _),
    abs_div, abs_of_pos (maskedFourthMomentLowerRate_pos hn (hm n) hnB)]

theorem maskedFourthFamily_distance_ereal_liminf {B : ℕ → ℝ} {m : ℕ → ℕ} [∀ n, NeZero (m n)]
    (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop) (hBTop : Tendsto B atTop atTop)
    (hΛ : Tendsto (fun n : ℕ => maskedFourthLog (B n)/Real.log (m n : ℝ)) atTop (𝓝 0))
    (hrate : Tendsto (fun n : ℕ => maskedFourthMomentLowerRate n (m n) (B n)) atTop (𝓝 0)) :
    ((1/(4*Real.exp 1) : ℝ) : EReal) ≤
      liminf (fun n : ℕ => ((familyComparisonDistance (maskedFourthFamilyParameters n (m n) (B n)) n (m n) /
        maskedFourthMomentLowerRate n (m n) (B n) : ℝ) : EReal)) atTop := by
  have hlim := continuous_coe_real_ereal.continuousAt.tendsto.comp
    (tendsto_maskedFourthFamily_orthantError_div_rate hm hmTop hBTop hΛ hrate)
  have hmono : ∀ᶠ n : ℕ in atTop,
      ((rectangleError (familyArrayLaw (maskedFourthFamilyParameters n (m n) (B n)) n (m n))
        (sumVector (familyNormalizedObservations (maskedFourthFamilyParameters n (m n) (B n))))
        (familyGaussianSquareFactor (maskedFourthFamilyParameters n (m n) (B n)) (m n))
        (familyOrthant (m n*m n) ((maskedFourthFamilyParameters n (m n) (B n)).scale*normalMaxThreshold (m n))) /
        maskedFourthMomentLowerRate n (m n) (B n) : ℝ) : EReal) ≤
      ((familyComparisonDistance (maskedFourthFamilyParameters n (m n) (B n)) n (m n) /
        maskedFourthMomentLowerRate n (m n) (B n) : ℝ) : EReal) := by
    filter_upwards [eventually_ge_atTop 1, hBTop.eventually (eventually_ge_atTop 2)] with n hn hnB
    exact_mod_cast div_le_div_of_nonneg_right (rectangleError_le_rectangleDistance _ _ _ _)
      (maskedFourthMomentLowerRate_pos hn (hm n) hnB).le
  have hh := liminf_le_liminf hmono
  have hEq := hlim.liminf_eq
  simp only [Function.comp_def] at hEq
  rw [hEq] at hh
  exact hh

structure MaskedFourthLowerConstruction (B : ℕ → ℝ) (m : ℕ → ℕ) : Prop where
  properties : ∀ᶠ n : ℕ in atTop, CommonSymmetricFamilyProperties (maskedFourthFamilyParameters n (m n) (B n)) n (m n)
  polynomialClass : ∀ᶠ n : ℕ in atTop,
    PolynomialIndependentHypotheses (familyArrayLaw (maskedFourthFamilyParameters n (m n) (B n)) n (m n))
      (familyRawObservations (maskedFourthFamilyParameters n (m n) (B n))) 4 (B n)
  matchingGaussianCovariance : ∀ᶠ n : ℕ in atTop,
    familyGaussianSquareFactor (maskedFourthFamilyParameters n (m n) (B n)) (m n) *
      (familyGaussianSquareFactor (maskedFourthFamilyParameters n (m n) (B n)) (m n)).transpose =
    covariance (familyArrayLaw (maskedFourthFamilyParameters n (m n) (B n)) n (m n))
      (sumVector (familyNormalizedObservations (maskedFourthFamilyParameters n (m n) (B n))))
  orthantLimit : Tendsto (fun n : ℕ =>
    rectangleError (familyArrayLaw (maskedFourthFamilyParameters n (m n) (B n)) n (m n))
      (sumVector (familyNormalizedObservations (maskedFourthFamilyParameters n (m n) (B n))))
      (familyGaussianSquareFactor (maskedFourthFamilyParameters n (m n) (B n)) (m n))
      (familyOrthant (m n*m n) ((maskedFourthFamilyParameters n (m n) (B n)).scale*normalMaxThreshold (m n))) /
      maskedFourthMomentLowerRate n (m n) (B n)) atTop (𝓝 (1/(4*Real.exp 1)))
  distanceLiminf : ((1/(4*Real.exp 1) : ℝ) : EReal) ≤
    liminf (fun n : ℕ => ((familyComparisonDistance (maskedFourthFamilyParameters n (m n) (B n)) n (m n) /
      maskedFourthMomentLowerRate n (m n) (B n) : ℝ) : EReal)) atTop

theorem maskedFourthLower_of_two_le {B : ℕ → ℝ} {m : ℕ → ℕ}
    (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop) (hBTop : Tendsto B atTop atTop)
    (hΛ : Tendsto (fun n : ℕ => maskedFourthLog (B n)/Real.log (m n : ℝ)) atTop (𝓝 0))
    (hrate : Tendsto (fun n : ℕ => maskedFourthMomentLowerRate n (m n) (B n)) atTop (𝓝 0)) :
    MaskedFourthLowerConstruction B m := by
  letI : ∀ n, NeZero (m n) := fun n => ⟨by have := hm n; omega⟩
  have hprops : ∀ᶠ n : ℕ in atTop, CommonSymmetricFamilyProperties (maskedFourthFamilyParameters n (m n) (B n)) n (m n) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact symmetricFamilyProperties _ hn (hm n)
  refine ⟨hprops, eventually_maskedFourthFamily_polynomialIndependent hmTop hBTop hrate, ?_,
    tendsto_maskedFourthFamily_orthantError_div_rate hm hmTop hBTop hΛ hrate,
    maskedFourthFamily_distance_ereal_liminf hm hmTop hBTop hΛ hrate⟩
  filter_upwards [hprops] with n hn
  rw [familyGaussianSquareFactor_gram, hn.sumCovariance]

/-- Theorem 6 (`opt:q4-growing`) for the genuine masked model. -/
theorem maskedFourthLower {B : ℕ → ℝ} {m : ℕ → ℕ}
    (hmTop : Tendsto m atTop atTop) (hBTop : Tendsto B atTop atTop)
    (hΛ : Tendsto (fun n : ℕ => maskedFourthLog (B n)/Real.log (m n : ℝ)) atTop (𝓝 0))
    (hrate : Tendsto (fun n : ℕ => maskedFourthMomentLowerRate n (m n) (B n)) atTop (𝓝 0)) :
    MaskedFourthLowerConstruction B m := by
  let m' := fun n => max 2 (m n)
  have heq : ∀ᶠ n : ℕ in atTop, max 2 (m n) = m n := by
    filter_upwards [hmTop.eventually (eventually_ge_atTop 2)] with n hn
    exact max_eq_right hn
  have hm'Top : Tendsto m' atTop atTop := tendsto_atTop_mono (fun n => le_max_right 2 (m n)) hmTop
  have hΛ' : Tendsto (fun n : ℕ => maskedFourthLog (B n)/Real.log (m' n : ℝ)) atTop (𝓝 0) := by
    apply hΛ.congr'
    filter_upwards [heq] with n hn
    dsimp only [m']
    rw [hn]
  have hr' : Tendsto (fun n : ℕ => maskedFourthMomentLowerRate n (m' n) (B n)) atTop (𝓝 0) := by
    apply hrate.congr'
    filter_upwards [heq] with n hn
    dsimp only [m']
    rw [hn]
  have h := maskedFourthLower_of_two_le (fun n => le_max_left 2 (m n)) hm'Top hBTop hΛ' hr'
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
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
