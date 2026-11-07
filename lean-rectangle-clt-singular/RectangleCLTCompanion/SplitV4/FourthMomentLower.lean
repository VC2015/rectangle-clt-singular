import RectangleCLTCompanion.SplitV4.FourthMomentCalibration

/-! The genuine fourth-moment lower construction and its actual detecting orthant. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology
namespace RectangleCLT.Companion.SplitV4
noncomputable section

theorem fourthMomentLowerRate_pos {n m : ℕ} (hn : 1 ≤ n) (hm : 2 ≤ m) :
    0 < fourthMomentLowerRate n m := by
  rw [fourthMomentLowerRate_eq n m hm]
  exact fourthLowerRate_pos (by omega) (Real.log_pos (by exact_mod_cast hm))

theorem fourth_lower_constant_identity :
    (Real.sqrt 2*Real.exp (-1))/4 = 1/(2*Real.sqrt 2*Real.exp 1) := by
  rw [Real.exp_neg]
  field_simp [(Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne', (Real.exp_pos 1).ne']
  calc
    Real.sqrt 2*(2*Real.sqrt 2*Real.exp 1) = 2*(Real.sqrt 2)^2*Real.exp 1 := by ring
    _ = Real.exp 1*4 := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; ring

theorem discrepancy_rate_quotient {d r s : ℝ} (hs : s ≠ 0) (hr : r ≠ 0) :
    (d/s)/(r/s) = d/r := by
  field_simp

theorem tendsto_fourthFamily_discrepancy_div_rate {m : ℕ → ℕ} [∀ n, NeZero (m n)]
    (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hrate : Tendsto (fun n : ℕ => fourthMomentLowerRate n (m n)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => familyShiftedCDFDifference (fourthFamilyParameters n (m n)) n (m n)
      (normalMaxThreshold (m n))/fourthMomentLowerRate n (m n)) atTop
      (𝓝 (1/(2*Real.sqrt 2*Real.exp 1))) := by
  have hcal := fourthFamilyCalibration hm hmTop hrate
  have hπ : ∀ᶠ n : ℕ in atTop,
      (fourthFamilyParameters n (m n)).pi = (boundedFamilyParameters n (m n)).pi :=
    Eventually.of_forall (fun n => by rw [fourthFamilyParameters_pi, boundedFamilyParameters_pi])
  have hlim := tendsto_amplifiedFamily_discrepancy_div_scale hm hmTop hcal.small hcal.thetaMatch hπ
    hcal.amplificationLarge hcal.amplificationSmall
  have hh := hlim.div hcal.rateRatio (by norm_num : (4 : ℝ) ≠ 0)
  rw [fourth_lower_constant_identity] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  dsimp only [Pi.div_apply]
  exact discrepancy_rate_quotient (amplifiedSymmetricLowerScale_pos _ hn (hm n)).ne'
    (fourthMomentLowerRate_pos hn (hm n)).ne'

theorem tendsto_fourthFamily_orthantError_div_rate {m : ℕ → ℕ} [∀ n, NeZero (m n)]
    (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hrate : Tendsto (fun n : ℕ => fourthMomentLowerRate n (m n)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      rectangleError (familyArrayLaw (fourthFamilyParameters n (m n)) n (m n))
        (sumVector (familyNormalizedObservations (fourthFamilyParameters n (m n))))
        (familyGaussianSquareFactor (fourthFamilyParameters n (m n)) (m n))
        (familyOrthant (m n*m n) ((fourthFamilyParameters n (m n)).scale*normalMaxThreshold (m n))) /
        fourthMomentLowerRate n (m n)) atTop (𝓝 (1/(2*Real.sqrt 2*Real.exp 1))) := by
  have hh := (continuous_abs.tendsto (1/(2*Real.sqrt 2*Real.exp 1))).comp
    (tendsto_fourthFamily_discrepancy_div_rate hm hmTop hrate)
  rw [abs_of_pos (by positivity : (0 : ℝ) < 1/(2*Real.sqrt 2*Real.exp 1))] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  dsimp only [Function.comp_apply]
  rw [familyShiftedCDFDifference_rectangleError _ _ _ _ (familyGaussianSquareFactor_gram _ _),
    abs_div, abs_of_pos (fourthMomentLowerRate_pos hn (hm n))]

theorem fourthFamily_distance_ereal_liminf {m : ℕ → ℕ} [∀ n, NeZero (m n)]
    (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hrate : Tendsto (fun n : ℕ => fourthMomentLowerRate n (m n)) atTop (𝓝 0)) :
    ((1/(2*Real.sqrt 2*Real.exp 1) : ℝ) : EReal) ≤
      liminf (fun n : ℕ =>
        ((familyComparisonDistance (fourthFamilyParameters n (m n)) n (m n) /
          fourthMomentLowerRate n (m n) : ℝ) : EReal)) atTop := by
  have hlim := continuous_coe_real_ereal.continuousAt.tendsto.comp
    (tendsto_fourthFamily_discrepancy_div_rate hm hmTop hrate)
  have hmono : ∀ᶠ n : ℕ in atTop,
      ((familyShiftedCDFDifference (fourthFamilyParameters n (m n)) n (m n)
        (normalMaxThreshold (m n))/fourthMomentLowerRate n (m n) : ℝ) : EReal) ≤
      ((familyComparisonDistance (fourthFamilyParameters n (m n)) n (m n) /
        fourthMomentLowerRate n (m n) : ℝ) : EReal) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact_mod_cast div_le_div_of_nonneg_right
      (familyShiftedCDFDifference_le_distance _ _ _ _) (fourthMomentLowerRate_pos hn (hm n)).le
  have hh := liminf_le_liminf hmono
  have hEq := hlim.liminf_eq
  simp only [Function.comp_def] at hEq
  rw [hEq] at hh
  exact hh

structure FourthMomentLowerConstruction (m : ℕ → ℕ) : Prop where
  properties : ∀ᶠ n : ℕ in atTop,
    CommonSymmetricFamilyProperties (fourthFamilyParameters n (m n)) n (m n)
  polynomialClass : ∀ᶠ n : ℕ in atTop,
    PolynomialIndependentHypotheses (familyArrayLaw (fourthFamilyParameters n (m n)) n (m n))
      (familyRawObservations (fourthFamilyParameters n (m n))) 4 2
  matchingGaussianCovariance : ∀ᶠ n : ℕ in atTop,
    familyGaussianSquareFactor (fourthFamilyParameters n (m n)) (m n) *
      (familyGaussianSquareFactor (fourthFamilyParameters n (m n)) (m n)).transpose =
    covariance (familyArrayLaw (fourthFamilyParameters n (m n)) n (m n))
      (sumVector (familyNormalizedObservations (fourthFamilyParameters n (m n))))
  orthantLimit : Tendsto (fun n : ℕ =>
    rectangleError (familyArrayLaw (fourthFamilyParameters n (m n)) n (m n))
      (sumVector (familyNormalizedObservations (fourthFamilyParameters n (m n))))
      (familyGaussianSquareFactor (fourthFamilyParameters n (m n)) (m n))
      (familyOrthant (m n*m n) ((fourthFamilyParameters n (m n)).scale*normalMaxThreshold (m n))) /
      fourthMomentLowerRate n (m n)) atTop (𝓝 (1/(2*Real.sqrt 2*Real.exp 1)))
  distanceLiminf : ((1/(2*Real.sqrt 2*Real.exp 1) : ℝ) : EReal) ≤
    liminf (fun n : ℕ =>
      ((familyComparisonDistance (fourthFamilyParameters n (m n)) n (m n) /
        fourthMomentLowerRate n (m n) : ℝ) : EReal)) atTop

theorem fourthMomentLower_of_two_le {m : ℕ → ℕ} (hm : ∀ n, 2 ≤ m n)
    (hmTop : Tendsto m atTop atTop)
    (hrate : Tendsto (fun n : ℕ => fourthMomentLowerRate n (m n)) atTop (𝓝 0)) :
    FourthMomentLowerConstruction m := by
  letI : ∀ n, NeZero (m n) := fun n => ⟨by have := hm n; omega⟩
  have hprops : ∀ᶠ n : ℕ in atTop,
      CommonSymmetricFamilyProperties (fourthFamilyParameters n (m n)) n (m n) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact symmetricFamilyProperties _ hn (hm n)
  refine ⟨hprops, ?_, ?_, tendsto_fourthFamily_orthantError_div_rate hm hmTop hrate,
    fourthFamily_distance_ereal_liminf hm hmTop hrate⟩
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact fourthFamily_polynomialIndependent hn
  · filter_upwards [hprops] with n hn
    rw [familyGaussianSquareFactor_gram, hn.sumCovariance]

/-- The fourth-moment lower construction under the literal dimension
sequence assumptions; no lower bound on finitely many initial dimensions is imposed. -/
theorem fourthMomentLower {m : ℕ → ℕ} (hmTop : Tendsto m atTop atTop)
    (hrate : Tendsto (fun n : ℕ => fourthMomentLowerRate n (m n)) atTop (𝓝 0)) :
    FourthMomentLowerConstruction m := by
  let m' := fun n => max 2 (m n)
  have heq : ∀ᶠ n : ℕ in atTop, max 2 (m n) = m n := by
    filter_upwards [hmTop.eventually (eventually_ge_atTop 2)] with n hn
    exact max_eq_right hn
  have hm'Top : Tendsto m' atTop atTop := tendsto_atTop_mono (fun n => le_max_right 2 (m n)) hmTop
  have hr' : Tendsto (fun n : ℕ => fourthMomentLowerRate n (m' n)) atTop (𝓝 0) := by
    apply hrate.congr'
    filter_upwards [heq] with n hn
    dsimp only [m']
    rw [hn]
  have h := fourthMomentLower_of_two_le (fun n => le_max_left 2 (m n)) hm'Top hr'
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
