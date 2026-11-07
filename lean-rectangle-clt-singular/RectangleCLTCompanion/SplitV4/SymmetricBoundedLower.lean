import RectangleCLTCompanion.SplitV4.SymmetricBoundedRemainder
import RectangleCLTCompanion.SplitV4.SymmetricBoundedRademacher
import RectangleCLTCompanion.SplitV4.SymmetricFamilyOrthant
import RectangleCLTCompanion.SplitV4.SymmetricFamilyCertification
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-! The full bounded centrally symmetric lower bound, with an actual detecting orthant. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology
namespace RectangleCLT.Companion.SplitV4
noncomputable section

def boundedSymmetricLowerRate (n m : ℕ) : ℝ := (2 / Real.sqrt n) * dimensionLog (m * m) ^ (3 / 2 : ℝ)

theorem tendsto_boundedFamily_discrepancy_div_scale {m : ℕ → ℕ} [∀ n, NeZero (m n)]
    (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => Real.log (m n : ℝ) ^ 3 / n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => familyShiftedCDFDifference (boundedFamilyParameters n (m n)) n (m n)
      (normalMaxThreshold (m n)) / boundedLowerScale n (m n)) atTop (𝓝 (Real.sqrt 2 * Real.exp (-1))) := by
  obtain ⟨C, hC, hCB⟩ := eventually_normalMaximumDensity_local_derivative_bound
  have hlog : Tendsto (fun n : ℕ => Real.log (m n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmTop)
  let disc := fun n => familyShiftedCDFDifference (boundedFamilyParameters n (m n)) n (m n) (normalMaxThreshold (m n))
  let lead := fun n => normalMaximumDensity (m n) (normalMaxThreshold (m n)) *
    familyShiftMeanDifference (boundedFamilyParameters n (m n)) n (m n)
  let cost := fun n => localShiftComparisonCost (C*Real.log (m n : ℝ))
    (1/Real.sqrt (Real.log (m n : ℝ))) (normalMaximumDensity (m n) (normalMaxThreshold (m n)))
  have hlead := tendsto_boundedFamily_leading_comparison_ratio hm hmTop hsmall
  have hE := (tendsto_rademacherLocalError_div_boundedLowerScale hmTop hsmall).const_mul (8*Real.exp 4)
  have hR := tendsto_boundedFamily_local_shift_remainder_ratio C hC.le hm hmTop hsmall
  have hupper := hE.add hR
  simp only [mul_zero, zero_add] at hupper
  have hbound : ∀ᶠ n : ℕ in atTop,
      |(disc n - lead n) / boundedLowerScale n (m n)| ≤
        8*Real.exp 4*(rademacherLocalError n (m n)/boundedLowerScale n (m n)) +
          cost n * familyShiftSecondMoments (boundedFamilyParameters n (m n)) n (m n) / boundedLowerScale n (m n) := by
    filter_upwards [hmTop.eventually hCB, hmTop.eventually eventually_normalTail_local_mass_bound,
      eventually_boundedFamily_rademacher_conditions hmTop hsmall, hlog.eventually (eventually_ge_atTop 1),
      eventually_ge_atTop 1, eventually_boundedLowerScale_pos hmTop]
      with n hnB hnMass hnRad hnL hn1 hnd
    have hh := familyLocal_master_comparison (boundedFamilyParameters n (m n)) hn1 hnL hnMass hnRad.1 hnRad.2
      (mul_nonneg hC.le (by linarith)) hnB
    have hdiv := div_le_div_of_nonneg_right hh hnd.le
    rw [abs_div, abs_of_pos hnd]
    convert hdiv using 1
    ring
  have habs := squeeze_zero' (Eventually.of_forall (fun n => abs_nonneg _)) hbound hupper
  have herr : Tendsto (fun n => (disc n - lead n) / boundedLowerScale n (m n)) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [sub_zero, Real.norm_eq_abs] using habs)
  have hh := hlead.add herr
  simp only [add_zero] at hh
  convert hh using 1
  funext n
  dsimp only [disc, lead]
  ring

theorem dimensionLog_square (m : ℕ) (hm : 1 ≤ m) : dimensionLog (m*m) = 1 + 2*Real.log (m : ℝ) := by
  have hm0 : m ≠ 0 := by omega
  have hmm : 1 ≤ m*m := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hm0 hm0)
  rw [dimensionLog_eq_one_add_log hmm, Nat.cast_mul,
    Real.log_mul (by exact_mod_cast hm0) (by exact_mod_cast hm0)]
  ring

theorem tendsto_boundedSymmetricLowerRate_div_scale {m : ℕ → ℕ} (hm : ∀ n, 2 ≤ m n)
    (hmTop : Tendsto m atTop atTop) :
    Tendsto (fun n : ℕ => boundedSymmetricLowerRate n (m n) / boundedLowerScale n (m n)) atTop
      (𝓝 ((2 : ℝ) ^ (7 / 2 : ℝ))) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (m n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmTop)
  have hh := tendsto_lower_bounded_rate_conversion hlog
  convert hh using 1
  funext n
  rw [boundedSymmetricLowerRate, dimensionLog_square (m n) (by have := hm n; omega), boundedLowerScale]

theorem eventually_boundedSymmetricLowerRate_pos {m : ℕ → ℕ} (hm : ∀ n, 2 ≤ m n) :
    ∀ᶠ n : ℕ in atTop, 0 < boundedSymmetricLowerRate n (m n) := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  unfold boundedSymmetricLowerRate
  have hL : 0 < dimensionLog (m n*m n) := by
    rw [dimensionLog_square _ (by have := hm n; omega)]
    have hlog := Real.log_pos (show (1 : ℝ) < m n by exact_mod_cast hm n)
    linarith
  exact mul_pos (div_pos (by norm_num) (Real.sqrt_pos.mpr hnp)) (Real.rpow_pos_of_pos hL _)

theorem bounded_lower_constant_identity :
    (Real.sqrt 2 * Real.exp (-1)) / (2 : ℝ) ^ (7 / 2 : ℝ) = 1 / (8 * Real.exp 1) := by
  have hpow : (2 : ℝ) ^ (7 / 2 : ℝ) = 8 * Real.sqrt 2 := by
    rw [show (7 / 2 : ℝ) = 3 + 1 / 2 by norm_num, Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      show (2 : ℝ) ^ (3 : ℝ) = 8 by norm_num, ← Real.sqrt_eq_rpow]
  rw [hpow, Real.exp_neg]
  field_simp [(Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne', (Real.exp_pos 1).ne']
  ring

theorem tendsto_boundedFamily_discrepancy_div_rate {m : ℕ → ℕ} [∀ n, NeZero (m n)]
    (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => Real.log (m n : ℝ) ^ 3 / n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => familyShiftedCDFDifference (boundedFamilyParameters n (m n)) n (m n)
      (normalMaxThreshold (m n)) / boundedSymmetricLowerRate n (m n)) atTop (𝓝 (1 / (8 * Real.exp 1))) := by
  have hh := (tendsto_boundedFamily_discrepancy_div_scale hm hmTop hsmall).div
    (tendsto_boundedSymmetricLowerRate_div_scale hm hmTop) (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).ne'
  rw [bounded_lower_constant_identity] at hh
  apply hh.congr'
  filter_upwards [eventually_boundedLowerScale_pos hmTop, eventually_boundedSymmetricLowerRate_pos hm] with n hd hr
  field_simp [hd.ne', hr.ne']


/-- The actual orthant in the construction has the sharp paper constant. -/
theorem tendsto_boundedFamily_orthantError_div_rate {m : ℕ → ℕ} [∀ n, NeZero (m n)]
    (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => Real.log (m n : ℝ) ^ 3 / n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      rectangleError (familyArrayLaw (boundedFamilyParameters n (m n)) n (m n))
        (sumVector (familyNormalizedObservations (boundedFamilyParameters n (m n))))
        (familyGaussianSquareFactor (boundedFamilyParameters n (m n)) (m n))
        (familyOrthant (m n * m n)
          ((boundedFamilyParameters n (m n)).scale * normalMaxThreshold (m n))) /
        boundedSymmetricLowerRate n (m n)) atTop (𝓝 (1 / (8 * Real.exp 1))) := by
  have hh := (continuous_abs.tendsto (1 / (8 * Real.exp 1))).comp
    (tendsto_boundedFamily_discrepancy_div_rate hm hmTop hsmall)
  rw [abs_of_pos (by positivity : (0 : ℝ) < 1 / (8 * Real.exp 1))] at hh
  apply hh.congr'
  filter_upwards [eventually_boundedSymmetricLowerRate_pos hm] with n hn
  dsimp only [Function.comp_apply]
  rw [familyShiftedCDFDifference_rectangleError _ _ _ _ (familyGaussianSquareFactor_gram _ _),
    abs_div, abs_of_pos hn]

/-- An equivalent real formulation of the full-distance lower limit. -/
theorem eventually_boundedFamily_distance_div_rate_ge {m : ℕ → ℕ} [∀ n, NeZero (m n)]
    (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => Real.log (m n : ℝ) ^ 3 / n) atTop (𝓝 0))
    {c : ℝ} (hc : c < 1 / (8 * Real.exp 1)) :
    ∀ᶠ n : ℕ in atTop, c ≤
      familyComparisonDistance (boundedFamilyParameters n (m n)) n (m n) /
        boundedSymmetricLowerRate n (m n) := by
  filter_upwards [(tendsto_boundedFamily_discrepancy_div_rate hm hmTop hsmall).eventually
      (eventually_gt_nhds hc), eventually_boundedSymmetricLowerRate_pos hm] with n hdisc hr
  exact hdisc.le.trans (div_le_div_of_nonneg_right
    (familyShiftedCDFDifference_le_distance _ _ _ _) hr.le)

/-- The literal lower limit is taken in the complete extended-real order;
no upper bound on the normalized distances is needed. -/
theorem boundedFamily_distance_ereal_liminf {m : ℕ → ℕ} [∀ n, NeZero (m n)]
    (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => Real.log (m n : ℝ) ^ 3 / n) atTop (𝓝 0)) :
    ((1 / (8 * Real.exp 1) : ℝ) : EReal) ≤
      liminf (fun n : ℕ =>
        ((familyComparisonDistance (boundedFamilyParameters n (m n)) n (m n) /
          boundedSymmetricLowerRate n (m n) : ℝ) : EReal)) atTop := by
  have hlim := continuous_coe_real_ereal.continuousAt.tendsto.comp
    (tendsto_boundedFamily_discrepancy_div_rate hm hmTop hsmall)
  have hmono : ∀ᶠ n : ℕ in atTop,
      ((familyShiftedCDFDifference (boundedFamilyParameters n (m n)) n (m n)
        (normalMaxThreshold (m n)) / boundedSymmetricLowerRate n (m n) : ℝ) : EReal) ≤
      ((familyComparisonDistance (boundedFamilyParameters n (m n)) n (m n) /
        boundedSymmetricLowerRate n (m n) : ℝ) : EReal) := by
    filter_upwards [eventually_boundedSymmetricLowerRate_pos hm] with n hn
    exact_mod_cast div_le_div_of_nonneg_right
      (familyShiftedCDFDifference_le_distance _ _ _ _) hn.le
  have hh := liminf_le_liminf hmono
  have hEq := hlim.liminf_eq
  simp only [Function.comp_def] at hEq
  rw [hEq] at hh
  exact hh

/-- Concrete data and conclusions of Theorem 4. All laws, observations,
Gaussian factors and rectangles are the explicit definitions above. -/
structure BoundedSymmetricLowerConstruction (m : ℕ → ℕ) : Prop where
  properties : ∀ᶠ n : ℕ in atTop,
    CommonSymmetricFamilyProperties (boundedFamilyParameters n (m n)) n (m n)
  envelope : ∀ (n : ℕ) (i : Fin n) (z : Fin n → FamilySeed (m n)),
    ‖familyRawObservations (boundedFamilyParameters n (m n)) i z‖ ≤ 2
  matchingGaussianCovariance : ∀ᶠ n : ℕ in atTop,
    familyGaussianSquareFactor (boundedFamilyParameters n (m n)) (m n) *
      (familyGaussianSquareFactor (boundedFamilyParameters n (m n)) (m n)).transpose =
    covariance (familyArrayLaw (boundedFamilyParameters n (m n)) n (m n))
      (sumVector (familyNormalizedObservations (boundedFamilyParameters n (m n))))
  orthantLimit : Tendsto (fun n : ℕ =>
    rectangleError (familyArrayLaw (boundedFamilyParameters n (m n)) n (m n))
      (sumVector (familyNormalizedObservations (boundedFamilyParameters n (m n))))
      (familyGaussianSquareFactor (boundedFamilyParameters n (m n)) (m n))
      (familyOrthant (m n * m n)
        ((boundedFamilyParameters n (m n)).scale * normalMaxThreshold (m n))) /
      boundedSymmetricLowerRate n (m n)) atTop (𝓝 (1 / (8 * Real.exp 1)))
  distanceLiminf : ((1 / (8 * Real.exp 1) : ℝ) : EReal) ≤
    liminf (fun n : ℕ =>
      ((familyComparisonDistance (boundedFamilyParameters n (m n)) n (m n) /
        boundedSymmetricLowerRate n (m n) : ℝ) : EReal)) atTop

/-- Theorem 4 (`opt:symmetric-lower`): genuine i.i.d. centered symmetric
observations bounded by two, with unit marginals and the stated lower constant. -/
theorem boundedSymmetricLower {m : ℕ → ℕ} (hm : ∀ n, 2 ≤ m n)
    (hmTop : Tendsto m atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => Real.log (m n : ℝ) ^ 3 / n) atTop (𝓝 0)) :
    BoundedSymmetricLowerConstruction m := by
  letI : ∀ n, NeZero (m n) := fun n => ⟨by have := hm n; omega⟩
  have hproperties : ∀ᶠ n : ℕ in atTop,
      CommonSymmetricFamilyProperties (boundedFamilyParameters n (m n)) n (m n) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact symmetricFamilyProperties _ hn (hm n)
  refine ⟨hproperties, fun n i z => boundedFamily_observations_envelope _ _ i z, ?_,
    tendsto_boundedFamily_orthantError_div_rate hm hmTop hsmall,
    boundedFamily_distance_ereal_liminf hm hmTop hsmall⟩
  filter_upwards [hproperties] with n hn
  rw [familyGaussianSquareFactor_gram, hn.sumCovariance]

end
end RectangleCLT.Companion.SplitV4
