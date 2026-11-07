import RectangleCLTCompanion.SplitV4.Printed.LowerTheorems

/-! Full explicit lower-construction endpoints for T4, T5, T6 and T8,
with the paper's literal detecting orthant and the printed global proof.
Earlier result-certificate constructions are retained separately. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

theorem eventually_boundedFamily_distance_div_rate_ge_printed {m : ℕ → ℕ} [∀ n, NeZero (m n)]
    (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => Real.log (m n : ℝ) ^ 3 / n) atTop (𝓝 0))
    {c : ℝ} (hc : c < 1 / (8 * Real.exp 1)) :
    ∀ᶠ n : ℕ in atTop, c ≤
      familyComparisonDistance (boundedFamilyParameters n (m n)) n (m n) /
        boundedSymmetricLowerRate n (m n) := by
  filter_upwards [(tendsto_boundedFamily_discrepancy_div_rate_printed hm hmTop hsmall).eventually
      (eventually_gt_nhds hc), eventually_boundedSymmetricLowerRate_pos hm] with n hdisc hr
  exact hdisc.le.trans (div_le_div_of_nonneg_right
    (familyShiftedCDFDifference_le_distance _ _ _ _) hr.le)

/-- The literal lower limit is taken in the complete extended-real order;
no upper bound on the normalized distances is needed. -/
theorem boundedFamily_distance_ereal_liminf_printed {m : ℕ → ℕ} [∀ n, NeZero (m n)]
    (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => Real.log (m n : ℝ) ^ 3 / n) atTop (𝓝 0)) :
    ((1 / (8 * Real.exp 1) : ℝ) : EReal) ≤
      liminf (fun n : ℕ =>
        ((familyComparisonDistance (boundedFamilyParameters n (m n)) n (m n) /
          boundedSymmetricLowerRate n (m n) : ℝ) : EReal)) atTop := by
  have hlim := continuous_coe_real_ereal.continuousAt.tendsto.comp
    (tendsto_boundedFamily_discrepancy_div_rate_printed hm hmTop hsmall)
  have hmono : ∀ᶠ n : ℕ in atTop,
      ((familyShiftedCDFDifference (boundedFamilyParameters n (m n)) n (m n)
        (printedNormalMaxThreshold (m n)) / boundedSymmetricLowerRate n (m n) : ℝ) : EReal) ≤
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
structure BoundedSymmetricLowerConstruction_printed (m : ℕ → ℕ) : Prop where
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
        ((boundedFamilyParameters n (m n)).scale * printedNormalMaxThreshold (m n))) /
      boundedSymmetricLowerRate n (m n)) atTop (𝓝 (1 / (8 * Real.exp 1)))
  distanceLiminf : ((1 / (8 * Real.exp 1) : ℝ) : EReal) ≤
    liminf (fun n : ℕ =>
      ((familyComparisonDistance (boundedFamilyParameters n (m n)) n (m n) /
        boundedSymmetricLowerRate n (m n) : ℝ) : EReal)) atTop

/-- Theorem 4 (`opt:symmetric-lower`): genuine i.i.d. centered symmetric
observations bounded by two, with unit marginals and the stated lower constant. -/
theorem boundedSymmetricLower_printed {m : ℕ → ℕ} (hm : ∀ n, 2 ≤ m n)
    (hmTop : Tendsto m atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => Real.log (m n : ℝ) ^ 3 / n) atTop (𝓝 0)) :
    BoundedSymmetricLowerConstruction_printed m := by
  letI : ∀ n, NeZero (m n) := fun n => ⟨by have := hm n; omega⟩
  have hproperties : ∀ᶠ n : ℕ in atTop,
      CommonSymmetricFamilyProperties (boundedFamilyParameters n (m n)) n (m n) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact symmetricFamilyProperties _ hn (hm n)
  refine ⟨hproperties, fun n i z => boundedFamily_observations_envelope _ _ i z, ?_,
    tendsto_boundedFamily_orthantError_div_rate_printed hm hmTop hsmall,
    boundedFamily_distance_ereal_liminf_printed hm hmTop hsmall⟩
  filter_upwards [hproperties] with n hn
  rw [familyGaussianSquareFactor_gram, hn.sumCovariance]

theorem fourthFamily_distance_ereal_liminf_printed {m : ℕ → ℕ} [∀ n, NeZero (m n)]
    (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hrate : Tendsto (fun n : ℕ => fourthMomentLowerRate n (m n)) atTop (𝓝 0)) :
    ((1/(2*Real.sqrt 2*Real.exp 1) : ℝ) : EReal) ≤
      liminf (fun n : ℕ =>
        ((familyComparisonDistance (fourthFamilyParameters n (m n)) n (m n) /
          fourthMomentLowerRate n (m n) : ℝ) : EReal)) atTop := by
  have hlim := continuous_coe_real_ereal.continuousAt.tendsto.comp
    (tendsto_fourthFamily_discrepancy_div_rate_printed hm hmTop hrate)
  have hmono : ∀ᶠ n : ℕ in atTop,
      ((familyShiftedCDFDifference (fourthFamilyParameters n (m n)) n (m n)
        (printedNormalMaxThreshold (m n))/fourthMomentLowerRate n (m n) : ℝ) : EReal) ≤
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

structure FourthMomentLowerConstruction_printed (m : ℕ → ℕ) : Prop where
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
      (familyOrthant (m n*m n) ((fourthFamilyParameters n (m n)).scale*printedNormalMaxThreshold (m n))) /
      fourthMomentLowerRate n (m n)) atTop (𝓝 (1/(2*Real.sqrt 2*Real.exp 1)))
  distanceLiminf : ((1/(2*Real.sqrt 2*Real.exp 1) : ℝ) : EReal) ≤
    liminf (fun n : ℕ =>
      ((familyComparisonDistance (fourthFamilyParameters n (m n)) n (m n) /
        fourthMomentLowerRate n (m n) : ℝ) : EReal)) atTop

theorem fourthMomentLower_of_two_le_printed {m : ℕ → ℕ} (hm : ∀ n, 2 ≤ m n)
    (hmTop : Tendsto m atTop atTop)
    (hrate : Tendsto (fun n : ℕ => fourthMomentLowerRate n (m n)) atTop (𝓝 0)) :
    FourthMomentLowerConstruction_printed m := by
  letI : ∀ n, NeZero (m n) := fun n => ⟨by have := hm n; omega⟩
  have hprops : ∀ᶠ n : ℕ in atTop,
      CommonSymmetricFamilyProperties (fourthFamilyParameters n (m n)) n (m n) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact symmetricFamilyProperties _ hn (hm n)
  refine ⟨hprops, ?_, ?_, tendsto_fourthFamily_orthantError_div_rate_printed hm hmTop hrate,
    fourthFamily_distance_ereal_liminf_printed hm hmTop hrate⟩
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact fourthFamily_polynomialIndependent hn
  · filter_upwards [hprops] with n hn
    rw [familyGaussianSquareFactor_gram, hn.sumCovariance]

/-- The fourth-moment lower construction under the literal dimension
sequence assumptions; no lower bound on finitely many initial dimensions is imposed. -/
theorem fourthMomentLower_printed {m : ℕ → ℕ} (hmTop : Tendsto m atTop atTop)
    (hrate : Tendsto (fun n : ℕ => fourthMomentLowerRate n (m n)) atTop (𝓝 0)) :
    FourthMomentLowerConstruction_printed m := by
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
  have h := fourthMomentLower_of_two_le_printed (fun n => le_max_left 2 (m n)) hm'Top hr'
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

theorem maskedFourthFamily_distance_ereal_liminf_printed {B : ℕ → ℝ} {m : ℕ → ℕ} [∀ n, NeZero (m n)]
    (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop) (hBTop : Tendsto B atTop atTop)
    (hΛ : Tendsto (fun n : ℕ => maskedFourthLog (B n)/Real.log (m n : ℝ)) atTop (𝓝 0))
    (hrate : Tendsto (fun n : ℕ => maskedFourthMomentLowerRate n (m n) (B n)) atTop (𝓝 0)) :
    ((1/(4*Real.exp 1) : ℝ) : EReal) ≤
      liminf (fun n : ℕ => ((familyComparisonDistance (maskedFourthFamilyParameters n (m n) (B n)) n (m n) /
        maskedFourthMomentLowerRate n (m n) (B n) : ℝ) : EReal)) atTop := by
  have hlim := continuous_coe_real_ereal.continuousAt.tendsto.comp
    (tendsto_maskedFourthFamily_orthantError_div_rate_printed hm hmTop hBTop hΛ hrate)
  have hmono : ∀ᶠ n : ℕ in atTop,
      ((rectangleError (familyArrayLaw (maskedFourthFamilyParameters n (m n) (B n)) n (m n))
        (sumVector (familyNormalizedObservations (maskedFourthFamilyParameters n (m n) (B n))))
        (familyGaussianSquareFactor (maskedFourthFamilyParameters n (m n) (B n)) (m n))
        (familyOrthant (m n*m n) ((maskedFourthFamilyParameters n (m n) (B n)).scale*printedNormalMaxThreshold (m n))) /
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

structure MaskedFourthLowerConstruction_printed (B : ℕ → ℝ) (m : ℕ → ℕ) : Prop where
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
      (familyOrthant (m n*m n) ((maskedFourthFamilyParameters n (m n) (B n)).scale*printedNormalMaxThreshold (m n))) /
      maskedFourthMomentLowerRate n (m n) (B n)) atTop (𝓝 (1/(4*Real.exp 1)))
  distanceLiminf : ((1/(4*Real.exp 1) : ℝ) : EReal) ≤
    liminf (fun n : ℕ => ((familyComparisonDistance (maskedFourthFamilyParameters n (m n) (B n)) n (m n) /
      maskedFourthMomentLowerRate n (m n) (B n) : ℝ) : EReal)) atTop

theorem maskedFourthLower_of_two_le_printed {B : ℕ → ℝ} {m : ℕ → ℕ}
    (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop) (hBTop : Tendsto B atTop atTop)
    (hΛ : Tendsto (fun n : ℕ => maskedFourthLog (B n)/Real.log (m n : ℝ)) atTop (𝓝 0))
    (hrate : Tendsto (fun n : ℕ => maskedFourthMomentLowerRate n (m n) (B n)) atTop (𝓝 0)) :
    MaskedFourthLowerConstruction_printed B m := by
  letI : ∀ n, NeZero (m n) := fun n => ⟨by have := hm n; omega⟩
  have hprops : ∀ᶠ n : ℕ in atTop, CommonSymmetricFamilyProperties (maskedFourthFamilyParameters n (m n) (B n)) n (m n) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact symmetricFamilyProperties _ hn (hm n)
  refine ⟨hprops, eventually_maskedFourthFamily_polynomialIndependent hmTop hBTop hrate, ?_,
    tendsto_maskedFourthFamily_orthantError_div_rate_printed hm hmTop hBTop hΛ hrate,
    maskedFourthFamily_distance_ereal_liminf_printed hm hmTop hBTop hΛ hrate⟩
  filter_upwards [hprops] with n hn
  rw [familyGaussianSquareFactor_gram, hn.sumCovariance]

/-- Theorem 6 (`opt:q4-growing`) for the genuine masked model. -/
theorem maskedFourthLower_printed {B : ℕ → ℝ} {m : ℕ → ℕ}
    (hmTop : Tendsto m atTop atTop) (hBTop : Tendsto B atTop atTop)
    (hΛ : Tendsto (fun n : ℕ => maskedFourthLog (B n)/Real.log (m n : ℝ)) atTop (𝓝 0))
    (hrate : Tendsto (fun n : ℕ => maskedFourthMomentLowerRate n (m n) (B n)) atTop (𝓝 0)) :
    MaskedFourthLowerConstruction_printed B m := by
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
  have h := maskedFourthLower_of_two_le_printed (fun n => le_max_left 2 (m n)) hm'Top hBTop hΛ' hr'
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

theorem sparseFamily_distance_ereal_liminf_printed {B : ℕ → ℝ} {m : ℕ → ℕ} {q : ℝ} [∀ n, NeZero (m n)]
    (hq : 2 < q) (hB : ∀ n, 2 ≤ B n) (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hK : Tendsto (fun n => sparseMomentK n (m n) q (B n)) atTop atTop)
    (hLog : Tendsto (fun n => Real.log (sparseMomentK n (m n) q (B n))/dimensionLog (m n*m n)) atTop (𝓝 0))
    (hrate : Tendsto (fun n : ℕ => sparseMomentLowerRate n (m n) q (B n)) atTop (𝓝 0)) :
    ((sparseMomentLowerConstant q : ℝ) : EReal) ≤
      liminf (fun n : ℕ => ((familyComparisonDistance (sparseFamilyParameters q n (m n) (B n)) n (m n) /
        sparseMomentLowerRate n (m n) q (B n) : ℝ) : EReal)) atTop := by
  have hlim := continuous_coe_real_ereal.continuousAt.tendsto.comp
    (tendsto_sparseFamily_orthantError_div_rate_printed hq hB hm hmTop hK hLog hrate)
  have hmono : ∀ᶠ n : ℕ in atTop,
      ((rectangleError (familyArrayLaw (sparseFamilyParameters q n (m n) (B n)) n (m n))
        (sumVector (familyNormalizedObservations (sparseFamilyParameters q n (m n) (B n))))
        (familyGaussianSquareFactor (sparseFamilyParameters q n (m n) (B n)) (m n))
        (familyOrthant (m n*m n) ((sparseFamilyParameters q n (m n) (B n)).scale*printedNormalMaxThreshold (m n))) /
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

structure SparseMomentLowerConstruction_printed (q : ℝ) (B : ℕ → ℝ) (m : ℕ → ℕ) : Prop where
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
      (familyOrthant (m n*m n) ((sparseFamilyParameters q n (m n) (B n)).scale*printedNormalMaxThreshold (m n))) /
      sparseMomentLowerRate n (m n) q (B n)) atTop (𝓝 (sparseMomentLowerConstant q))
  positiveConstant : 0 < sparseMomentLowerConstant q
  distanceLiminf : ((sparseMomentLowerConstant q : ℝ) : EReal) ≤
    liminf (fun n : ℕ => ((familyComparisonDistance (sparseFamilyParameters q n (m n) (B n)) n (m n) /
      sparseMomentLowerRate n (m n) q (B n) : ℝ) : EReal)) atTop

theorem sparseMomentLower_of_two_le_printed {B : ℕ → ℝ} {m : ℕ → ℕ} {q : ℝ}
    (hq : 2 < q) (hB : ∀ n, 2 ≤ B n) (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hK : Tendsto (fun n => sparseMomentK n (m n) q (B n)) atTop atTop)
    (hLog : Tendsto (fun n => Real.log (sparseMomentK n (m n) q (B n))/dimensionLog (m n*m n)) atTop (𝓝 0))
    (hrate : Tendsto (fun n : ℕ => sparseMomentLowerRate n (m n) q (B n)) atTop (𝓝 0)) :
    SparseMomentLowerConstruction_printed q B m := by
  letI : ∀ n, NeZero (m n) := fun n => ⟨by have := hm n; omega⟩
  have hprops : ∀ᶠ n : ℕ in atTop, CommonSymmetricFamilyProperties (sparseFamilyParameters q n (m n) (B n)) n (m n) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact symmetricFamilyProperties _ hn (hm n)
  have hPaper := sparsePaperCalibration hq hB hm hmTop hK hLog hrate
  refine ⟨hprops, hPaper.polynomialClass, ?_,
    tendsto_sparseFamily_orthantError_div_rate_printed hq hB hm hmTop hK hLog hrate,
    sparseMomentLowerConstant_pos q, sparseFamily_distance_ereal_liminf_printed hq hB hm hmTop hK hLog hrate⟩
  filter_upwards [hprops] with n hn
  rw [familyGaussianSquareFactor_gram, hn.sumCovariance]

/-- The actual sparse model under the paper's literal hypotheses. -/
theorem sparseMomentLower_printed {B : ℕ → ℝ} {m : ℕ → ℕ} {q : ℝ}
    (hq : 2 < q) (hB : ∀ n, 2 ≤ B n) (hmTop : Tendsto m atTop atTop)
    (hK : Tendsto (fun n => sparseMomentK n (m n) q (B n)) atTop atTop)
    (hLog : Tendsto (fun n => Real.log (sparseMomentK n (m n) q (B n))/dimensionLog (m n*m n)) atTop (𝓝 0))
    (hrate : Tendsto (fun n => sparseMomentLowerRate n (m n) q (B n)) atTop (𝓝 0)) :
    SparseMomentLowerConstruction_printed q B m := by
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
  have h := sparseMomentLower_of_two_le_printed hq hB (fun n => le_max_left 2 (m n)) hm'Top hK' hLog' hr'
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
end RectangleCLT.Companion.SplitV4.Printed
