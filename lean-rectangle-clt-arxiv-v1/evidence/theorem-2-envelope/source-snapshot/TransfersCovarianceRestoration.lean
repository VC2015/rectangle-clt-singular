import RectangleCLTArxivV1.TransfersWidth
import RectangleCLTCompanion.SplitV4.ConditionalExceptionalMaximum
import RectangleCLTCompanion.SplitV4.PairedNormalization

/-! The actual residual covariance identity used by the second Gaussian
addition comparison in Appendix E.1. -/

namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion
  RectangleCLT.Companion.SplitV4
open scoped BigOperators

/-- The deterministic all-retained conditional covariance `Q₀`. -/
noncomputable def conditionalAllCovariance {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) (T : ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  conditionalCovarianceForMask μ T (fun _ => false)

/-- The omitted conditional covariance `H_T=(1/n)∑p_i C_i^0`. -/
noncomputable def conditionalOmittedCovariance {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) (T : ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  fun j k => (1 / (n : ℝ)) * ∑ i, (μ i).real (goodTruncationSet T)ᶜ *
    covariance (goodConditionalLaw (μ i) T) id j k

/-- The covariance of the actual centered normalized exceptional sum. -/
noncomputable def conditionalResidualCovariance {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) (T : ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  covariance (Measure.pi μ) (normalizedObservationSum (exceptionalArray μ T))

private theorem exceptionalPart_pair_identity {p : ℕ}
    (μ : Measure (Vector p)) (T : ℝ) (j k : Fin p) (x : Vector p) :
    conditionalExceptionalPart μ T x j * conditionalExceptionalPart μ T x k =
      (goodTruncationSet T).indicator
        (fun _ => conditionalGoodMean μ T j * conditionalGoodMean μ T k) x +
      (goodTruncationSet T)ᶜ.indicator (fun x : Vector p => x j * x k) x := by
  by_cases hx : ‖x‖ ≤ T <;> simp [conditionalExceptionalPart, goodTruncationSet, hx]

/-- The residual covariance is computed from its actual disjoint good/bad
pieces. -/
theorem covariance_conditionalExceptionalPart {p : ℕ}
    (μ : Measure (Vector p)) [IsProbabilityMeasure μ] {B T q : ℝ}
    (h : ConditionalTruncationMomentHypotheses μ B T q) (j k : Fin p) :
    covariance μ (conditionalExceptionalPart μ T) j k =
      μ.real (goodTruncationSet T) * (conditionalGoodMean μ T j * conditionalGoodMean μ T k) +
      (∫ x in (goodTruncationSet T)ᶜ, x j * x k ∂μ) := by
  have hm (l : Fin p) := conditionalExceptionalPart_centered μ h.threshold_pos.le l
    (h.integrable_coordinate l) (h.centered l)
  simp only [covariance, hm, mul_zero, sub_zero]
  simp_rw [exceptionalPart_pair_identity]
  rw [integral_add ((integrable_const _).indicator (measurableSet_goodTruncationSet T))
    ((h.integrable_coordinate_pair j k).indicator (measurableSet_goodTruncationSet T).compl),
    integral_indicator (measurableSet_goodTruncationSet T),
    integral_indicator (measurableSet_goodTruncationSet T).compl]
  simp only [integral_const, smul_eq_mul, measureReal_restrict_apply_univ]

/-- The exact observation-level covariance identity. -/
theorem conditional_covariance_restoration_single {p : ℕ}
    (μ : Measure (Vector p)) [IsProbabilityMeasure μ] {B T q : ℝ}
    (h : ConditionalTruncationMomentHypotheses μ B T q) :
    covariance (goodConditionalLaw μ T) id + covariance μ (conditionalExceptionalPart μ T) =
      covariance μ id + μ.real (goodTruncationSet T)ᶜ • covariance (goodConditionalLaw μ T) id := by
  ext j k
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    covariance_conditionalExceptionalPart μ h j k]
  linarith [h.good_covariance_bias_identity j k]

/-- The residual average is the covariance of the actual normalized
independent exceptional sum. -/
theorem conditionalResidualCovariance_eq_average {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    {B T q : ℝ} (h : ∀ i, ConditionalTruncationMomentHypotheses (μ i) B T q)
    (hn : 1 ≤ n) (j k : Fin p) :
    conditionalResidualCovariance μ T j k = (1 / (n : ℝ)) *
      ∑ i, covariance (μ i) (conditionalExceptionalPart (μ i) T) j k := by
  have hLp (i : Fin n) (l : Fin p) :
      MemLp (fun x => exceptionalArray μ T i x l) 2 (Measure.pi μ) :=
    (memLp_two_iff_integrable_sq
      (((measurable_pi_apply l).comp (exceptionalArray_measurable μ T i)).aestronglyMeasurable)).mpr
      (exceptionalArray_second_integrable μ h i l)
  have hsum : sumVector (sampleNormalizedObservations (exceptionalArray μ T)) =
      normalizedObservationSum (exceptionalArray μ T) := by
    funext x
    ext l
    simp only [sampleNormalizedObservations, normalizedObservationSum, sumVector, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hc := covariance_sampleNormalizedObservations (exceptionalArray_independent μ T)
    (exceptionalArray_centered μ h) hLp (by omega : 0 < n) j k
  rw [hsum] at hc
  unfold conditionalResidualCovariance
  rw [hc]
  have hpair (i : Fin n) :
      (∫ x, exceptionalArray μ T i x j * exceptionalArray μ T i x k ∂Measure.pi μ) =
        covariance (μ i) (conditionalExceptionalPart (μ i) T) j k := by
    have hi : Integrable (fun x : Vector p =>
        conditionalExceptionalPart (μ i) T x j * conditionalExceptionalPart (μ i) T x k) (μ i) := by
      simp_rw [exceptionalPart_pair_identity]
      exact ((integrable_const _).indicator (measurableSet_goodTruncationSet T)).add
        (((h i).integrable_coordinate_pair j k).indicator (measurableSet_goodTruncationSet T).compl)
    rw [show (fun x => exceptionalArray μ T i x j * exceptionalArray μ T i x k) =
      (fun x : Fin n → Vector p => conditionalExceptionalPart (μ i) T (x i) j *
        conditionalExceptionalPart (μ i) T (x i) k) from rfl,
      integral_vectorProduct_eval μ i _ hi]
    have hm (l : Fin p) := conditionalExceptionalPart_centered (μ i) (h i).threshold_pos.le l
      ((h i).integrable_coordinate l) ((h i).centered l)
    simp only [covariance, hm, mul_zero, sub_zero]
  simp only [hpair, one_div, div_eq_mul_inv, mul_comm, mul_one]

/-- The two Gaussian additions have exactly the same covariance:
`Q₀ + D_R = Σ + H_T`. Every matrix is defined from the actual marginal laws. -/
theorem conditional_covariance_restoration {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    {B T q : ℝ} (h : ∀ i, ConditionalTruncationMomentHypotheses (μ i) B T q) (hn : 1 ≤ n) :
    conditionalAllCovariance μ T + conditionalResidualCovariance μ T =
      originalAverageCovariance μ + conditionalOmittedCovariance μ T := by
  ext j k
  simp only [Matrix.add_apply, conditionalAllCovariance, conditionalCovarianceForMask,
    Bool.false_eq_true, if_false, conditionalResidualCovariance_eq_average μ h hn,
    originalAverageCovariance, conditionalOmittedCovariance, ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have he := congrFun (congrFun (conditional_covariance_restoration_single (μ i) (h i)) j) k
  simpa only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] using he

/-- The covariance of the actual residual sum has the printed small
coordinate-variance budget. -/
theorem conditionalResidualCovariance_diagonal_le {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    {B T q : ℝ} (h : ∀ i, ConditionalTruncationMomentHypotheses (μ i) B T q)
    (hn : 1 ≤ n) (j : Fin p) :
    conditionalResidualCovariance μ T j j ≤ 2 * truncationVarianceBudget B T q := by
  rw [conditionalResidualCovariance_eq_average μ h hn]
  have hm (i : Fin n) := conditionalExceptionalPart_centered (μ i) (h i).threshold_pos.le j
    ((h i).integrable_coordinate j) ((h i).centered j)
  simp only [covariance, hm, mul_zero, sub_zero]
  simp only [← pow_two]
  calc
    _ ≤ (1 / (n : ℝ)) * ∑ _i : Fin n, 2 * truncationVarianceBudget B T q :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ =>
        (h i).integral_exceptionalPart_coordinate_sq_le j)) (by positivity)
    _ = _ := by
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp

/-- The second added Gaussian covariance has the same small diagonal
budget, obtained from the actual exceptional probabilities. -/
theorem conditionalOmittedCovariance_diagonal_le {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    {B T q : ℝ} (h : ∀ i, ConditionalTruncationMomentHypotheses (μ i) B T q)
    (hn : 1 ≤ n) (j : Fin p) :
    conditionalOmittedCovariance μ T j j ≤ 2 * truncationVarianceBudget B T q := by
  have hb (i : Fin n) : (μ i).real (goodTruncationSet T)ᶜ *
      covariance (goodConditionalLaw (μ i) T) id j j ≤
        2 * truncationVarianceBudget B T q := by
    have hc := (abs_le.mp ((h i).abs_good_covariance_le_threshold_sq j j)).2
    have hh := mul_le_mul_of_nonneg_left hc
      (measureReal_nonneg (μ := μ i) (s := (goodTruncationSet T)ᶜ))
    nlinarith only [hh, (h i).bad_probability_mul_threshold_sq_le]
  unfold conditionalOmittedCovariance
  calc
    _ ≤ (1 / (n : ℝ)) * ∑ _i : Fin n, 2 * truncationVarianceBudget B T q :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hb i)) (by positivity)
    _ = _ := by
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp

theorem factor_exists_of_symmetric_quadratic_nonneg {p : ℕ}
    (M : Matrix (Fin p) (Fin p) ℝ) (hs : M.transpose = M)
    (hq : ∀ v : Vector p, 0 ≤ matrixQuadratic M v) :
    ∃ A : Matrix (Fin p) (Fin p) ℝ, A * A.transpose = M := by
  have hPSD : M.PosSemidef := by
    constructor
    · simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hs
    · intro v
      simpa [matrixQuadratic, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc] using hq v
  refine ⟨hPSD.sqrt, ?_⟩
  have hsym : hPSD.sqrt.transpose = hPSD.sqrt := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using
      hPSD.posSemidef_sqrt.isHermitian
  rw [hsym]
  exact hPSD.sqrt_mul_self

/-- A genuine square Gaussian factor exists for the actual residual
covariance, including singular residual laws. -/
theorem conditionalResidualCovariance_factor_exists {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    {B T q : ℝ} (h : ∀ i, ConditionalTruncationMomentHypotheses (μ i) B T q) :
    ∃ D : Matrix (Fin p) (Fin p) ℝ,
      D * D.transpose = conditionalResidualCovariance μ T := by
  have hLp (i : Fin n) (j : Fin p) :
      MemLp (fun x => exceptionalArray μ T i x j) 2 (Measure.pi μ) :=
    (memLp_two_iff_integrable_sq
      (((measurable_pi_apply j).comp (exceptionalArray_measurable μ T i)).aestronglyMeasurable)).mpr
      (exceptionalArray_second_integrable μ h i j)
  obtain ⟨D, hD⟩ := normalizedSummands_gaussian_factor_exists hLp (exceptionalArray_centered μ h)
  exact ⟨D, by simpa only [sumVector_normalizedSummands, conditionalResidualCovariance] using hD⟩

/-- The omitted covariance is nonnegative in every direction. -/
theorem conditionalOmittedCovariance_quadratic_nonneg {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    {T : ℝ} (hT : 0 ≤ T) (v : Vector p) :
    0 ≤ matrixQuadratic (conditionalOmittedCovariance μ T) v := by
  have heq : conditionalOmittedCovariance μ T = fun j k => (1 / (n : ℝ)) *
      ∑ i, ((μ i).real (goodTruncationSet T)ᶜ • covariance (goodConditionalLaw (μ i) T) id) j k := rfl
  rw [heq, matrixQuadratic_average]
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro i _
  rw [matrixQuadratic_smul_real]
  exact mul_nonneg measureReal_nonneg (goodConditional_covariance_quadratic_nonneg (μ i) hT v)

/-- The omitted covariance has an actual Gaussian factor as well. -/
theorem conditionalOmittedCovariance_factor_exists {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ H : Matrix (Fin p) (Fin p) ℝ,
      H * H.transpose = conditionalOmittedCovariance μ T := by
  apply factor_exists_of_symmetric_quadratic_nonneg _ _
    (conditionalOmittedCovariance_quadratic_nonneg μ hT)
  ext j k
  simp only [Matrix.transpose_apply, conditionalOmittedCovariance, covariance, mul_comm]

/-- The Gaussian covariance `Q₀-Q` is positive semidefinite for every
retained mask, so the first covariance addition also exists concretely. -/
theorem conditionalMaskDifference_factor_exists {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    {T : ℝ} (hT : 0 ≤ T) (mask : Fin n → Bool) :
    ∃ J : Matrix (Fin p) (Fin p) ℝ,
      J * J.transpose = conditionalAllCovariance μ T - conditionalCovarianceForMask μ T mask := by
  apply factor_exists_of_symmetric_quadratic_nonneg
  · ext j k
    simp only [Matrix.transpose_apply, Matrix.sub_apply, conditionalAllCovariance,
      conditionalCovarianceForMask, covariance, mul_comm]
  · intro v
    have heq : matrixQuadratic
        (conditionalAllCovariance μ T - conditionalCovarianceForMask μ T mask) v =
        matrixQuadratic (conditionalAllCovariance μ T) v -
          matrixQuadratic (conditionalCovarianceForMask μ T mask) v := by
      simp only [matrixQuadratic, Matrix.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]
    rw [heq]
    exact sub_nonneg.mpr (conditionalCovarianceForMask_quadratic_le_allRetained μ hT mask v)

end RectangleCLTArxivV1
