import RectangleCLTArxivV1.TransfersCovarianceRestoration
import RectangleCLTCompanion.SplitV4.Printed.PolynomialMoments

/-! The printed direct diagonal-maximum budget for the first Gaussian
addition. Every conditional covariance and mask is the actual one. -/

namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators

noncomputable def matrixMaxDiagonal {p : ℕ} (M : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  (Finset.univ : Finset (Fin p)).fold max 0 (fun j => M j j)

theorem matrixMaxDiagonal_nonneg {p : ℕ} (M : Matrix (Fin p) (Fin p) ℝ) :
    0 ≤ matrixMaxDiagonal M := (Finset.le_fold_max 0).mpr (Or.inl le_rfl)

theorem diagonal_le_matrixMaxDiagonal {p : ℕ} (M : Matrix (Fin p) (Fin p) ℝ) (j : Fin p) :
    M j j ≤ matrixMaxDiagonal M :=
  (Finset.le_fold_max (M j j)).mpr (Or.inr ⟨j, Finset.mem_univ j, le_rfl⟩)

theorem matrixMaxDiagonal_le_norm {p : ℕ} (M : Matrix (Fin p) (Fin p) ℝ) :
    matrixMaxDiagonal M ≤ matrixMaxEntryNorm M := by
  apply (Finset.fold_max_le _).mpr
  refine ⟨norm_nonneg _, ?_⟩
  intro j _
  exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using
    (norm_le_pi_norm (M j) j).trans (norm_le_pi_norm M j))

/-- Exact `2 B²` conditional covariance bound, from the actual envelope
moment by the archive's printed Lyapunov/Jensen argument. -/
theorem conditionalGoodCovariance_maxDiagonal_le {p : ℕ}
    (μ : Measure (Vector p)) [IsProbabilityMeasure μ] {B T q : ℝ}
    (h : ConditionalTruncationMomentHypotheses μ B T q) :
    matrixMaxDiagonal (covariance (goodConditionalLaw μ T) id) ≤ 2 * B ^ 2 := by
  apply (Finset.fold_max_le _).mpr
  refine ⟨by positivity, ?_⟩
  intro j _
  exact (le_abs_self _).trans (Printed.abs_good_covariance_le_envelope_sq h j j)

/-- The maximum diagonal omitted by a mask is bounded by the sum of the
omitted conditional diagonal maxima, exactly as in the printed proof. -/
theorem conditionalMask_maxDiagonal_le_sum {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) (T : ℝ) (mask : Fin n → Bool) :
    matrixMaxDiagonal (conditionalAllCovariance μ T - conditionalCovarianceForMask μ T mask) ≤
      (1 / (n : ℝ)) * ∑ i, if mask i then
        matrixMaxDiagonal (covariance (goodConditionalLaw (μ i) T) id) else 0 := by
  apply (Finset.fold_max_le _).mpr
  constructor
  · apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro i _
    split <;> simp only [matrixMaxDiagonal_nonneg, le_refl]
  · intro j _
    have heq : (conditionalAllCovariance μ T - conditionalCovarianceForMask μ T mask) j j =
        (1 / (n : ℝ)) * ∑ i, if mask i then covariance (goodConditionalLaw (μ i) T) id j j else 0 := by
      unfold conditionalAllCovariance conditionalCovarianceForMask
      simp only [Matrix.sub_apply, Bool.false_eq_true, if_false, ← mul_sub, ← Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      split <;> simp
    rw [heq]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro i _
    split
    · exact diagonal_le_matrixMaxDiagonal _ j
    · exact le_rfl

/-- The actual observed omitted-diagonal maximum is integrable. -/
theorem integrable_observedOmittedDiagonalMaximum {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)] (T : ℝ) :
    Integrable (fun x => matrixMaxDiagonal
      (conditionalAllCovariance μ T - conditionalCovarianceForMask μ T (observedTruncationMask T x)))
      (Measure.pi μ) := by
  let f := fun mask : Fin n → Bool => matrixMaxDiagonal
    (conditionalAllCovariance μ T - conditionalCovarianceForMask μ T mask)
  have hm : Measurable (fun x : Fin n → Vector p => f (observedTruncationMask T x)) :=
    (measurable_of_countable f).comp (measurable_observedTruncationMask T)
  apply (integrable_const (∑ mask, f mask)).mono' hm.aestronglyMeasurable
  apply ae_of_all
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (matrixMaxDiagonal_nonneg _)]
  have hnonneg (mask : Fin n → Bool) : 0 ≤ f mask := matrixMaxDiagonal_nonneg _
  exact Finset.single_le_sum (fun mask _ => hnonneg mask)
    (Finset.mem_univ (observedTruncationMask T x))

/-- The direct expectation in the printed first-addition argument. It
uses the `2B²` bound and `p_i B² ≤ v_T`, with no covariance-deviation detour. -/
theorem expected_observedOmittedDiagonalMaximum_le {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    {B T q : ℝ} (h : ∀ i, ConditionalTruncationMomentHypotheses (μ i) B T q) (hn : 1 ≤ n) :
    (∫ x, matrixMaxDiagonal
      (conditionalAllCovariance μ T - conditionalCovarianceForMask μ T (observedTruncationMask T x))
      ∂Measure.pi μ) ≤ 2 * truncationVarianceBudget B T q := by
  let c (i : Fin n) := matrixMaxDiagonal (covariance (goodConditionalLaw (μ i) T) id)
  let F : (Fin n → Vector p) → ℝ := fun x => (1 / (n : ℝ)) *
    ∑ i, c i * (if observedTruncationMask T x i then 1 else 0)
  have hi (i : Fin n) : Integrable
      (fun x : Fin n → Vector p => c i * (if observedTruncationMask T x i then 1 else 0)) (Measure.pi μ) :=
    (integrable_observed_exceptional_indicator μ T i).const_mul (c i)
  have hF : Integrable F (Measure.pi μ) := (integrable_finset_sum Finset.univ (fun i _ => hi i)).const_mul _
  have hp (i : Fin n) : c i * (μ i).real (goodTruncationSet T)ᶜ ≤
      2 * truncationVarianceBudget B T q := by
    have hh := mul_le_mul_of_nonneg_right (conditionalGoodCovariance_maxDiagonal_le (μ i) (h i))
      (measureReal_nonneg (μ := μ i) (s := (goodTruncationSet T)ᶜ))
    have hb := Printed.bad_probability_mul_envelope_sq_le (h i)
    change c i * (μ i).real (goodTruncationSet T)ᶜ ≤ _ at hh
    nlinarith only [hh, hb]
  calc
    _ ≤ ∫ x, F x ∂Measure.pi μ := integral_mono
      (integrable_observedOmittedDiagonalMaximum μ T) hF (fun x => by
        have hh := conditionalMask_maxDiagonal_le_sum μ T (observedTruncationMask T x)
        convert hh using 1
        dsimp only [F, c]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        split <;> simp [c])
    _ = (1 / (n : ℝ)) * ∑ i, c i * (μ i).real (goodTruncationSet T)ᶜ := by
      rw [show (∫ x, F x ∂Measure.pi μ) = (1 / (n : ℝ)) *
        (∫ x, ∑ i, c i * (if observedTruncationMask T x i then 1 else 0) ∂Measure.pi μ) from integral_const_mul _ _]
      rw [integral_finset_sum Finset.univ (fun i _ => hi i)]
      simp only [integral_const_mul, integral_observed_exceptional_indicator]
    _ ≤ (1 / (n : ℝ)) * ∑ _i : Fin n, 2 * truncationVarianceBudget B T q :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hp i)) (by positivity)
    _ = _ := by
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp

end RectangleCLTArxivV1
