import RectangleCLT.GaussianComponentJoinedArray
import RectangleCLT.IndependentCovariance

/-!
# Moments and covariance of the actual joined bounded array

The third tensor is unchanged exactly, including cancellation across the
original observations. The added fourth-moment cost tends to zero. The
covariance loss is precisely the positive discarded Gaussian moment
matrix; no local eigenvalue condition is imposed on that component.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RectangleCLT

noncomputable section

theorem gaussianComponentJoinedArray_integral_sum
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (B : Matrix (Fin p) (Fin p) ℝ) (k : ℕ)
    (f : Vector p → ℝ) (hf : Measurable f) :
    (∑ i : Fin (n + k ^ 6), ∫ z,
      f (gaussianComponentJoinedArray (p := p) (n := n) k i z)
      ∂Measure.pi (gaussianComponentJoinedMarginal μ ξ B k)) =
      (∑ i : Fin n, ∫ ω, f (ξ i ω) ∂μ) +
        (k ^ 6 : ℕ) * ∫ x, f (gaussianComponentIncrement k x) ∂gaussianLaw B := by
  let ν := gaussianComponentJoinedMarginal μ ξ B k
  letI (i : Fin n ⊕ Fin (k ^ 6)) : IsProbabilityMeasure (ν i) :=
    gaussianComponentJoinedMarginal_isProbability μ ξ hξ B k i
  have hrow (i : Fin n ⊕ Fin (k ^ 6)) :
      (∫ z, f (z i) ∂Measure.pi ν) = ∫ x, f x ∂ν i := by
    have hm := integral_map (μ := Measure.pi ν)
      (measurable_pi_apply i).aemeasurable hf.aestronglyMeasurable
    rw [gaussianComponentPi_map_eval ν] at hm
    exact hm.symm
  change (∑ i, ∫ z, f (z (finSumFinEquiv.symm i)) ∂Measure.pi ν) = _
  simp_rw [hrow]
  rw [finSumFinEquiv.symm.sum_comp, Fintype.sum_sum_type]
  change (∑ i : Fin n, ∫ x, f x ∂μ.map (ξ i)) +
    (∑ _i : Fin (k ^ 6), ∫ x, f x
      ∂(gaussianLaw B).map (gaussianComponentIncrement k)) = _
  simp only [integral_map (measurable_gaussianComponentIncrement k).aemeasurable
    hf.aestronglyMeasurable, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact integral_map (hξ i).aemeasurable hf.aestronglyMeasurable

theorem gaussianComponentJoinedArray_third_sum
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (B : Matrix (Fin p) (Fin p) ℝ) (k : ℕ) (j l r : Fin p) :
    (∑ i : Fin (n + k ^ 6), ∫ z,
      gaussianComponentJoinedArray (p := p) (n := n) k i z j *
        gaussianComponentJoinedArray (p := p) (n := n) k i z l *
        gaussianComponentJoinedArray (p := p) (n := n) k i z r
      ∂Measure.pi (gaussianComponentJoinedMarginal μ ξ B k)) =
      ∑ i : Fin n, ∫ ω, ξ i ω j * ξ i ω l * ξ i ω r ∂μ := by
  have hm := gaussianComponentJoinedArray_integral_sum μ ξ hξ B k
    (fun x => x j * x l * x r)
    (((measurable_pi_apply j).mul (measurable_pi_apply l)).mul (measurable_pi_apply r))
  simpa only [gaussianComponentIncrement_third_integral_zero, mul_zero, add_zero] using hm

theorem gaussianComponentJoinedArray_gamma3
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (B : Matrix (Fin p) (Fin p) ℝ) (k : ℕ) :
    gamma3 (Measure.pi (gaussianComponentJoinedMarginal μ ξ B k))
      (gaussianComponentJoinedArray (p := p) (n := n) k) = gamma3 μ ξ := by
  unfold gamma3
  simp_rw [gaussianComponentJoinedArray_third_sum μ ξ hξ B k]

theorem gaussianComponentJoinedArray_fourth_sum_le
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (hp : 1 ≤ p) (B : Matrix (Fin p) (Fin p) ℝ) {k : ℕ} (hk : k ≠ 0)
    (j : Fin p) :
    (∑ i : Fin (n + k ^ 6), ∫ z,
      gaussianComponentJoinedArray (p := p) (n := n) k i z j ^ 4
      ∂Measure.pi (gaussianComponentJoinedMarginal μ ξ B k)) ≤
      (∑ i : Fin n, ∫ ω, ξ i ω j ^ 4 ∂μ) +
        gaussianComponentFourthMoment B / (k : ℝ) ^ 6 := by
  rw [gaussianComponentJoinedArray_integral_sum μ ξ hξ B k
    (fun x => x j ^ 4) ((measurable_pi_apply j).pow_const 4)]
  apply add_le_add_left
  have h := mul_le_mul_of_nonneg_left
    (gaussianComponentIncrement_fourth_le hp B hk j)
    (Nat.cast_nonneg (k ^ 6) : 0 ≤ ((k ^ 6 : ℕ) : ℝ))
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  convert h using 1
  push_cast
  field_simp [hk'] <;> ring

theorem gaussianComponentJoinedArray_gamma4_le
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (hp : 1 ≤ p) (B : Matrix (Fin p) (Fin p) ℝ) {k : ℕ} (hk : k ≠ 0) :
    gamma4 (Measure.pi (gaussianComponentJoinedMarginal μ ξ B k))
      (gaussianComponentJoinedArray (p := p) (n := n) k) ≤
      gamma4 μ ξ + gaussianComponentFourthMoment B / (k : ℝ) ^ 6 := by
  unfold gamma4
  apply (Finset.fold_max_le _).mpr
  refine ⟨add_nonneg (gamma4_nonneg μ ξ)
    (div_nonneg (gaussianComponentFourthMoment_nonneg B) (by positivity)), ?_⟩
  intro j _
  apply (gaussianComponentJoinedArray_fourth_sum_le μ ξ hξ hp B hk j).trans
  apply add_le_add_right
  exact (Finset.le_fold_max (0 : ℝ)).mpr
    (Or.inr ⟨j, Finset.mem_univ _, le_rfl⟩)

/-- The Gaussian part of the joined covariance is exactly the truncated
base covariance: the `k^6` small increment covariances add to it. -/
theorem gaussianComponentJoinedArray_covariance
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ)
    (B : Matrix (Fin p) (Fin p) ℝ) {k : ℕ} (hk : k ≠ 0) :
    covariance (Measure.pi (gaussianComponentJoinedMarginal μ ξ B k))
      (sumVector (gaussianComponentJoinedArray (p := p) (n := n) k)) =
      covariance μ (sumVector ξ) +
        covariance (gaussianLaw B) (truncateVector ((k : ℝ) ^ 2)) := by
  let ν := gaussianComponentJoinedMarginal μ ξ B k
  letI (i : Fin n ⊕ Fin (k ^ 6)) : IsProbabilityMeasure (ν i) :=
    gaussianComponentJoinedMarginal_isProbability μ ξ h.measurable B k i
  have hjoined := gaussianComponentJoinedArray_boundedIndependent μ ξ h B hk
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  ext j l
  rw [hjoined.covariance_sum,
    gaussianComponentJoinedArray_integral_sum μ ξ h.measurable B k
      (fun x => x j * x l) ((measurable_pi_apply j).mul (measurable_pi_apply l)),
    Matrix.add_apply, h.covariance_sum]
  congr 1
  have heq (x : Vector p) : gaussianComponentIncrement k x j *
      gaussianComponentIncrement k x l = (((k : ℝ) ^ 3)⁻¹) ^ 2 *
        (truncateVector ((k : ℝ) ^ 2) x j * truncateVector ((k : ℝ) ^ 2) x l) := by
    simp only [gaussianComponentIncrement, Pi.smul_apply, smul_eq_mul]
    ring
  simp_rw [heq]
  rw [integral_const_mul]
  simp only [covariance, gaussianComponent_truncated_integral_zero,
    zero_mul, sub_zero]
  push_cast
  field_simp [hk'] <;> ring

theorem gaussianComponentJoinedArray_covariance_error_le
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ)
    (hp : 1 ≤ p) (B : Matrix (Fin p) (Fin p) ℝ) {k : ℕ} (hk : k ≠ 0)
    (j l : Fin p) :
    |covariance (Measure.pi (gaussianComponentJoinedMarginal μ ξ B k))
      (sumVector (gaussianComponentJoinedArray (p := p) (n := n) k)) j l -
        (covariance μ (sumVector ξ) + B * B.transpose) j l| ≤
      gaussianComponentFourthMoment B / (k : ℝ) ^ 4 := by
  rw [gaussianComponentJoinedArray_covariance μ ξ h B hk]
  simp only [Matrix.add_apply, add_sub_add_left_eq_sub, abs_sub_comm]
  have hk' : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
  convert gaussianComponent_covariance_deficit_le hp B (pow_pos hk' 2) j l using 1 <;>
    simp only [gaussianComponentFourthMoment, ← pow_mul]

end

end RectangleCLT
