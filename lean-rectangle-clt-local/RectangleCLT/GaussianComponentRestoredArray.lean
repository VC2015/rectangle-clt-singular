import RectangleCLT.GaussianComponentJoinedMoments
import RectangleCLT.GaussianComponentRestoration

/-!
# The bounded array with exactly restored covariance

The three blocks are the original observations, the truncated small
Gaussian increments, and the symmetric covariance-restoring columns.
All observations are canonical coordinates under their actual product
law. The resulting covariance is exactly the original sum covariance
plus the covariance of the Gaussian component.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RectangleCLT

noncomputable section

def gaussianComponentRestorationError {p : ℕ}
    (B : Matrix (Fin p) (Fin p) ℝ) (k : ℕ) : ℝ :=
  gaussianComponentFourthMoment B / (k : ℝ) ^ 4

theorem gaussianComponentRestorationError_nonneg {p : ℕ}
    (B : Matrix (Fin p) (Fin p) ℝ) (k : ℕ) :
    0 ≤ gaussianComponentRestorationError B k :=
  div_nonneg (gaussianComponentFourthMoment_nonneg B) (by positivity)

def gaussianComponentRestoredIndex (p n k : ℕ) :
    Fin (n + (k ^ 6 + p)) ≃ Fin n ⊕ (Fin (k ^ 6) ⊕ Fin p) :=
  finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv.symm)

def gaussianComponentRestoredMarginal
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (B : Matrix (Fin p) (Fin p) ℝ) (k : ℕ) :
    Fin n ⊕ (Fin (k ^ 6) ⊕ Fin p) → Measure (Vector p) :=
  Sum.elim (fun i => μ.map (ξ i))
    (Sum.elim (fun _ => (gaussianLaw B).map (gaussianComponentIncrement k))
      (restorationColumnMarginal (gaussianComponentRestorationFactor B ((k : ℝ) ^ 2))))

def gaussianComponentRestoredArray {p n : ℕ} (k : ℕ)
    (i : Fin (n + (k ^ 6 + p)))
    (z : Fin n ⊕ (Fin (k ^ 6) ⊕ Fin p) → Vector p) : Vector p :=
  z (gaussianComponentRestoredIndex p n k i)

theorem gaussianComponentRestoredMarginal_isProbability
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (B : Matrix (Fin p) (Fin p) ℝ) (k : ℕ)
    (i : Fin n ⊕ (Fin (k ^ 6) ⊕ Fin p)) :
    IsProbabilityMeasure (gaussianComponentRestoredMarginal μ ξ B k i) := by
  cases i with
  | inl i => exact isProbabilityMeasure_map (hξ i).aemeasurable
  | inr i =>
      cases i with
      | inl i => exact isProbabilityMeasure_map
          (measurable_gaussianComponentIncrement k).aemeasurable
      | inr i => exact restorationColumnMarginal_isProbability _ _

theorem gaussianComponentRestoredFactor_diagonal_le {p : ℕ}
    (hp : 1 ≤ p) (B : Matrix (Fin p) (Fin p) ℝ) {k : ℕ} (hk : k ≠ 0)
    (j : Fin p) :
    (gaussianComponentRestorationFactor B ((k : ℝ) ^ 2) *
      (gaussianComponentRestorationFactor B ((k : ℝ) ^ 2)).transpose) j j ≤
        gaussianComponentRestorationError B k := by
  rw [gaussianComponentRestorationFactor_covariance]
  have hk' : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
  convert gaussianComponentDiscardedCovariance_diagonal_le hp B (pow_pos hk' 2) j using 1 <;>
    simp only [gaussianComponentRestorationError, ← pow_mul]

theorem gaussianComponentRestoredArray_boundedIndependent
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ)
    (hp : 1 ≤ p) (B : Matrix (Fin p) (Fin p) ℝ) {k : ℕ} (hk : k ≠ 0) :
    BoundedIndependentHypotheses
      (Measure.pi (gaussianComponentRestoredMarginal μ ξ B k))
      (gaussianComponentRestoredArray (p := p) (n := n) k)
      (max δ (max (k : ℝ)⁻¹ (Real.sqrt (gaussianComponentRestorationError B k)))) := by
  let ν := gaussianComponentRestoredMarginal μ ξ B k
  letI (i : Fin n ⊕ (Fin (k ^ 6) ⊕ Fin p)) : IsProbabilityMeasure (ν i) :=
    gaussianComponentRestoredMarginal_isProbability μ ξ h.measurable B k i
  let d := max δ (max (k : ℝ)⁻¹ (Real.sqrt (gaussianComponentRestorationError B k)))
  apply gaussianComponentPi_boundedIndependent (gaussianComponentRestoredIndex p n k) ν
    (h.delta_nonneg.trans (le_max_left _ _))
  · intro i j
    cases i with
    | inl i =>
        change (∫ x, x j ∂μ.map (ξ i)) = 0
        rw [integral_map (h.measurable i).aemeasurable
          (measurable_pi_apply j).aestronglyMeasurable]
        exact h.centered i j
    | inr i =>
        cases i with
        | inl i =>
            change (∫ x, x j ∂(gaussianLaw B).map (gaussianComponentIncrement k)) = 0
            rw [integral_map (measurable_gaussianComponentIncrement k).aemeasurable
              (measurable_pi_apply j).aestronglyMeasurable]
            exact gaussianComponentIncrement_integral_zero B k j
        | inr i => exact symmetricColumnLaw_centered _ j
  · intro i
    have hs : MeasurableSet {x : Vector p | ‖x‖ ≤ d} :=
      measurableSet_le measurable_norm measurable_const
    cases i with
    | inl i =>
        change ∀ᵐ x ∂μ.map (ξ i), ‖x‖ ≤ d
        apply (ae_map_iff (h.measurable i).aemeasurable hs).mpr
        filter_upwards [h.bounded i] with ω hω
        exact hω.trans (le_max_left _ _)
    | inr i =>
        cases i with
        | inl i =>
            change ∀ᵐ x ∂(gaussianLaw B).map (gaussianComponentIncrement k), ‖x‖ ≤ d
            apply (ae_map_iff (measurable_gaussianComponentIncrement k).aemeasurable hs).mpr
            exact ae_of_all _ fun x => (norm_gaussianComponentIncrement_le hk x).trans
              ((le_max_left _ _).trans (le_max_right _ _))
        | inr i =>
            apply (symmetricColumnLaw_bounded
              (factor_column_norm_le_sqrt_diagonal_bound _
                (gaussianComponentRestorationError_nonneg B k)
                (gaussianComponentRestoredFactor_diagonal_le hp B hk) i)).mono
            intro x hx
            exact hx.trans ((le_max_right _ _).trans (le_max_right _ _))

theorem gaussianComponentRestoredArray_integral_sum
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (B : Matrix (Fin p) (Fin p) ℝ) (k : ℕ)
    (f : Vector p → ℝ) (hf : Measurable f) :
    (∑ i : Fin (n + (k ^ 6 + p)), ∫ z,
      f (gaussianComponentRestoredArray (p := p) (n := n) k i z)
      ∂Measure.pi (gaussianComponentRestoredMarginal μ ξ B k)) =
      (∑ i : Fin n, ∫ ω, f (ξ i ω) ∂μ) +
        (k ^ 6 : ℕ) * (∫ x, f (gaussianComponentIncrement k x) ∂gaussianLaw B) +
        ∑ r : Fin p, ∫ x, f x ∂restorationColumnMarginal
          (gaussianComponentRestorationFactor B ((k : ℝ) ^ 2)) r := by
  let ν := gaussianComponentRestoredMarginal μ ξ B k
  letI (i : Fin n ⊕ (Fin (k ^ 6) ⊕ Fin p)) : IsProbabilityMeasure (ν i) :=
    gaussianComponentRestoredMarginal_isProbability μ ξ hξ B k i
  have hrow (i : Fin n ⊕ (Fin (k ^ 6) ⊕ Fin p)) :
      (∫ z, f (z i) ∂Measure.pi ν) = ∫ x, f x ∂ν i := by
    have hm := integral_map (μ := Measure.pi ν)
      (measurable_pi_apply i).aemeasurable hf.aestronglyMeasurable
    rw [gaussianComponentPi_map_eval ν] at hm
    exact hm.symm
  change (∑ i, ∫ z, f (z (gaussianComponentRestoredIndex p n k i)) ∂Measure.pi ν) = _
  simp_rw [hrow]
  rw [(gaussianComponentRestoredIndex p n k).sum_comp,
    Fintype.sum_sum_type, Fintype.sum_sum_type]
  change (∑ i : Fin n, ∫ x, f x ∂μ.map (ξ i)) +
    ((∑ _i : Fin (k ^ 6), ∫ x, f x
      ∂(gaussianLaw B).map (gaussianComponentIncrement k)) + _) = _
  simp only [integral_map (measurable_gaussianComponentIncrement k).aemeasurable
    hf.aestronglyMeasurable, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [← add_assoc]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  exact integral_map (hξ i).aemeasurable hf.aestronglyMeasurable

theorem gaussianComponentRestoredArray_third_sum
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (B : Matrix (Fin p) (Fin p) ℝ) (k : ℕ) (j l r : Fin p) :
    (∑ i : Fin (n + (k ^ 6 + p)), ∫ z,
      gaussianComponentRestoredArray (p := p) (n := n) k i z j *
        gaussianComponentRestoredArray (p := p) (n := n) k i z l *
        gaussianComponentRestoredArray (p := p) (n := n) k i z r
      ∂Measure.pi (gaussianComponentRestoredMarginal μ ξ B k)) =
      ∑ i : Fin n, ∫ ω, ξ i ω j * ξ i ω l * ξ i ω r ∂μ := by
  have hm := gaussianComponentRestoredArray_integral_sum μ ξ hξ B k
    (fun x => x j * x l * x r)
    (((measurable_pi_apply j).mul (measurable_pi_apply l)).mul (measurable_pi_apply r))
  simpa only [gaussianComponentIncrement_third_integral_zero,
    restorationColumnMarginal, symmetricColumnLaw_third, mul_zero,
    Finset.sum_const_zero, add_zero] using hm

theorem gaussianComponentRestoredArray_gamma3
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (B : Matrix (Fin p) (Fin p) ℝ) (k : ℕ) :
    gamma3 (Measure.pi (gaussianComponentRestoredMarginal μ ξ B k))
      (gaussianComponentRestoredArray (p := p) (n := n) k) = gamma3 μ ξ := by
  unfold gamma3
  simp_rw [gaussianComponentRestoredArray_third_sum μ ξ hξ B k]

theorem gaussianComponentRestoredArray_fourth_sum_le
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (hp : 1 ≤ p) (B : Matrix (Fin p) (Fin p) ℝ) {k : ℕ} (hk : k ≠ 0)
    (j : Fin p) :
    (∑ i : Fin (n + (k ^ 6 + p)), ∫ z,
      gaussianComponentRestoredArray (p := p) (n := n) k i z j ^ 4
      ∂Measure.pi (gaussianComponentRestoredMarginal μ ξ B k)) ≤
      (∑ i : Fin n, ∫ ω, ξ i ω j ^ 4 ∂μ) +
        gaussianComponentFourthMoment B / (k : ℝ) ^ 6 +
        gaussianComponentRestorationError B k ^ 2 := by
  let A := gaussianComponentRestorationFactor B ((k : ℝ) ^ 2)
  let ε := gaussianComponentRestorationError B k
  have hε : 0 ≤ ε := gaussianComponentRestorationError_nonneg B k
  have hdiag : (A * A.transpose) j j ≤ ε :=
    gaussianComponentRestoredFactor_diagonal_le hp B hk j
  have hdiag0 : 0 ≤ (A * A.transpose) j j := by
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, ← pow_two] using
      Finset.sum_nonneg (fun r (_ : r ∈ (Finset.univ : Finset (Fin p))) =>
        sq_nonneg (A j r))
  have hcorr : (∑ r : Fin p, ∫ x, x j ^ 4 ∂restorationColumnMarginal A r) ≤ ε ^ 2 := by
    simp only [restorationColumnMarginal, symmetricColumnLaw_fourth]
    exact (factor_fourth_sum_le_diagonal_sq A j).trans
      (by simpa only [pow_two] using mul_self_le_mul_self hdiag0 hdiag)
  have hgauss : ((k ^ 6 : ℕ) : ℝ) *
      (∫ x, gaussianComponentIncrement k x j ^ 4 ∂gaussianLaw B) ≤
        gaussianComponentFourthMoment B / (k : ℝ) ^ 6 := by
    have hb := mul_le_mul_of_nonneg_left (gaussianComponentIncrement_fourth_le hp B hk j)
      (Nat.cast_nonneg (k ^ 6) : 0 ≤ ((k ^ 6 : ℕ) : ℝ))
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    convert hb using 1
    push_cast
    field_simp [hk'] <;> ring
  rw [gaussianComponentRestoredArray_integral_sum μ ξ hξ B k
    (fun x => x j ^ 4) ((measurable_pi_apply j).pow_const 4)]
  exact add_le_add (add_le_add_left hgauss _) hcorr

theorem gaussianComponentRestoredArray_gamma4_le
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (hp : 1 ≤ p) (B : Matrix (Fin p) (Fin p) ℝ) {k : ℕ} (hk : k ≠ 0) :
    gamma4 (Measure.pi (gaussianComponentRestoredMarginal μ ξ B k))
      (gaussianComponentRestoredArray (p := p) (n := n) k) ≤
      gamma4 μ ξ + gaussianComponentFourthMoment B / (k : ℝ) ^ 6 +
        gaussianComponentRestorationError B k ^ 2 := by
  unfold gamma4
  apply (Finset.fold_max_le _).mpr
  refine ⟨add_nonneg (add_nonneg (gamma4_nonneg μ ξ)
    (div_nonneg (gaussianComponentFourthMoment_nonneg B) (by positivity))) (sq_nonneg _), ?_⟩
  intro j _
  apply (gaussianComponentRestoredArray_fourth_sum_le μ ξ hξ hp B hk j).trans
  apply add_le_add_right
  apply add_le_add_right
  exact (Finset.le_fold_max (0 : ℝ)).mpr
    (Or.inr ⟨j, Finset.mem_univ _, le_rfl⟩)

theorem gaussianComponentRestoredArray_covariance
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ)
    (hp : 1 ≤ p) (B : Matrix (Fin p) (Fin p) ℝ) {k : ℕ} (hk : k ≠ 0) :
    covariance (Measure.pi (gaussianComponentRestoredMarginal μ ξ B k))
      (sumVector (gaussianComponentRestoredArray (p := p) (n := n) k)) =
      covariance μ (sumVector ξ) + B * B.transpose := by
  let ν := gaussianComponentRestoredMarginal μ ξ B k
  letI (i : Fin n ⊕ (Fin (k ^ 6) ⊕ Fin p)) : IsProbabilityMeasure (ν i) :=
    gaussianComponentRestoredMarginal_isProbability μ ξ h.measurable B k i
  have hrestored := gaussianComponentRestoredArray_boundedIndependent μ ξ h hp B hk
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  let A := gaussianComponentRestorationFactor B ((k : ℝ) ^ 2)
  have hgauss (j l : Fin p) : ((k ^ 6 : ℕ) : ℝ) *
      (∫ x, gaussianComponentIncrement k x j * gaussianComponentIncrement k x l
        ∂gaussianLaw B) =
      covariance (gaussianLaw B) (truncateVector ((k : ℝ) ^ 2)) j l := by
    have heq (x : Vector p) : gaussianComponentIncrement k x j *
        gaussianComponentIncrement k x l = (((k : ℝ) ^ 3)⁻¹) ^ 2 *
          (truncateVector ((k : ℝ) ^ 2) x j * truncateVector ((k : ℝ) ^ 2) x l) := by
      simp only [gaussianComponentIncrement, Pi.smul_apply, smul_eq_mul]
      ring
    simp_rw [heq]
    rw [integral_const_mul]
    simp only [covariance, gaussianComponent_truncated_integral_zero, zero_mul, sub_zero]
    push_cast
    field_simp [hk'] <;> ring
  have hcorr (j l : Fin p) :
      (∑ r : Fin p, ∫ x, x j * x l ∂restorationColumnMarginal A r) =
        gaussianComponentDiscardedCovariance B ((k : ℝ) ^ 2) j l := by
    simp only [restorationColumnMarginal, symmetricColumnLaw_second]
    change (A * A.transpose) j l = _
    rw [gaussianComponentRestorationFactor_covariance]
  ext j l
  rw [hrestored.covariance_sum,
    gaussianComponentRestoredArray_integral_sum μ ξ h.measurable B k
      (fun x => x j * x l) ((measurable_pi_apply j).mul (measurable_pi_apply l)),
    hgauss, hcorr, gaussianComponentDiscardedCovariance_eq]
  simp only [Matrix.add_apply, Matrix.sub_apply, h.covariance_sum]
  ring

theorem sumVector_gaussianComponentRestoredArray {p n : ℕ} (k : ℕ)
    (z : Fin n ⊕ (Fin (k ^ 6) ⊕ Fin p) → Vector p) :
    sumVector (gaussianComponentRestoredArray (p := p) (n := n) k) z =
      ((∑ i : Fin n, z (.inl i)) + ∑ i : Fin (k ^ 6), z (.inr (.inl i))) +
        ∑ r : Fin p, z (.inr (.inr r)) := by
  unfold sumVector gaussianComponentRestoredArray
  rw [(gaussianComponentRestoredIndex p n k).sum_comp,
    Fintype.sum_sum_type, Fintype.sum_sum_type, add_assoc]

end

end RectangleCLT
