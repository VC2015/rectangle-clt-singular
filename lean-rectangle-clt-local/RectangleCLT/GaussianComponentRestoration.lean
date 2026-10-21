import RectangleCLT.GaussianComponentApproximation
import RectangleCLT.GaussianComponentJoinedArray
import RectangleCLT.GaussianComparisonCovariance

/-!
# Exact restoration of the covariance discarded by Gaussian truncation

Whole-vector truncation of a centered Gaussian is symmetric. Its lost
covariance is therefore the positive semidefinite tail second-moment
matrix. Independent symmetric two-point column observations restore this
covariance exactly. Their aggregate third moments are zero, their fourth
moments vanish with the discarded covariance, and their total displacement
is deterministically small. This avoids changing the covariance proxy or
normalizing the original coordinates.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RectangleCLT

noncomputable section

def gaussianComponentDiscardedCovariance {p : ℕ}
    (B : Matrix (Fin p) (Fin p) ℝ) (u : ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  fun j k => ∫ x : Vector p, {x | ‖x‖ ≤ u}ᶜ.indicator
    (fun x => x j * x k) x ∂gaussianLaw B

theorem gaussianComponentDiscardedCovariance_eq {p : ℕ}
    (B : Matrix (Fin p) (Fin p) ℝ) (u : ℝ) :
    gaussianComponentDiscardedCovariance B u =
      B * B.transpose - covariance (gaussianLaw B) (truncateVector u) := by
  ext j k
  have h := truncation_covariance_deficit (μ := gaussianLaw B) measurable_id
    (gaussianLaw_integrable_coordinate_product B)
    (gaussianLaw_integral_coordinate B) u j k
  rw [covariance_gaussianLaw, gaussianComponent_truncationMean_eq_zero] at h
  simpa only [gaussianComponentDiscardedCovariance, Pi.zero_apply,
    zero_mul, add_zero, Matrix.sub_apply] using h.symm

theorem gaussianComponentDiscardedCovariance_posSemidef {p : ℕ}
    (B : Matrix (Fin p) (Fin p) ℝ) (u : ℝ) :
    (gaussianComponentDiscardedCovariance B u).PosSemidef := by
  classical
  let E : Set (Vector p) := {x | ‖x‖ ≤ u}ᶜ
  have hE : MeasurableSet E :=
    (measurableSet_le measurable_norm measurable_const).compl
  have hI (j k : Fin p) :
      Integrable (E.indicator (fun x : Vector p => x j * x k)) (gaussianLaw B) :=
    (gaussianLaw_integrable_coordinate_product B j k).indicator hE
  constructor
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    ext j k
    simp only [Matrix.transpose_apply, gaussianComponentDiscardedCovariance, mul_comm]
  · intro v
    have hsum : matrixQuadratic (gaussianComponentDiscardedCovariance B u) v =
        ∫ x : Vector p, E.indicator (fun x => (∑ j, v j * x j) ^ 2) x
          ∂gaussianLaw B := by
      let F : Fin p → Fin p → Vector p → ℝ := fun j k x =>
        v j * E.indicator (fun x => x j * x k) x * v k
      have hF (j k : Fin p) : Integrable (F j k) (gaussianLaw B) :=
        ((hI j k).const_mul (v j)).mul_const (v k)
      calc
        _ = ∑ j, ∑ k, ∫ x, F j k x ∂gaussianLaw B := by
          simp only [matrixQuadratic, gaussianComponentDiscardedCovariance,
            F, E, integral_mul_const, integral_const_mul]
        _ = ∫ x, ∑ j, ∑ k, F j k x ∂gaussianLaw B := by
          rw [integral_finset_sum Finset.univ (fun j _ =>
            integrable_finset_sum Finset.univ (fun k _ => hF j k))]
          apply Finset.sum_congr rfl
          intro j _
          rw [integral_finset_sum Finset.univ (fun k _ => hF j k)]
        _ = _ := by
          apply integral_congr_ae
          exact ae_of_all _ fun x => by
            by_cases hx : x ∈ E
            · simp only [F, Set.indicator_of_mem hx, pow_two,
                Finset.sum_mul, Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              apply Finset.sum_congr rfl
              intro k _
              ring
            · simp only [F, Set.indicator_of_not_mem hx, mul_zero, zero_mul,
                Finset.sum_const_zero]
    have hquad : 0 ≤ matrixQuadratic (gaussianComponentDiscardedCovariance B u) v := by
      rw [hsum]
      exact integral_nonneg fun x => by
        by_cases hx : x ∈ E <;> simp [hx, sq_nonneg]
    simpa only [matrixQuadratic, Matrix.mulVec, dotProduct, Finset.mul_sum,
      star_trivial, mul_assoc] using hquad

theorem gaussianComponentDiscardedCovariance_diagonal_le {p : ℕ}
    (hp : 1 ≤ p) (B : Matrix (Fin p) (Fin p) ℝ) {u : ℝ} (hu : 0 < u)
    (j : Fin p) :
    gaussianComponentDiscardedCovariance B u j j ≤
      gaussianComponentFourthMoment B / u ^ 2 := by
  rw [gaussianComponentDiscardedCovariance_eq]
  exact (le_abs_self _).trans (gaussianComponent_covariance_deficit_le hp B hu j j)

/-- A concrete square root of the discarded covariance. -/
def gaussianComponentRestorationFactor {p : ℕ}
    (B : Matrix (Fin p) (Fin p) ℝ) (u : ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  (gaussianComponentDiscardedCovariance_posSemidef B u).sqrt

theorem gaussianComponentRestorationFactor_covariance {p : ℕ}
    (B : Matrix (Fin p) (Fin p) ℝ) (u : ℝ) :
    gaussianComponentRestorationFactor B u *
      (gaussianComponentRestorationFactor B u).transpose =
        gaussianComponentDiscardedCovariance B u := by
  let h := gaussianComponentDiscardedCovariance_posSemidef B u
  have hs : h.sqrt.transpose = h.sqrt := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
      using h.posSemidef_sqrt.isHermitian
  change h.sqrt * h.sqrt.transpose = _
  rw [hs]
  exact h.sqrt_mul_self

theorem factor_entry_sq_le_diagonal {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (j k : Fin p) :
    A j k ^ 2 ≤ (A * A.transpose) j j := by
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, pow_two] using
    (Finset.single_le_sum (fun i _ => sq_nonneg (A j i)) (Finset.mem_univ k))

theorem factor_column_norm_le_sqrt_diagonal_bound {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) {ε : ℝ}
    (_hε : 0 ≤ ε) (hdiag : ∀ j, (A * A.transpose) j j ≤ ε) (k : Fin p) :
    ‖fun j => A j k‖ ≤ Real.sqrt ε := by
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg ε)).mpr
  intro j
  rw [Real.norm_eq_abs]
  apply Real.le_sqrt_of_sq_le
  simpa only [sq_abs] using (factor_entry_sq_le_diagonal A j k).trans (hdiag j)

/-- The sum of column fourth powers is controlled by the square of one
covariance diagonal, without a dimension factor. -/
theorem factor_fourth_sum_le_diagonal_sq {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (j : Fin p) :
    (∑ k, A j k ^ 4) ≤ ((A * A.transpose) j j) ^ 2 := by
  have hdiag : 0 ≤ (A * A.transpose) j j := by
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, ← pow_two] using
      Finset.sum_nonneg (fun k (_ : k ∈ (Finset.univ : Finset (Fin p))) => sq_nonneg (A j k))
  calc
    _ ≤ ∑ k, (A * A.transpose) j j * A j k ^ 2 := by
      apply Finset.sum_le_sum
      intro k _
      nlinarith [mul_le_mul_of_nonneg_right (factor_entry_sq_le_diagonal A j k)
        (sq_nonneg (A j k))]
    _ = (A * A.transpose) j j * ∑ k, A j k ^ 2 := by rw [Finset.mul_sum]
    _ = ((A * A.transpose) j j) ^ 2 := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, pow_two]

/-- The centered symmetric two-point law at one factor column. -/
def symmetricColumnLaw {p : ℕ} (c : Vector p) : Measure (Vector p) :=
  (2 : ℝ≥0∞)⁻¹ • Measure.dirac c + (2 : ℝ≥0∞)⁻¹ • Measure.dirac (-c)

instance symmetricColumnLaw_isProbability {p : ℕ} (c : Vector p) :
    IsProbabilityMeasure (symmetricColumnLaw c) where
  measure_univ := by simpa [symmetricColumnLaw] using ENNReal.inv_two_add_inv_two

theorem integrable_symmetricColumnLaw {p : ℕ} (c : Vector p) (f : Vector p → ℝ) :
    Integrable f (symmetricColumnLaw c) := by
  exact Integrable.add_measure
    (integrable_dirac.smul_measure (by norm_num))
    (integrable_dirac.smul_measure (by norm_num))

theorem integral_symmetricColumnLaw {p : ℕ} (c : Vector p) (f : Vector p → ℝ) :
    (∫ x, f x ∂symmetricColumnLaw c) = (f c + f (-c)) / 2 := by
  rw [symmetricColumnLaw, integral_add_measure
    (integrable_dirac.smul_measure (by norm_num))
    (integrable_dirac.smul_measure (by norm_num))]
  simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_inv,
    ENNReal.toReal_ofNat, smul_eq_mul]
  ring

theorem symmetricColumnLaw_centered {p : ℕ} (c : Vector p) (j : Fin p) :
    (∫ x, x j ∂symmetricColumnLaw c) = 0 := by
  rw [integral_symmetricColumnLaw]
  simp

theorem symmetricColumnLaw_second {p : ℕ} (c : Vector p) (j k : Fin p) :
    (∫ x, x j * x k ∂symmetricColumnLaw c) = c j * c k := by
  rw [integral_symmetricColumnLaw]
  simp only [Pi.neg_apply]
  ring

theorem symmetricColumnLaw_third {p : ℕ} (c : Vector p) (j k l : Fin p) :
    (∫ x, x j * x k * x l ∂symmetricColumnLaw c) = 0 := by
  rw [integral_symmetricColumnLaw]
  simp only [Pi.neg_apply]
  ring

theorem symmetricColumnLaw_fourth {p : ℕ} (c : Vector p) (j : Fin p) :
    (∫ x, x j ^ 4 ∂symmetricColumnLaw c) = c j ^ 4 := by
  rw [integral_symmetricColumnLaw]
  simp only [Pi.neg_apply]
  ring

theorem symmetricColumnLaw_bounded {p : ℕ} {c : Vector p} {δ : ℝ}
    (hc : ‖c‖ ≤ δ) : ∀ᵐ x ∂symmetricColumnLaw c, ‖x‖ ≤ δ := by
  rw [symmetricColumnLaw, ae_add_measure_iff]
  constructor
  · apply Measure.ae_smul_measure
    filter_upwards [ae_eq_dirac (id : Vector p → Vector p)] with x hx
    change x = c at hx
    simpa only [hx] using hc
  · apply Measure.ae_smul_measure
    filter_upwards [ae_eq_dirac (id : Vector p → Vector p)] with x hx
    change x = -c at hx
    simpa only [hx, norm_neg] using hc

def restorationColumnMarginal {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (k : Fin p) : Measure (Vector p) :=
  symmetricColumnLaw (fun j => A j k)

instance restorationColumnMarginal_isProbability {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (k : Fin p) :
    IsProbabilityMeasure (restorationColumnMarginal A k) :=
  symmetricColumnLaw_isProbability _

/-- Independent bounded observations whose actual sum has covariance
`A*A.transpose`. Each observation is symmetric, so every third moment is
exactly zero. -/
theorem restorationColumnArray_boundedIndependent {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hdiag : ∀ j, (A * A.transpose) j j ≤ ε) :
    BoundedIndependentHypotheses (Measure.pi (restorationColumnMarginal A))
      (fun k (z : Fin p → Vector p) => z k) (Real.sqrt ε) := by
  apply gaussianComponentPi_boundedIndependent (Equiv.refl (Fin p))
    (restorationColumnMarginal A) (Real.sqrt_nonneg ε)
  · intro k j
    exact symmetricColumnLaw_centered _ j
  · intro k
    exact symmetricColumnLaw_bounded
      (factor_column_norm_le_sqrt_diagonal_bound A hε hdiag k)

end

end RectangleCLT
