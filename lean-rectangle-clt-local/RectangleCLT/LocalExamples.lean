import RectangleCLT.LocalCovariance

/-! A concrete singular covariance admitted by the local assumptions: the
five-coordinate regular simplex has unit diagonal and four-coordinate lower
bound one quarter, while its all-ones vector is in the kernel. -/

open scoped BigOperators

namespace RectangleCLT.LocalExamples

/-- The five-coordinate simplex correlation matrix, with diagonal one and every
off-diagonal entry minus one quarter. -/
noncomputable def simplexMatrix : Matrix (Fin 5) (Fin 5) ℝ :=
  fun j k => (if j = k then (5 / 4 : ℝ) else 0) - 1 / 4

theorem simplexMatrix_diagonal (j : Fin 5) : simplexMatrix j j = 1 := by
  norm_num [simplexMatrix]

theorem simplexMatrix_offDiagonal (j k : Fin 5) (hjk : j ≠ k) :
    simplexMatrix j k = -1 / 4 := by
  norm_num [simplexMatrix, hjk]

/-- Exact quadratic form of the simplex correlation matrix. -/
theorem simplexMatrix_quadratic (v : Fin 5 → ℝ) :
    matrixQuadratic simplexMatrix v =
      (5 * vectorNormSq v - (∑ j, v j) ^ 2) / 4 := by
  have hterm (j k : Fin 5) :
      v j * simplexMatrix j k * v k =
        (if j = k then (5 / 4 : ℝ) * v j ^ 2 else 0) - (1 / 4 : ℝ) * v j * v k := by
    by_cases hjk : j = k
    · subst k
      simp only [simplexMatrix, ite_true]
      ring
    · simp only [simplexMatrix, hjk, if_false]
      ring
  unfold matrixQuadratic
  simp_rw [hterm, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  unfold vectorNormSq
  ring

theorem simplexMatrix_posSemidef : simplexMatrix.PosSemidef := by
  constructor
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    ext j k
    simp [simplexMatrix, eq_comm]
  · intro v
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 5))
      (fun _ => (1 : ℝ)) v
    have hsum : (∑ j, v j) ^ 2 ≤ 5 * vectorNormSq v := by
      simpa [vectorNormSq] using hcs
    have hquad : 0 ≤ matrixQuadratic simplexMatrix v := by
      rw [simplexMatrix_quadratic]
      linarith
    simpa [matrixQuadratic, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc] using hquad

private theorem sum_on_support {p : ℕ} (v : Fin p → ℝ) :
    (∑ j ∈ coordinateSupport v, v j) = ∑ j, v j := by
  classical
  unfold coordinateSupport
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : v j = 0 <;> simp [hj]

private theorem sum_sq_on_support {p : ℕ} (v : Fin p → ℝ) :
    (∑ j ∈ coordinateSupport v, v j ^ 2) = vectorNormSq v := by
  classical
  unfold coordinateSupport vectorNormSq
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : v j = 0 <;> simp [hj]

/-- Cauchy–Schwarz needs only the number of active coordinates. -/
theorem sparse_sum_sq_le {p r : ℕ} (v : Fin p → ℝ)
    (hs : (coordinateSupport v).card ≤ r) :
    (∑ j, v j) ^ 2 ≤ (r : ℝ) * vectorNormSq v := by
  classical
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (coordinateSupport v)
    (fun _ => (1 : ℝ)) v
  have hsum : (∑ j, v j) ^ 2 ≤ ((coordinateSupport v).card : ℝ) * vectorNormSq v := by
    simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one,
      sum_on_support, sum_sq_on_support] using hcs
  have hcard : ((coordinateSupport v).card : ℝ) ≤ r := by exact_mod_cast hs
  exact hsum.trans (mul_le_mul_of_nonneg_right hcard (vectorNormSq_nonneg v))

/-- Every coordinate group of size at most four has covariance lower bound
one quarter, despite the singular full five-coordinate covariance. -/
theorem simplexMatrix_local_four : LocalCovarianceLower simplexMatrix 4 (1 / 4) := by
  intro v hs
  have hcs := sparse_sum_sq_le v hs
  rw [simplexMatrix_quadratic]
  norm_num at hcs ⊢
  linarith

theorem simplexMatrix_a4_ge : (1 / 4 : ℝ) ≤ a4 simplexMatrix :=
  le_localEigenvalue (by decide : 0 < 5) (by decide : 0 < 4) simplexMatrix_local_four

theorem simplexMatrix_a4_pos : 0 < a4 simplexMatrix :=
  (by norm_num : (0 : ℝ) < 1 / 4).trans_le simplexMatrix_a4_ge

theorem allOnes_ne_zero : (fun _ : Fin 5 => (1 : ℝ)) ≠ 0 := by
  intro h
  have hh := congrFun h 0
  norm_num at hh

theorem simplexMatrix_allOnes_kernel :
    simplexMatrix.mulVec (fun _ : Fin 5 => (1 : ℝ)) = 0 := by
  funext j
  simp [Matrix.mulVec, dotProduct, simplexMatrix, Finset.sum_sub_distrib]
  norm_num

/-- In particular, the example admits no positive lower bound on the full
quadratic form. This is stronger than merely omitting such a hypothesis. -/
theorem simplexMatrix_no_positive_global_lower (a : ℝ) (ha : 0 < a) :
    ¬(∀ v : Fin 5 → ℝ, a * vectorNormSq v ≤ matrixQuadratic simplexMatrix v) := by
  intro h
  have hh := h (fun _ => 1)
  rw [simplexMatrix_quadratic] at hh
  norm_num [vectorNormSq] at hh
  linarith

/-- A concrete witness that the local covariance assumptions allow a singular
full covariance matrix. -/
theorem singular_local_covariance_example :
    ∃ Q : Matrix (Fin 5) (Fin 5) ℝ, Q.PosSemidef ∧ (∀ j, Q j j = 1) ∧
      0 < a4 Q ∧ ∃ v : Fin 5 → ℝ, v ≠ 0 ∧ Q.mulVec v = 0 :=
  ⟨simplexMatrix, simplexMatrix_posSemidef, simplexMatrix_diagonal,
    simplexMatrix_a4_pos, fun _ => 1, allOnes_ne_zero, simplexMatrix_allOnes_kernel⟩

end RectangleCLT.LocalExamples
