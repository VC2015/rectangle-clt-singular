import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Exact joint covariance restoration, including singular block matrices.
The cross blocks are retained. A finite two-point clipping example shows why
the difference of the original and clipped covariances need not be positive
semidefinite, so it cannot generally be supplied by independent added noise. -/

open scoped BigOperators Matrix ComplexOrder

namespace RectangleCLT.Companion

noncomputable section

set_option autoImplicit false

abbrev JointIndex (p : ℕ) := Fin p ⊕ Fin p

def covarianceBlock11 {p : ℕ} (Q : Matrix (JointIndex p) (JointIndex p) ℝ) :
    Matrix (Fin p) (Fin p) ℝ := Q.submatrix Sum.inl Sum.inl

def covarianceBlock12 {p : ℕ} (Q : Matrix (JointIndex p) (JointIndex p) ℝ) :
    Matrix (Fin p) (Fin p) ℝ := Q.submatrix Sum.inl Sum.inr

def covarianceBlock21 {p : ℕ} (Q : Matrix (JointIndex p) (JointIndex p) ℝ) :
    Matrix (Fin p) (Fin p) ℝ := Q.submatrix Sum.inr Sum.inl

def covarianceBlock22 {p : ℕ} (Q : Matrix (JointIndex p) (JointIndex p) ℝ) :
    Matrix (Fin p) (Fin p) ℝ := Q.submatrix Sum.inr Sum.inr

/-- The covariance of the sum projection of a joint vector. -/
def restoredCovariance {p : ℕ} (Q : Matrix (JointIndex p) (JointIndex p) ℝ) :
    Matrix (Fin p) (Fin p) ℝ :=
  covarianceBlock11 Q + covarianceBlock12 Q + covarianceBlock21 Q + covarianceBlock22 Q

@[simp] theorem restoredCovariance_apply {p : ℕ}
    (Q : Matrix (JointIndex p) (JointIndex p) ℝ) (j k : Fin p) :
    restoredCovariance Q j k =
      Q (Sum.inl j) (Sum.inl k) + Q (Sum.inl j) (Sum.inr k) +
        Q (Sum.inr j) (Sum.inl k) + Q (Sum.inr j) (Sum.inr k) := rfl

/-- The two components use columns of one common Gaussian factor. -/
def leftJointFactor {p : ℕ} (B : Matrix (JointIndex p) (JointIndex p) ℝ) :
    Matrix (Fin p) (JointIndex p) ℝ := B.submatrix Sum.inl id

def rightJointFactor {p : ℕ} (B : Matrix (JointIndex p) (JointIndex p) ℝ) :
    Matrix (Fin p) (JointIndex p) ℝ := B.submatrix Sum.inr id

def sumJointFactor {p : ℕ} (B : Matrix (JointIndex p) (JointIndex p) ℝ) :
    Matrix (Fin p) (JointIndex p) ℝ := leftJointFactor B + rightJointFactor B

/-- Every positive semidefinite joint covariance has a real factor. No
positive eigenvalue, nonsingularity, or inverse is required. -/
theorem jointCovariance_factor_exists {p : ℕ}
    (Q : Matrix (JointIndex p) (JointIndex p) ℝ) (hQ : Q.PosSemidef) :
    ∃ B : Matrix (JointIndex p) (JointIndex p) ℝ, B * B.transpose = Q := by
  refine ⟨hQ.sqrt, ?_⟩
  have hsymmetric : hQ.sqrt.transpose = hQ.sqrt := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using
      hQ.posSemidef_sqrt.isHermitian
  rw [hsymmetric]
  exact hQ.sqrt_mul_self

private theorem rowFactor_cross_gram {p : ℕ}
    (B : Matrix (JointIndex p) (JointIndex p) ℝ)
    (f g : Fin p → JointIndex p) :
    (B.submatrix f id) * (B.submatrix g id).transpose =
      (B * B.transpose).submatrix f g := by
  rfl

/-- Summing the projected factors retains both cross-covariance blocks. -/
theorem sumJointFactor_gram {p : ℕ}
    (B : Matrix (JointIndex p) (JointIndex p) ℝ) :
    sumJointFactor B * (sumJointFactor B).transpose =
      restoredCovariance (B * B.transpose) := by
  ext j k
  simp only [sumJointFactor, leftJointFactor, rightJointFactor, restoredCovariance,
    covarianceBlock11, covarianceBlock12, covarianceBlock21, covarianceBlock22,
    Matrix.mul_apply, Matrix.transpose_apply, Matrix.add_apply, Matrix.submatrix_apply,
    id_eq, add_mul, mul_add, Finset.sum_add_distrib]
  ring

/-- Exact restoration data for a joint covariance. The marginal and cross
Grams all arise from the same factor, permitting dependence of the two blocks. -/
theorem jointCovariance_restoration_exists {p : ℕ}
    (Q : Matrix (JointIndex p) (JointIndex p) ℝ) (hQ : Q.PosSemidef) :
    ∃ L R : Matrix (Fin p) (JointIndex p) ℝ,
      L * L.transpose = covarianceBlock11 Q ∧
      L * R.transpose = covarianceBlock12 Q ∧
      R * L.transpose = covarianceBlock21 Q ∧
      R * R.transpose = covarianceBlock22 Q ∧
      (L + R) * (L + R).transpose = restoredCovariance Q := by
  obtain ⟨B, hB⟩ := jointCovariance_factor_exists Q hQ
  refine ⟨leftJointFactor B, rightJointFactor B, ?_, ?_, ?_, ?_, ?_⟩
  · change (B.submatrix Sum.inl id) * (B.submatrix Sum.inl id).transpose = _
    rw [rowFactor_cross_gram, hB]
    rfl
  · change (B.submatrix Sum.inl id) * (B.submatrix Sum.inr id).transpose = _
    rw [rowFactor_cross_gram, hB]
    rfl
  · change (B.submatrix Sum.inr id) * (B.submatrix Sum.inl id).transpose = _
    rw [rowFactor_cross_gram, hB]
    rfl
  · change (B.submatrix Sum.inr id) * (B.submatrix Sum.inr id).transpose = _
    rw [rowFactor_cross_gram, hB]
    rfl
  · simpa only [sumJointFactor, hB] using sumJointFactor_gram B

/-- In particular, the sum covariance is positive semidefinite even if the
joint covariance has a nontrivial kernel. -/
theorem restoredCovariance_posSemidef {p : ℕ}
    (Q : Matrix (JointIndex p) (JointIndex p) ℝ) (hQ : Q.PosSemidef) :
    (restoredCovariance Q).PosSemidef := by
  obtain ⟨L, R, _, _, _, _, hsum⟩ := jointCovariance_restoration_exists Q hQ
  rw [← hsum]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_self_mul_conjTranspose (L + R)

namespace ClippingCounterexample

/-- Scalar clipping at level one. -/
def clipOne (x : ℝ) : ℝ := max (-1) (min 1 x)

def originalVector : Fin 2 → ℝ := ![2, 1]
def clippedVector : Fin 2 → ℝ := ![1, 1]

def signedVector (v : Fin 2 → ℝ) (b : Bool) : Fin 2 → ℝ := if b then v else -v

/-- The covariance of the centered uniform two-point vector `±v`, written
as its literal finite average. -/
def twoPointCovariance (v : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun j k => (1 / 2 : ℝ) * ∑ b : Bool, signedVector v b j * signedVector v b k

theorem signedVector_centered (v : Fin 2 → ℝ) (j : Fin 2) :
    (1 / 2 : ℝ) * ∑ b : Bool, signedVector v b j = 0 := by
  simp only [Fintype.sum_bool, signedVector, Bool.false_eq_true, ↓reduceIte, Pi.neg_apply]
  ring

theorem twoPointCovariance_eq_outer (v : Fin 2 → ℝ) :
    twoPointCovariance v = fun j k => v j * v k := by
  ext j k
  simp only [twoPointCovariance, Fintype.sum_bool, signedVector,
    Bool.false_eq_true, ↓reduceIte, Pi.neg_apply]
  ring

theorem clipped_signedVector (b : Bool) (j : Fin 2) :
    clipOne (signedVector originalVector b j) = signedVector clippedVector b j := by
  cases b <;> fin_cases j <;> norm_num [clipOne, signedVector, originalVector, clippedVector]

def originalCovariance : Matrix (Fin 2) (Fin 2) ℝ := ![![4, 2], ![2, 1]]
def clippedCovariance : Matrix (Fin 2) (Fin 2) ℝ := ![![1, 1], ![1, 1]]

theorem originalCovariance_eq_twoPoint :
    originalCovariance = twoPointCovariance originalVector := by
  rw [twoPointCovariance_eq_outer]
  ext j k
  fin_cases j <;> fin_cases k <;> norm_num [originalCovariance, originalVector]

theorem clippedCovariance_eq_twoPoint :
    clippedCovariance = twoPointCovariance clippedVector := by
  rw [twoPointCovariance_eq_outer]
  ext j k
  fin_cases j <;> fin_cases k <;> norm_num [clippedCovariance, clippedVector]

private theorem outer_posSemidef (v : Fin 2 → ℝ) :
    (twoPointCovariance v).PosSemidef := by
  let B : Matrix (Fin 2) (Fin 1) ℝ := fun j _ => v j
  have hB : B * B.transpose = twoPointCovariance v := by
    rw [twoPointCovariance_eq_outer]
    ext j k
    simp [Matrix.mul_apply, Matrix.transpose_apply, B]
  rw [← hB]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_self_mul_conjTranspose B

theorem originalCovariance_posSemidef : originalCovariance.PosSemidef := by
  rw [originalCovariance_eq_twoPoint]
  exact outer_posSemidef _

theorem clippedCovariance_posSemidef : clippedCovariance.PosSemidef := by
  rw [clippedCovariance_eq_twoPoint]
  exact outer_posSemidef _

/-- Independent added Gaussian noise cannot generally repair the clipped
covariance: even this actual two-point example has an indefinite difference. -/
theorem covariance_difference_not_posSemidef :
    ¬(originalCovariance - clippedCovariance).PosSemidef := by
  intro h
  have hh := h.2 ![1, -4]
  norm_num [originalCovariance, clippedCovariance, Matrix.mulVec, dotProduct,
    Matrix.sub_apply, Fin.sum_univ_succ] at hh

/-- There is no positive semidefinite additive covariance restoring this
clipped covariance to the original one. The joint block construction above
is necessary to retain the cross terms. -/
theorem no_independent_covariance_restoration :
    ¬∃ D : Matrix (Fin 2) (Fin 2) ℝ,
      D.PosSemidef ∧ clippedCovariance + D = originalCovariance := by
  rintro ⟨D, hD, heq⟩
  have hdiff : originalCovariance - clippedCovariance = D := by
    rw [← heq]
    abel
  exact covariance_difference_not_posSemidef (hdiff.symm ▸ hD)

end ClippingCounterexample

end
end RectangleCLT.Companion
