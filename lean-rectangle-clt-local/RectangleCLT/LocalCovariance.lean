import RectangleCLT.SmootherSecondDerivatives
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Finset.Fold
import Mathlib.LinearAlgebra.Matrix.Trace

/-! Intrinsic local covariance parameters and the pair-gap contraction of the
explicit smoother covariance. No positive lower bound on the full covariance
matrix is assumed in the local statements. -/

open scoped BigOperators

namespace RectangleCLT

noncomputable def vectorNormSq {p : ℕ} (v : Fin p → ℝ) : ℝ := ∑ j, v j ^ 2

noncomputable def matrixQuadratic {p : ℕ}
    (Q : Matrix (Fin p) (Fin p) ℝ) (v : Fin p → ℝ) : ℝ :=
  ∑ j, ∑ k, v j * Q j k * v k

noncomputable def coordinateSupport {p : ℕ} (v : Fin p → ℝ) : Finset (Fin p) := by
  classical
  exact Finset.univ.filter (fun j => v j ≠ 0)

/-- A scaled lower bound tested only on vectors supported on at most `r`
coordinates. The full covariance matrix is permitted to be singular. -/
def LocalCovarianceLower {p : ℕ} (Q : Matrix (Fin p) (Fin p) ℝ)
    (r : ℕ) (a : ℝ) : Prop :=
  ∀ v : Fin p → ℝ, (coordinateSupport v).card ≤ r →
    a * vectorNormSq v ≤ matrixQuadratic Q v

/-- Sparse Rayleigh quotients are an intrinsic characterization of the least
principal-submatrix eigenvalue over coordinate sets of size at most `r`. -/
noncomputable def localRayleighValues {p : ℕ}
    (Q : Matrix (Fin p) (Fin p) ℝ) (r : ℕ) : Set ℝ :=
  {q | ∃ v : Fin p → ℝ, v ≠ 0 ∧ (coordinateSupport v).card ≤ r ∧
    q = matrixQuadratic Q v / vectorNormSq v}

/-- The intrinsic local covariance parameter. For `p,r ≥ 1` this is the
infimum of nonempty sparse Rayleigh quotients. -/
noncomputable def localEigenvalue {p : ℕ}
    (Q : Matrix (Fin p) (Fin p) ℝ) (r : ℕ) : ℝ := sInf (localRayleighValues Q r)

noncomputable def a3 {p : ℕ} (Q : Matrix (Fin p) (Fin p) ℝ) : ℝ := localEigenvalue Q 3
noncomputable def a4 {p : ℕ} (Q : Matrix (Fin p) (Fin p) ℝ) : ℝ := localEigenvalue Q 4

/-- Maximum absolute off-diagonal entry. The maximum of an empty off-diagonal
family is zero, giving pair gap one in dimension one. -/
noncomputable def maxOffDiagonal {p : ℕ} (Q : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  (Finset.univ : Finset (Fin p × Fin p)).fold max 0
    (fun jk => if jk.1 = jk.2 then 0 else |Q jk.1 jk.2|)

noncomputable def pairGap {p : ℕ} (Q : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  1 - maxOffDiagonal Q

theorem vectorNormSq_nonneg {p : ℕ} (v : Fin p → ℝ) : 0 ≤ vectorNormSq v :=
  Finset.sum_nonneg (fun _j _ => sq_nonneg _)

theorem vectorNormSq_pos {p : ℕ} {v : Fin p → ℝ} (hv : v ≠ 0) : 0 < vectorNormSq v := by
  classical
  have h : ∃ j, v j ≠ 0 := by
    by_contra h
    push_neg at h
    apply hv
    funext j
    exact h j
  obtain ⟨j, hj⟩ := h
  exact (sq_pos_of_ne_zero hj).trans_le
    (Finset.single_le_sum (fun k _ => sq_nonneg (v k)) (Finset.mem_univ j))

theorem LocalCovarianceLower.mono {p : ℕ} {Q : Matrix (Fin p) (Fin p) ℝ}
    {r s : ℕ} {a : ℝ} (h : LocalCovarianceLower Q s a) (hrs : r ≤ s) :
    LocalCovarianceLower Q r a := fun v hv => h v (hv.trans hrs)

theorem full_lower_implies_local {p : ℕ} (Q : Matrix (Fin p) (Fin p) ℝ)
    (a : ℝ) (h : ∀ v, a * vectorNormSq v ≤ matrixQuadratic Q v) (r : ℕ) :
    LocalCovarianceLower Q r a := fun v _ => h v

theorem local_four_implies_three {p : ℕ} {Q : Matrix (Fin p) (Fin p) ℝ} {a : ℝ}
    (h : LocalCovarianceLower Q 4 a) : LocalCovarianceLower Q 3 a := h.mono (by omega)

theorem local_three_implies_two {p : ℕ} {Q : Matrix (Fin p) (Fin p) ℝ} {a : ℝ}
    (h : LocalCovarianceLower Q 3 a) : LocalCovarianceLower Q 2 a := h.mono (by omega)

theorem maxOffDiagonal_nonneg {p : ℕ} (Q : Matrix (Fin p) (Fin p) ℝ) :
    0 ≤ maxOffDiagonal Q := (Finset.le_fold_max 0).mpr (Or.inl le_rfl)

theorem pairGap_le_one {p : ℕ} (Q : Matrix (Fin p) (Fin p) ℝ) : pairGap Q ≤ 1 := by
  unfold pairGap
  linarith [maxOffDiagonal_nonneg Q]

theorem abs_offDiagonal_le {p : ℕ} (Q : Matrix (Fin p) (Fin p) ℝ)
    (j k : Fin p) (hjk : j ≠ k) : |Q j k| ≤ 1 - pairGap Q := by
  have h : |Q j k| ≤ maxOffDiagonal Q := by
    apply (Finset.le_fold_max _).mpr
    exact Or.inr ⟨(j, k), Finset.mem_univ _, by simp [hjk]⟩
  simpa only [pairGap, sub_sub_cancel] using h

/-- A unit coordinate vector, used to show that the local Rayleigh families
are nonempty whenever `p,r ≥ 1`. -/
def localBasisVector {p : ℕ} (j : Fin p) : Fin p → ℝ := fun k => if k = j then 1 else 0

theorem localBasisVector_ne_zero {p : ℕ} (j : Fin p) : localBasisVector j ≠ 0 := by
  intro h
  have hh := congrFun h j
  simp [localBasisVector] at hh

theorem localBasisVector_support {p : ℕ} (j : Fin p) :
    coordinateSupport (localBasisVector j) = {j} := by
  classical
  ext k
  simp [coordinateSupport, localBasisVector]

theorem localBasisVector_normSq {p : ℕ} (j : Fin p) :
    vectorNormSq (localBasisVector j) = 1 := by
  simp [vectorNormSq, localBasisVector]

theorem localBasisVector_quadratic {p : ℕ}
    (Q : Matrix (Fin p) (Fin p) ℝ) (j : Fin p) :
    matrixQuadratic Q (localBasisVector j) = Q j j := by
  simp [matrixQuadratic, localBasisVector, mul_ite, ite_mul]

theorem matrixQuadratic_nonneg_of_posSemidef {p : ℕ}
    {Q : Matrix (Fin p) (Fin p) ℝ} (hQ : Q.PosSemidef) (v : Fin p → ℝ) :
    0 ≤ matrixQuadratic Q v := by
  simpa [matrixQuadratic, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc] using hQ.2 v

theorem matrix_symmetric_of_posSemidef {p : ℕ}
    {Q : Matrix (Fin p) (Fin p) ℝ} (hQ : Q.PosSemidef) : ∀ j k, Q j k = Q k j := by
  intro j k
  simpa using hQ.isHermitian.apply k j

theorem localRayleighValues_nonempty {p r : ℕ}
    (Q : Matrix (Fin p) (Fin p) ℝ) (hp : 0 < p) (hr : 0 < r) :
    (localRayleighValues Q r).Nonempty := by
  let j : Fin p := ⟨0, hp⟩
  exact ⟨matrixQuadratic Q (localBasisVector j) / vectorNormSq (localBasisVector j),
    localBasisVector j, localBasisVector_ne_zero j,
    by simpa only [localBasisVector_support, Finset.card_singleton] using hr, rfl⟩

theorem localRayleighValues_bddBelow {p r : ℕ}
    {Q : Matrix (Fin p) (Fin p) ℝ} (hQ : ∀ v, 0 ≤ matrixQuadratic Q v) :
    BddBelow (localRayleighValues Q r) := by
  refine ⟨0, ?_⟩
  rintro q ⟨v, _, _, rfl⟩
  exact div_nonneg (hQ v) (vectorNormSq_nonneg v)

/-- The intrinsic Rayleigh infimum supplies the corresponding sparse quadratic
lower bound under positive semidefiniteness, including singular full matrices. -/
theorem localEigenvalue_lower {p r : ℕ}
    {Q : Matrix (Fin p) (Fin p) ℝ} (hQ : ∀ v, 0 ≤ matrixQuadratic Q v) :
    LocalCovarianceLower Q r (localEigenvalue Q r) := by
  intro v hs
  by_cases hv : v = 0
  · subst v
    simp [vectorNormSq, matrixQuadratic]
  · have hmem : matrixQuadratic Q v / vectorNormSq v ∈ localRayleighValues Q r :=
      ⟨v, hv, hs, rfl⟩
    exact (le_div_iff₀ (vectorNormSq_pos hv)).mp
      (csInf_le (localRayleighValues_bddBelow hQ) hmem)

theorem le_localEigenvalue {p r : ℕ} {Q : Matrix (Fin p) (Fin p) ℝ} {a : ℝ}
    (hp : 0 < p) (hr : 0 < r) (h : LocalCovarianceLower Q r a) :
    a ≤ localEigenvalue Q r := by
  apply le_csInf (localRayleighValues_nonempty Q hp hr)
  rintro q ⟨v, hv, hs, rfl⟩
  exact (le_div_iff₀ (vectorNormSq_pos hv)).mpr (h v hs)

/-- Exact correspondence between the intrinsic parameter and sparse quadratic
lower bounds. The only global matrix assumption is positive semidefiniteness. -/
theorem le_localEigenvalue_iff {p r : ℕ} {Q : Matrix (Fin p) (Fin p) ℝ} {a : ℝ}
    (hp : 0 < p) (hr : 0 < r) (hQ : ∀ v, 0 ≤ matrixQuadratic Q v) :
    a ≤ localEigenvalue Q r ↔ LocalCovarianceLower Q r a := by
  constructor
  · intro ha v hv
    exact (mul_le_mul_of_nonneg_right ha (vectorNormSq_nonneg v)).trans
      (localEigenvalue_lower hQ v hv)
  · exact le_localEigenvalue hp hr

theorem localEigenvalue_nonneg {p r : ℕ} {Q : Matrix (Fin p) (Fin p) ℝ}
    (hp : 0 < p) (hr : 0 < r) (hQ : ∀ v, 0 ≤ matrixQuadratic Q v) :
    0 ≤ localEigenvalue Q r := by
  apply le_localEigenvalue hp hr
  intro v _
  simpa only [zero_mul] using hQ v

theorem localEigenvalue_antitone {p r s : ℕ} {Q : Matrix (Fin p) (Fin p) ℝ}
    (hp : 0 < p) (hr : 0 < r) (hrs : r ≤ s) (hQ : ∀ v, 0 ≤ matrixQuadratic Q v) :
    localEigenvalue Q s ≤ localEigenvalue Q r :=
  le_localEigenvalue hp hr ((localEigenvalue_lower hQ).mono hrs)

theorem LocalCovarianceLower.le_one {p r : ℕ} {Q : Matrix (Fin p) (Fin p) ℝ} {a : ℝ}
    (h : LocalCovarianceLower Q r a) (hp : 0 < p) (hr : 0 < r)
    (hdiag : ∀ j, Q j j = 1) : a ≤ 1 := by
  let j : Fin p := ⟨0, hp⟩
  have hh := h (localBasisVector j)
    (by simpa only [localBasisVector_support, Finset.card_singleton] using hr)
  simpa only [localBasisVector_normSq, localBasisVector_quadratic, hdiag, mul_one] using hh

theorem localEigenvalue_le_one {p r : ℕ} {Q : Matrix (Fin p) (Fin p) ℝ}
    (hp : 0 < p) (hr : 0 < r) (hQ : ∀ v, 0 ≤ matrixQuadratic Q v)
    (hdiag : ∀ j, Q j j = 1) : localEigenvalue Q r ≤ 1 :=
  (localEigenvalue_lower hQ).le_one hp hr hdiag

/-- A full spectral bound also bounds every intrinsic local parameter. -/
theorem full_lower_le_localEigenvalue {p r : ℕ} {Q : Matrix (Fin p) (Fin p) ℝ} {a : ℝ}
    (hp : 0 < p) (hr : 0 < r)
    (h : ∀ v, a * vectorNormSq v ≤ matrixQuadratic Q v) :
    a ≤ localEigenvalue Q r :=
  le_localEigenvalue hp hr (full_lower_implies_local Q a h r)

/-- A vector supported on a specified coordinate pair. -/
def twoCoordinateVector {p : ℕ} (j k : Fin p) (a b : ℝ) : Fin p → ℝ :=
  fun l => (if l = j then a else 0) + (if l = k then b else 0)

theorem twoCoordinateVector_support {p : ℕ} (j k : Fin p) (a b : ℝ) :
    coordinateSupport (twoCoordinateVector j k a b) ⊆ {j, k} := by
  classical
  intro l hl
  simp only [coordinateSupport, Finset.mem_filter, Finset.mem_univ, true_and] at hl
  by_contra hn
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
  exact hl (by simp [twoCoordinateVector, hn.1, hn.2])

theorem twoCoordinateVector_support_card {p : ℕ} (j k : Fin p) (a b : ℝ) :
    (coordinateSupport (twoCoordinateVector j k a b)).card ≤ 2 := by
  exact (Finset.card_le_card (twoCoordinateVector_support j k a b)).trans
    (by simpa using Finset.card_insert_le j ({k} : Finset (Fin p)))

theorem matrixQuadratic_twoCoordinateVector {p : ℕ}
    (Q : Matrix (Fin p) (Fin p) ℝ) (j k : Fin p) (a b : ℝ) :
    matrixQuadratic Q (twoCoordinateVector j k a b) =
      a ^ 2 * Q j j + a * b * Q j k + b * a * Q k j + b ^ 2 * Q k k := by
  simp [matrixQuadratic, twoCoordinateVector, add_mul, mul_add,
    Finset.sum_add_distrib, mul_ite, ite_mul]
  ring

theorem vectorNormSq_twoCoordinateVector {p : ℕ}
    (j k : Fin p) (hjk : j ≠ k) (a b : ℝ) :
    vectorNormSq (twoCoordinateVector j k a b) = a ^ 2 + b ^ 2 := by
  simp [vectorNormSq, twoCoordinateVector, add_sq, Finset.sum_add_distrib,
    mul_ite, ite_mul, hjk, Ne.symm hjk]

/-- A local two-coordinate lower bound controls each off-diagonal entry. -/
theorem LocalCovarianceLower.abs_offDiagonal_le {p : ℕ}
    {Q : Matrix (Fin p) (Fin p) ℝ} {a : ℝ}
    (h : LocalCovarianceLower Q 2 a)
    (hsym : ∀ j k, Q j k = Q k j) (hdiag : ∀ j, Q j j = 1)
    (j k : Fin p) (hjk : j ≠ k) : |Q j k| ≤ 1 - a := by
  have hp := h (twoCoordinateVector j k 1 1) (twoCoordinateVector_support_card j k 1 1)
  have hm := h (twoCoordinateVector j k 1 (-1)) (twoCoordinateVector_support_card j k 1 (-1))
  rw [vectorNormSq_twoCoordinateVector j k hjk,
    matrixQuadratic_twoCoordinateVector] at hp hm
  rw [hdiag j, hdiag k, ← hsym j k] at hp hm
  apply abs_le.mpr
  constructor <;> nlinarith

/-- Thus local nondegeneracy on pairs is sufficient for a pairwise gap. -/
theorem LocalCovarianceLower.le_pairGap {p : ℕ}
    {Q : Matrix (Fin p) (Fin p) ℝ} {a : ℝ}
    (h : LocalCovarianceLower Q 2 a) (ha : a ≤ 1)
    (hsym : ∀ j k, Q j k = Q k j) (hdiag : ∀ j, Q j j = 1) : a ≤ pairGap Q := by
  have hmax : maxOffDiagonal Q ≤ 1 - a := by
    apply (Finset.fold_max_le _).mpr
    refine ⟨by linarith, ?_⟩
    intro jk _
    by_cases hjk : jk.1 = jk.2
    · simp [hjk]
      linarith
    · simpa only [hjk, if_false] using h.abs_offDiagonal_le hsym hdiag jk.1 jk.2 hjk
  unfold pairGap
  linarith

theorem a4_le_a3 {p : ℕ} {Q : Matrix (Fin p) (Fin p) ℝ}
    (hp : 0 < p) (hQ : Q.PosSemidef) : a4 Q ≤ a3 Q :=
  localEigenvalue_antitone hp (by omega) (by omega)
    (matrixQuadratic_nonneg_of_posSemidef hQ)

theorem a3_le_pairGap {p : ℕ} {Q : Matrix (Fin p) (Fin p) ℝ}
    (hp : 0 < p) (hQ : Q.PosSemidef) (hdiag : ∀ j, Q j j = 1) :
    a3 Q ≤ pairGap Q := by
  have hlocal : LocalCovarianceLower Q 3 (a3 Q) :=
    localEigenvalue_lower (matrixQuadratic_nonneg_of_posSemidef hQ)
  exact (local_three_implies_two hlocal).le_pairGap
    (hlocal.le_one hp (by omega) hdiag) (matrix_symmetric_of_posSemidef hQ) hdiag

theorem a4_nonneg {p : ℕ} {Q : Matrix (Fin p) (Fin p) ℝ}
    (hp : 0 < p) (hQ : Q.PosSemidef) : 0 ≤ a4 Q :=
  localEigenvalue_nonneg hp (by omega) (matrixQuadratic_nonneg_of_posSemidef hQ)

theorem a3_pos_of_a4_pos {p : ℕ} {Q : Matrix (Fin p) (Fin p) ℝ}
    (hp : 0 < p) (hQ : Q.PosSemidef) (ha4 : 0 < a4 Q) : 0 < a3 Q :=
  ha4.trans_le (a4_le_a3 hp hQ)

theorem pairGap_pos_of_a4_pos {p : ℕ} {Q : Matrix (Fin p) (Fin p) ℝ}
    (hp : 0 < p) (hQ : Q.PosSemidef) (hdiag : ∀ j, Q j j = 1)
    (ha4 : 0 < a4 Q) : 0 < pairGap Q :=
  (a3_pos_of_a4_pos hp hQ ha4).trans_le (a3_le_pairGap hp hQ hdiag)

namespace FaceWeights

variable {p : ℕ} (w : FaceWeights p)

/-- Covariance of the signed coordinate normals, including the zero normal.
Division by the bandwidth gives the potential's coordinate Hessian entries. -/
noncomputable def covarianceEntry (j k : Fin p) : ℝ :=
  w.diagonalMass j k - w.v j * w.v k

/-- The off-diagonal absolute mass of the smoother covariance. -/
noncomputable def offDiagonalAbsSum : ℝ :=
  ∑ j, ∑ k, if j = k then 0 else |w.covarianceEntry j k|

/-- Frobenius contraction, equal to the matrix trace contraction because the
smoother covariance is symmetric. -/
noncomputable def covarianceContraction (Q : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  ∑ j, ∑ k, Q j k * w.covarianceEntry j k

theorem covarianceEntry_diagonal (j : Fin p) :
    w.covarianceEntry j j = w.covarianceDiagonal j := by
  simp [covarianceEntry, diagonalMass, coordinateMass, covarianceDiagonal, pow_two]

theorem covarianceEntry_offDiagonal (j k : Fin p) (hjk : j ≠ k) :
    w.covarianceEntry j k = -(w.v j * w.v k) := by
  simp [covarianceEntry, diagonalMass, hjk]

theorem covarianceEntry_symm (j k : Fin p) :
    w.covarianceEntry j k = w.covarianceEntry k j := by
  by_cases hjk : j = k
  · subst k
    rfl
  · rw [w.covarianceEntry_offDiagonal j k hjk,
      w.covarianceEntry_offDiagonal k j (Ne.symm hjk), mul_comm]

theorem covarianceEntry_trace : ∑ j, w.covarianceEntry j j = w.kappa := by
  simp_rw [w.covarianceEntry_diagonal]
  exact w.covariance_trace_eq_kappa

theorem offDiagonalAbsSum_eq :
    w.offDiagonalAbsSum + w.normSq = (∑ j, |w.v j|) ^ 2 := by
  have hpoint (j k : Fin p) :
      (if j = k then 0 else |w.covarianceEntry j k|) +
          (if j = k then w.v j ^ 2 else 0) = |w.v j| * |w.v k| := by
    by_cases hjk : j = k
    · subst k
      simp only [ite_true, zero_add]
      simp only [← pow_two, sq_abs]
    · simp only [hjk, if_false, add_zero, w.covarianceEntry_offDiagonal j k hjk,
        abs_neg, abs_mul]
  calc
    _ = ∑ j, ∑ k, ((if j = k then 0 else |w.covarianceEntry j k|) +
        (if j = k then w.v j ^ 2 else 0)) := by
      simp_rw [Finset.sum_add_distrib]
      simp only [offDiagonalAbsSum, normSq, Finset.sum_ite_eq,
        Finset.mem_univ, if_true]
    _ = ∑ j, ∑ k, |w.v j| * |w.v k| := by simp_rw [hpoint]
    _ = (∑ j, |w.v j|) ^ 2 := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul]
      ring

/-- The paper's off-diagonal Hessian estimate before division by bandwidth. -/
theorem offDiagonalAbsSum_le_kappa : w.offDiagonalAbsSum ≤ w.kappa := by
  have hA : 0 ≤ ∑ j, |w.v j| := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  have hprod := mul_nonneg hA (sub_nonneg.mpr w.sum_abs_v_le_one)
  have hsum := w.sum_abs_v_le_theta
  have heq := w.offDiagonalAbsSum_eq
  unfold kappa
  nlinarith

theorem kappa_le_one : w.kappa ≤ 1 := by
  have hnorm : 0 ≤ w.normSq := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  unfold kappa
  linarith [w.theta_lt_one]

private theorem contraction_split (Q : Matrix (Fin p) (Fin p) ℝ)
    (hdiag : ∀ j, Q j j = 1) :
    w.covarianceContraction Q = w.kappa +
      ∑ j, ∑ k, if j = k then 0 else Q j k * w.covarianceEntry j k := by
  have hpoint (j k : Fin p) :
      Q j k * w.covarianceEntry j k =
        (if j = k then w.covarianceEntry j j else 0) +
          (if j = k then 0 else Q j k * w.covarianceEntry j k) := by
    by_cases hjk : j = k
    · subst k
      simp [hdiag]
    · simp [hjk]
  unfold covarianceContraction
  calc
    _ = ∑ j, ∑ k, ((if j = k then w.covarianceEntry j j else 0) +
        (if j = k then 0 else Q j k * w.covarianceEntry j k)) := by
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_congr rfl (fun k _ => hpoint j k)
    _ = _ := by
      simp_rw [Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, w.covarianceEntry_trace]

/-- Unit diagonal and a pairwise correlation gap suffice for the curvature
contraction. No global lower eigenvalue, or even positive semidefiniteness, is
needed for this algebraic implication. -/
theorem covarianceContraction_ge (Q : Matrix (Fin p) (Fin p) ℝ) (c : ℝ)
    (hc : c ≤ 1) (hdiag : ∀ j, Q j j = 1)
    (hgap : ∀ j k, j ≠ k → |Q j k| ≤ 1 - c) :
    c * w.kappa ≤ w.covarianceContraction Q := by
  have hcross : -(1 - c) * w.offDiagonalAbsSum ≤
      ∑ j, ∑ k, if j = k then 0 else Q j k * w.covarianceEntry j k := by
    unfold offDiagonalAbsSum
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    apply Finset.sum_le_sum
    intro k _
    by_cases hjk : j = k
    · simp [hjk]
    · simp only [hjk, if_false]
      have habs : |Q j k * w.covarianceEntry j k| ≤
          (1 - c) * |w.covarianceEntry j k| := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hgap j k hjk) (abs_nonneg _)
      have hsign := neg_abs_le (Q j k * w.covarianceEntry j k)
      linarith
  have hmass := mul_le_mul_of_nonneg_left w.offDiagonalAbsSum_le_kappa
    (sub_nonneg.mpr hc)
  rw [w.contraction_split Q hdiag]
  nlinarith

theorem covarianceContraction_ge_pairGap (Q : Matrix (Fin p) (Fin p) ℝ)
    (hdiag : ∀ j, Q j j = 1) :
    pairGap Q * w.kappa ≤ w.covarianceContraction Q :=
  w.covarianceContraction_ge Q (pairGap Q) (pairGap_le_one Q) hdiag
    (abs_offDiagonal_le Q)

end FaceWeights

namespace FaceSmoother

variable {p : ℕ} (s : FaceSmoother p)

/-- An actual first coordinate derivative of the logarithmic potential. -/
noncomputable def potentialCoordinateDerivative (x : Fin p → ℝ) (j : Fin p) : ℝ :=
  deriv (fun t => s.potential (line x (coordinateDirection j) t)) 0

/-- The matrix of actual iterated second coordinate derivatives. This is an
explicit coordinate definition, rather than an unproved Fréchet-Hessian claim. -/
noncomputable def potentialCoordinateHessian (x : Fin p → ℝ) :
    Matrix (Fin p) (Fin p) ℝ := fun j k =>
  deriv (fun t => s.potentialCoordinateDerivative (line x (coordinateDirection k) t) j) 0

theorem potentialCoordinateHessian_eq (x : Fin p → ℝ) (j k : Fin p) :
    s.potentialCoordinateHessian x j k =
      (s.weights x).covarianceEntry j k / s.bandwidth := by
  unfold potentialCoordinateHessian potentialCoordinateDerivative
  simp_rw [s.deriv_potential_coordinate]
  have h := (s.hasDerivAt_v_coordinate_line x (coordinateDirection k) j 0).deriv
  by_cases hjk : j = k <;>
    simpa only [line_zero, directionalMean_coordinate, coordinateDirection,
      FaceWeights.covarianceEntry, FaceWeights.diagonalMass, hjk,
      ↓reduceIte, mul_one, mul_zero] using h

theorem potentialCoordinateHessian_trace (x : Fin p → ℝ) :
    Matrix.trace (s.potentialCoordinateHessian x) = s.kappa x / s.bandwidth := by
  change (∑ j, s.potentialCoordinateHessian x j j) = _
  simp_rw [s.potentialCoordinateHessian_eq]
  simp only [div_eq_mul_inv, ← Finset.sum_mul]
  rw [(s.weights x).covarianceEntry_trace]
  rfl

theorem potentialCoordinateHessian_contraction (x : Fin p → ℝ)
    (Q : Matrix (Fin p) (Fin p) ℝ) :
    Matrix.trace (Q * s.potentialCoordinateHessian x) =
      (s.weights x).covarianceContraction Q / s.bandwidth := by
  change (∑ j, ∑ k, Q j k * s.potentialCoordinateHessian x k j) = _
  simp_rw [s.potentialCoordinateHessian_eq, (s.weights x).covarianceEntry_symm]
  simp only [div_eq_mul_inv, ← mul_assoc, ← Finset.sum_mul]
  rfl

/-- The off-diagonal bound for the actual mixed coordinate derivatives. -/
theorem potentialCoordinateHessian_offDiagonal_le_trace (x : Fin p → ℝ) :
    (∑ j, ∑ k, if j = k then 0 else |s.potentialCoordinateHessian x j k|) ≤
      Matrix.trace (s.potentialCoordinateHessian x) := by
  have hterm (j k : Fin p) :
      (if j = k then 0 else |s.potentialCoordinateHessian x j k|) =
        (if j = k then 0 else |(s.weights x).covarianceEntry j k|) / s.bandwidth := by
    by_cases hjk : j = k <;>
      simp [hjk, s.potentialCoordinateHessian_eq, abs_div, abs_of_pos s.bandwidth_pos]
  simp_rw [hterm]
  simp only [div_eq_mul_inv, ← Finset.sum_mul]
  rw [s.potentialCoordinateHessian_trace]
  exact mul_le_mul_of_nonneg_right (s.weights x).offDiagonalAbsSum_le_kappa
    (inv_nonneg.mpr s.bandwidth_pos.le)

theorem potentialCoordinateHessian_trace_le (x : Fin p → ℝ) :
    Matrix.trace (s.potentialCoordinateHessian x) ≤ 1 / s.bandwidth := by
  rw [s.potentialCoordinateHessian_trace]
  exact div_le_div_of_nonneg_right (s.weights x).kappa_le_one s.bandwidth_pos.le

/-- The paper's pair-gap trace contraction for the actual coordinate Hessian.
No global nondegeneracy assumption is used. -/
theorem potentialCoordinateHessian_pairGap_contraction (x : Fin p → ℝ)
    (Q : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, Q j j = 1) :
    pairGap Q * Matrix.trace (s.potentialCoordinateHessian x) ≤
      Matrix.trace (Q * s.potentialCoordinateHessian x) := by
  rw [s.potentialCoordinateHessian_trace, s.potentialCoordinateHessian_contraction]
  calc
    _ = (pairGap Q * s.kappa x) / s.bandwidth := by ring
    _ ≤ _ := div_le_div_of_nonneg_right
      ((s.weights x).covarianceContraction_ge_pairGap Q hdiag) s.bandwidth_pos.le

end FaceSmoother

end RectangleCLT
