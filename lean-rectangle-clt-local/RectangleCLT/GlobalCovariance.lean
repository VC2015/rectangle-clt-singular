import RectangleCLT.LocalStatement

/-!
# The full spectral parameter and its local lower bounds

The full parameter is the infimum of all nonzero Rayleigh quotients. The
square root `fullCovarianceScale` is the manuscript's `b`; the eigenvalue
itself is `fullEigenvalue`. These definitions and comparison lemmas do not
assert the full-eigenvalue Gaussian derivative estimate or a global CLT.
-/

namespace RectangleCLT

noncomputable section

/-- The full least Rayleigh value. Testing support size at most `p` imposes
no restriction on a vector in `Fin p → ℝ`. -/
def fullEigenvalue {p : ℕ} (Q : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  localEigenvalue Q p

/-- The square root of the full eigenvalue, denoted `b` in the paper. -/
def fullCovarianceScale {p : ℕ} (Q : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  Real.sqrt (fullEigenvalue Q)

theorem fullEigenvalue_lower {p : ℕ} {Q : Matrix (Fin p) (Fin p) ℝ}
    (hQ : Q.PosSemidef) (v : Vector p) :
    fullEigenvalue Q * vectorNormSq v ≤ matrixQuadratic Q v := by
  apply localEigenvalue_lower (matrixQuadratic_nonneg_of_posSemidef hQ) v
  simpa only [Fintype.card_fin] using (coordinateSupport v).card_le_univ

theorem le_fullEigenvalue {p : ℕ} {Q : Matrix (Fin p) (Fin p) ℝ} {a : ℝ}
    (hp : 0 < p) (h : ∀ v, a * vectorNormSq v ≤ matrixQuadratic Q v) :
    a ≤ fullEigenvalue Q :=
  full_lower_le_localEigenvalue hp hp h

theorem fullEigenvalue_nonneg {p : ℕ} {Q : Matrix (Fin p) (Fin p) ℝ}
    (hp : 0 < p) (hQ : Q.PosSemidef) : 0 ≤ fullEigenvalue Q :=
  localEigenvalue_nonneg hp hp (matrixQuadratic_nonneg_of_posSemidef hQ)

theorem fullEigenvalue_le_localEigenvalue {p r : ℕ}
    {Q : Matrix (Fin p) (Fin p) ℝ} (hp : 0 < p) (hr : 0 < r)
    (hQ : Q.PosSemidef) : fullEigenvalue Q ≤ localEigenvalue Q r :=
  full_lower_le_localEigenvalue hp hr (fullEigenvalue_lower hQ)

theorem fullEigenvalue_le_a4 {p : ℕ} {Q : Matrix (Fin p) (Fin p) ℝ}
    (hp : 0 < p) (hQ : Q.PosSemidef) : fullEigenvalue Q ≤ a4 Q :=
  fullEigenvalue_le_localEigenvalue hp (by omega) hQ

theorem fullEigenvalue_le_pairGap {p : ℕ} {Q : Matrix (Fin p) (Fin p) ℝ}
    (hp : 0 < p) (hQ : Q.PosSemidef) (hdiag : ∀ j, Q j j = 1) :
    fullEigenvalue Q ≤ pairGap Q :=
  (fullEigenvalue_le_localEigenvalue hp (by omega : 0 < 3) hQ).trans
    (a3_le_pairGap hp hQ hdiag)

theorem fullCovarianceScale_sq {p : ℕ} {Q : Matrix (Fin p) (Fin p) ℝ}
    (hp : 0 < p) (hQ : Q.PosSemidef) :
    fullCovarianceScale Q ^ 2 = fullEigenvalue Q :=
  Real.sq_sqrt (fullEigenvalue_nonneg hp hQ)

/-- Positivity of the full eigenvalue implies the actual local covariance
hypotheses, including in dimensions below four. -/
theorem localCovarianceHypotheses_of_fullEigenvalue_pos {p : ℕ}
    {Q : Matrix (Fin p) (Fin p) ℝ} (hp : 0 < p) (hQ : Q.PosSemidef)
    (hdiag : ∀ j, Q j j = 1) (hfull : 0 < fullEigenvalue Q) :
    LocalCovarianceHypotheses Q :=
  ⟨hQ, hdiag, hfull.trans_le (fullEigenvalue_le_a4 hp hQ)⟩

/-- The reciprocal eigenvalue equals `b⁻²`; confusing `b` with the
eigenvalue would give the wrong power in the recovery corollary. -/
theorem inv_fullEigenvalue_eq_inv_scale_sq {p : ℕ}
    {Q : Matrix (Fin p) (Fin p) ℝ} (hp : 0 < p) (hQ : Q.PosSemidef) :
    1 / fullEigenvalue Q = 1 / fullCovarianceScale Q ^ 2 := by
  rw [fullCovarianceScale_sq hp hQ]

end

end RectangleCLT
