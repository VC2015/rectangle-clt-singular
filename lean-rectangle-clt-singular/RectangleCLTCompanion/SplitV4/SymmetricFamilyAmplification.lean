import RectangleCLTCompanion.SplitV4.SymmetricBoundedLower

/-! Exact change of amplitude in the genuine common-family law.
The sign/activation/mask law depends only on the two probabilities. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology
namespace RectangleCLT.Companion.SplitV4
noncomputable section

def familyShiftAmplification (P Q : SymmetricFamilyParameters) : ℝ :=
  P.amplitude * Q.scale / (Q.amplitude * P.scale)

theorem familyShiftAmplification_pos (P Q : SymmetricFamilyParameters) :
    0 < familyShiftAmplification P Q :=
  div_pos (mul_pos P.amplitude_pos Q.scale_pos) (mul_pos Q.amplitude_pos P.scale_pos)

theorem familyRestLaw_eq_of_probabilities (P Q : SymmetricFamilyParameters)
    (hθ : P.theta = Q.theta) (hπ : P.pi = Q.pi) (m : ℕ) :
    familyRestLaw P m = familyRestLaw Q m := by
  have ht : familyTheta P = familyTheta Q := Subtype.ext hθ
  have hp : familyPi P = familyPi Q := Subtype.ext hπ
  simp only [familyRestLaw, familyMaskLaw, ht, hp]

theorem familyRestArrayLaw_eq_of_probabilities (P Q : SymmetricFamilyParameters)
    (hθ : P.theta = Q.theta) (hπ : P.pi = Q.pi) (n m : ℕ) :
    familyRestArrayLaw P n m = familyRestArrayLaw Q n m := by
  simp only [familyRestArrayLaw, familyRestLaw_eq_of_probabilities P Q hθ hπ]

theorem family_variance_amplification (P Q : SymmetricFamilyParameters)
    (hθ : P.theta = Q.theta) (hπ : P.pi = Q.pi) :
    P.variance = (P.amplitude / Q.amplitude)^2 * Q.variance := by
  unfold SymmetricFamilyParameters.variance
  rw [hθ, hπ]
  field_simp [Q.amplitude_pos.ne']
  ring

theorem family_sqrt_variance_amplification (P Q : SymmetricFamilyParameters)
    (hθ : P.theta = Q.theta) (hπ : P.pi = Q.pi) :
    Real.sqrt P.variance = P.amplitude / Q.amplitude * Real.sqrt Q.variance := by
  rw [family_variance_amplification P Q hθ hπ, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (div_pos P.amplitude_pos Q.amplitude_pos).le]

theorem familyObservationShift_amplification (P Q : SymmetricFamilyParameters)
    {n m : ℕ} [NeZero m] (z : Fin n → FamilyRestSeed m) :
    familyObservationShift P z = familyShiftAmplification P Q * familyObservationShift Q z := by
  unfold familyObservationShift familyShiftAmplification
  by_cases hw : Real.sqrt (n : ℝ) = 0
  · simp only [hw, mul_zero, div_zero, zero_mul, mul_zero]
  · field_simp [P.scale_pos.ne', Q.scale_pos.ne', Q.amplitude_pos.ne', hw]
    ring

theorem familyGaussianShift_amplification (P Q : SymmetricFamilyParameters)
    (hθ : P.theta = Q.theta) (hπ : P.pi = Q.pi) {m : ℕ} [NeZero m] (z : Vector m) :
    familyGaussianShift P z = familyShiftAmplification P Q * familyGaussianShift Q z := by
  unfold familyGaussianShift familyShiftAmplification
  rw [family_sqrt_variance_amplification P Q hθ hπ]
  field_simp [P.scale_pos.ne', Q.scale_pos.ne', Q.amplitude_pos.ne']
  ring

theorem familyShiftMeanDifference_amplification (P Q : SymmetricFamilyParameters)
    (hθ : P.theta = Q.theta) (hπ : P.pi = Q.pi) (n m : ℕ) [NeZero m] :
    familyShiftMeanDifference P n m =
      familyShiftAmplification P Q * familyShiftMeanDifference Q n m := by
  unfold familyShiftMeanDifference
  rw [familyRestArrayLaw_eq_of_probabilities P Q hθ hπ]
  simp_rw [familyGaussianShift_amplification P Q hθ hπ, familyObservationShift_amplification P Q]
  rw [integral_const_mul, integral_const_mul]
  ring

theorem familyShiftSecondMoments_amplification (P Q : SymmetricFamilyParameters)
    (hθ : P.theta = Q.theta) (hπ : P.pi = Q.pi) (n m : ℕ) [NeZero m] :
    familyShiftSecondMoments P n m =
      familyShiftAmplification P Q ^ 2 * familyShiftSecondMoments Q n m := by
  unfold familyShiftSecondMoments
  rw [familyRestArrayLaw_eq_of_probabilities P Q hθ hπ]
  simp_rw [familyGaussianShift_amplification P Q hθ hπ, familyObservationShift_amplification P Q, mul_pow]
  rw [integral_const_mul, integral_const_mul]
  ring

end
end RectangleCLT.Companion.SplitV4
