import RectangleCLTCompanion.SplitV4.SymmetricFamilyPolynomial
import RectangleCLTCompanion.SplitV4.SymmetricBoundedParameters
import RectangleCLTCompanion.SplitV4.MaskedFourthLowerCalibrationScales

/-! Actual growing-envelope fourth-moment masked family. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology
namespace RectangleCLT.Companion.SplitV4
noncomputable section

def maskedFourthFamilyParameters (n m : ℕ) (B : ℝ) : SymmetricFamilyParameters :=
  if h : 0 < maskedFourthTheta n (Real.log (m : ℝ)) B ∧ maskedFourthTheta n (Real.log (m : ℝ)) B ≤ 1 ∧
      0 < maskedFourthPi B ∧ maskedFourthPi B ≤ 1 ∧
      0 < maskedFourthAmplitude n (Real.log (m : ℝ)) B ∧ maskedFourthVariance n (Real.log (m : ℝ)) B < 1/2 then
    { theta := maskedFourthTheta n (Real.log (m : ℝ)) B
      pi := maskedFourthPi B
      amplitude := maskedFourthAmplitude n (Real.log (m : ℝ)) B
      theta_pos := h.1
      theta_le_one := h.2.1
      pi_pos := h.2.2.1
      pi_le_one := h.2.2.2.1
      amplitude_pos := h.2.2.2.2.1
      variance_lt_half := h.2.2.2.2.2 }
  else unmaskedUnitParameters (1/4) (by norm_num) (by norm_num)

theorem maskedFourthFamilyParameters_of_good (n m : ℕ) (B : ℝ)
    (h : 0 < maskedFourthTheta n (Real.log (m : ℝ)) B ∧ maskedFourthTheta n (Real.log (m : ℝ)) B ≤ 1 ∧
      0 < maskedFourthPi B ∧ maskedFourthPi B ≤ 1 ∧
      0 < maskedFourthAmplitude n (Real.log (m : ℝ)) B ∧ maskedFourthVariance n (Real.log (m : ℝ)) B < 1/2) :
    (maskedFourthFamilyParameters n m B).theta = maskedFourthTheta n (Real.log (m : ℝ)) B ∧
      (maskedFourthFamilyParameters n m B).pi = maskedFourthPi B ∧
      (maskedFourthFamilyParameters n m B).amplitude = maskedFourthAmplitude n (Real.log (m : ℝ)) B := by
  simp only [maskedFourthFamilyParameters, dif_pos h, and_self]

def maskedFourthMomentLowerRate (n m : ℕ) (B : ℝ) : ℝ := maskedFourthRate n (Real.log (m : ℝ)) B

end
end RectangleCLT.Companion.SplitV4
