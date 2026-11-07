import RectangleCLTCompanion.SplitV4.SymmetricFamilyPolynomial
import RectangleCLTCompanion.SplitV4.SymmetricBoundedLower
import RectangleCLTCompanion.SplitV4.DenseLowerCalibrationScales

/-! The actual unmasked common family for fixed B and q>4. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology
namespace RectangleCLT.Companion.SplitV4
noncomputable section

def unmaskedAmplitudeParameters (θ a : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (ha : 0 < a)
    (hv : θ*a^2 < 1/2) : SymmetricFamilyParameters where
  theta := θ
  pi := 1
  amplitude := a
  theta_pos := hθ
  theta_le_one := hθ1
  pi_pos := by norm_num
  pi_le_one := le_rfl
  amplitude_pos := ha
  variance_lt_half := by simpa only [mul_one] using hv

def denseFamilyParameters (q B : ℝ) (n m : ℕ) : SymmetricFamilyParameters :=
  if h : 0 < fourthLowerTheta n (Real.log (m : ℝ)) ∧ fourthLowerTheta n (Real.log (m : ℝ)) ≤ 1 ∧
      0 < denseLowerAmplitude n (Real.log (m : ℝ)) q B ∧
      fourthLowerTheta n (Real.log (m : ℝ))*denseLowerAmplitude n (Real.log (m : ℝ)) q B^2 < 1/2 then
    unmaskedAmplitudeParameters (fourthLowerTheta n (Real.log (m : ℝ)))
      (denseLowerAmplitude n (Real.log (m : ℝ)) q B) h.1 h.2.1 h.2.2.1 h.2.2.2
  else unmaskedUnitParameters (1/4) (by norm_num) (by norm_num)

theorem denseFamilyParameters_pi (q B : ℝ) (n m : ℕ) : (denseFamilyParameters q B n m).pi = 1 := by
  unfold denseFamilyParameters
  split_ifs <;> rfl

theorem denseFamilyParameters_of_good (q B : ℝ) (n m : ℕ)
    (h : 0 < fourthLowerTheta n (Real.log (m : ℝ)) ∧ fourthLowerTheta n (Real.log (m : ℝ)) ≤ 1 ∧
      0 < denseLowerAmplitude n (Real.log (m : ℝ)) q B ∧
      fourthLowerTheta n (Real.log (m : ℝ))*denseLowerAmplitude n (Real.log (m : ℝ)) q B^2 < 1/2) :
    (denseFamilyParameters q B n m).theta = fourthLowerTheta n (Real.log (m : ℝ)) ∧
      (denseFamilyParameters q B n m).amplitude = denseLowerAmplitude n (Real.log (m : ℝ)) q B := by
  simp only [denseFamilyParameters, dif_pos h, unmaskedAmplitudeParameters, and_self]

def denseMomentLowerRate (n m : ℕ) (q B : ℝ) : ℝ :=
  B*dimensionLog (m*m)^(3/2-1/q)/(n : ℝ)^(1/2-1/q)

theorem denseMomentLowerRate_eq (n m : ℕ) (hm : 2 ≤ m) (q B : ℝ) :
    denseMomentLowerRate n m q B = denseLowerEnvelopeRate n (Real.log (m : ℝ)) q B := by
  rw [denseMomentLowerRate, dimensionLog_square m (by omega), denseLowerEnvelopeRate]

end
end RectangleCLT.Companion.SplitV4
