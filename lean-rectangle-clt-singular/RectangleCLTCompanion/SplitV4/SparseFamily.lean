import RectangleCLTCompanion.SplitV4.SparseFamilyMoments
import RectangleCLTCompanion.SplitV4.SparseLowerCalibrationScales
import RectangleCLTCompanion.SplitV4.RareFamilyComparison

/-! The actual masked common family for the general sparse polynomial regime. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology
namespace RectangleCLT.Companion.SplitV4
noncomputable section

def sparseFamilyParameters (q : ℝ) (n m : ℕ) (B : ℝ) : SymmetricFamilyParameters :=
  if h : 0 < sparseLowerTheta n (Real.log (m : ℝ)) q B ∧ sparseLowerTheta n (Real.log (m : ℝ)) q B ≤ 1 ∧
      0 < sparseLowerPi n (Real.log (m : ℝ)) q B ∧ sparseLowerPi n (Real.log (m : ℝ)) q B ≤ 1 ∧
      0 < sparseLowerAmplitude n (Real.log (m : ℝ)) q B ∧ sparseLowerVariance n (Real.log (m : ℝ)) q B < 1/2 then
    { theta := sparseLowerTheta n (Real.log (m : ℝ)) q B
      pi := sparseLowerPi n (Real.log (m : ℝ)) q B
      amplitude := sparseLowerAmplitude n (Real.log (m : ℝ)) q B
      theta_pos := h.1
      theta_le_one := h.2.1
      pi_pos := h.2.2.1
      pi_le_one := h.2.2.2.1
      amplitude_pos := h.2.2.2.2.1
      variance_lt_half := h.2.2.2.2.2 }
  else unmaskedUnitParameters (1/4) (by norm_num) (by norm_num)

theorem sparseFamilyParameters_of_good (q : ℝ) (n m : ℕ) (B : ℝ)
    (h : 0 < sparseLowerTheta n (Real.log (m : ℝ)) q B ∧ sparseLowerTheta n (Real.log (m : ℝ)) q B ≤ 1 ∧
      0 < sparseLowerPi n (Real.log (m : ℝ)) q B ∧ sparseLowerPi n (Real.log (m : ℝ)) q B ≤ 1 ∧
      0 < sparseLowerAmplitude n (Real.log (m : ℝ)) q B ∧ sparseLowerVariance n (Real.log (m : ℝ)) q B < 1/2) :
    (sparseFamilyParameters q n m B).theta = sparseLowerTheta n (Real.log (m : ℝ)) q B ∧
      (sparseFamilyParameters q n m B).pi = sparseLowerPi n (Real.log (m : ℝ)) q B ∧
      (sparseFamilyParameters q n m B).amplitude = sparseLowerAmplitude n (Real.log (m : ℝ)) q B := by
  simp only [sparseFamilyParameters, dif_pos h, and_self]

theorem sparseFamily_identities {q B : ℝ} {n m : ℕ} (hn : 1 ≤ n)
    (h : (sparseFamilyParameters q n m B).theta = sparseLowerTheta n (Real.log (m : ℝ)) q B ∧
      (sparseFamilyParameters q n m B).pi = sparseLowerPi n (Real.log (m : ℝ)) q B ∧
      (sparseFamilyParameters q n m B).amplitude = sparseLowerAmplitude n (Real.log (m : ℝ)) q B) :
    (sparseFamilyParameters q n m B).variance = sparseLowerVariance n (Real.log (m : ℝ)) q B ∧
      (n : ℝ)*(sparseFamilyParameters q n m B).theta = sparseLowerCount n (Real.log (m : ℝ)) q B ∧
      familyRareShiftScale (sparseFamilyParameters q n m B) n =
        sparseLowerAmplitude n (Real.log (m : ℝ)) q B*sparseLowerCount n (Real.log (m : ℝ)) q B/Real.sqrt n ∧
      familyRareLowerScale (sparseFamilyParameters q n m B) n m = sparseLowerScale n (Real.log (m : ℝ)) q B := by
  have hcount : (n : ℝ)*(sparseFamilyParameters q n m B).theta = sparseLowerCount n (Real.log (m : ℝ)) q B := by
    rw [h.1, sparseLowerTheta_count (by omega : 0 < n)]
  refine ⟨?_, hcount, ?_, ?_⟩
  · unfold SymmetricFamilyParameters.variance
    rw [h.1, h.2.1, h.2.2]
    rfl
  · unfold familyRareShiftScale
    rw [h.2.2, hcount]
  · unfold familyRareLowerScale familyRareShiftScale sparseLowerScale
    rw [h.2.2, hcount]
    ring

end
end RectangleCLT.Companion.SplitV4
