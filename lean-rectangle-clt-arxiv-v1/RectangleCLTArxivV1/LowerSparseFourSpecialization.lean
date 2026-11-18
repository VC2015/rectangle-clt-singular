import RectangleCLTArxivV1.LowerSparseTheorem
import RectangleCLTArxivV1.LowerMaskedFourthTheorem

/-! The literal specialization `q=4` in the final paragraph of F.6. -/
namespace RectangleCLTArxivV1
open RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
noncomputable section
set_option autoImplicit false

theorem lowerSparseIntrinsicK_four (n : ℕ) (L B : ℝ) : lowerSparseIntrinsicK n L 4 B = B := by
  norm_num [lowerSparseIntrinsicK]

theorem lowerSparseIntrinsicRate_four (n : ℕ) (L B g : ℝ) :
    lowerSparseIntrinsicRate n L 4 B g = lowerMaskedFourthIntrinsicRate n L B g := by
  norm_num [lowerSparseIntrinsicRate,lowerMaskedFourthIntrinsicRate,lowerSparseIntrinsicK]

theorem lowerSparseSequence_four (B : ℕ → ℝ) (m : ℕ → ℕ) (n : ℕ) :
    lowerSparseSequence 4 B m n = lowerMaskedFourthSequence B m n := by
  unfold lowerSparseSequence lowerMaskedFourthSequence sparseFamilyParameters maskedFourthFamilyParameters
  have hθ : sparseLowerTheta n (Real.log (m n : ℝ)) 4 (B n) = maskedFourthTheta n (Real.log (m n : ℝ)) (B n) := by
    norm_num [sparseLowerTheta,sparseLowerCount,sparseLowerLog,sparseLowerKhat,maskedFourthTheta,maskedFourthCount]
  have hπ : sparseLowerPi n (Real.log (m n : ℝ)) 4 (B n) = maskedFourthPi (B n) := by
    norm_num [sparseLowerPi,maskedFourthPi]
  have ha : sparseLowerAmplitude n (Real.log (m n : ℝ)) 4 (B n) =
      maskedFourthAmplitude n (Real.log (m n : ℝ)) (B n) := by
    norm_num only [sparseLowerAmplitude,maskedFourthAmplitude,hθ]
  have hv : sparseLowerVariance n (Real.log (m n : ℝ)) 4 (B n) =
      maskedFourthVariance n (Real.log (m n : ℝ)) (B n) := by
    unfold sparseLowerVariance maskedFourthVariance
    rw [hθ,hπ,ha]
  simp only [hθ,hπ,ha,hv]

end
end RectangleCLTArxivV1
