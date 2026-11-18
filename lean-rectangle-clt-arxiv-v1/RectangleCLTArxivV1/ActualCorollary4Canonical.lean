import RectangleCLTArxivV1.ActualCorollaries

/-! Corollary4 at the actual covariance gap defined in the main paper. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
noncomputable section
set_option autoImplicit false

theorem corollary4_canonical_correlation_gap
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1≤p)
    (hunit : ∀ j,covariance μ (sumVector ξ) j j=1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose=covariance μ (sumVector ξ))
    (hc : 0<pairGap (covariance μ (sumVector ξ))) :
    rectangleDistance μ (sumVector ξ) A≤corollary4Constant*
      min 1 (δ*gaussianMaximumMean A*dimensionLog p*
        Real.sqrt (1+Real.log (1/pairGap (covariance μ (sumVector ξ))))) := by
  have hgap (j k : Fin p) (hjk : j≠k) :
      pairGap (covariance μ (sumVector ξ))≤1-|covariance μ (sumVector ξ) j k| := by
    linarith [abs_offDiagonal_le (covariance μ (sumVector ξ)) j k hjk]
  simpa only [positiveGapRate,positiveGapGain] using
    corollary4_positive_correlation_gap μ ξ h hp hunit A hA hc (pairGap_le_one _) hgap

end
end RectangleCLTArxivV1
