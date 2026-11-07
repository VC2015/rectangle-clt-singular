import RectangleCLTCompanion.SplitV4.Printed.MatrixNonnegativeContraction
import RectangleCLTCompanion.SplitV4.LogisticMatrixEstimate

/-! Printed B.4's generic (possibly vanishing) log-concave weight reduction.
The original selector specialization is retained unchanged. -/

open MeasureTheory

namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

/-- The generic nuclear inequality of equation matrix-trace-reduction.
All covariance and integrability requirements follow from the displayed
weight assumptions, including for convex-cell indicators. -/
theorem nonnegative_logConcave_weight_nuclear_reduction {r : ℕ}
    (w : Vector r → ℝ) (hw : Measurable w)
    (hw₀ : ∀ g, 0 ≤ w g) (hw₁ : ∀ g, w g ≤ 1)
    (hp : 0 < ∫ g, w g ∂standardGaussian r) (hc : NonnegativeLogConcave w) :
    symmetricNuclearNorm (weightedScore (standardGaussian r) id w) ≤
      2 * weightMass (standardGaussian r) w *
        vectorNormSq (weightMean (standardGaussian r) id w) -
      ∫ g, (vectorNormSq g - (r : ℝ)) * w g ∂standardGaussian r := by
  rw [← SignedSurface.trace_weightedScore_eq_gaussian_score w hw
    (fun g => by rw [abs_of_nonneg (hw₀ g)]; exact hw₁ g)]
  apply csSup_le (symmetricTrace_values_nonempty _)
  rintro t ⟨B, hB, rfl⟩
  have hh := standardGaussian_weightedScore_reduction w hw
    (fun g => by rw [abs_of_nonneg (hw₀ g)]; exact hw₁ g) B (b := 1) hp
    (fun z => by simpa only [one_mul] using hB.2.1 z)
    (gaussian_weightCovariance_contraction_nonnegative w hw hw₀ hw₁ hp hc)
  exact (le_abs_self _).trans (by simpa only [one_mul] using hh)

end
end RectangleCLT.Companion.SplitV4.Printed
