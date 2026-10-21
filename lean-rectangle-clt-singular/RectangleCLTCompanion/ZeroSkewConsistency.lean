import RectangleCLTCompanion.ZeroSkewConsistencyNecessity
import RectangleCLTCompanion.ConsistencyUpper

/-! # The exact fixed-envelope zero-skew consistency threshold

This is the second assertion of Theorem 5. Its uniformity is over the
whole probability class at each sample size, including singular covariance.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

universe u

namespace RectangleCLT.Companion

noncomputable section

/-- For every fixed `B ≥ 1` and `c₀ ∈ (0,1]`, the supremum rectangle
error over the aggregate-zero-third-tensor class tends to zero exactly
when `log p = o(sqrt n)`. No covariance eigenvalue is assumed. -/
theorem zeroSkewFixedGapUniformConsistency_iff
    {c₀ B : ℝ} {p : ℕ → ℕ} (hc₀ : 0 < c₀) (hc₁ : c₀ ≤ 1) (hB : 1 ≤ B)
    (hp : ∀ n, 1 ≤ p n) :
    ZeroSkewFixedGapUniformConsistency.{u} c₀ B p ↔
      Tendsto (fun n : ℕ => Real.log (p n : ℝ) / Real.sqrt n) atTop (𝓝 0) := by
  constructor
  · exact zeroSkewFixedGapUniformConsistency_necessary hc₁ hB hp
  · intro hlog
    exact zeroSkewFixedGapUniformConsistency_of_log_rate_tendsto_zero hc₀ p hp hlog

end

end RectangleCLT.Companion
