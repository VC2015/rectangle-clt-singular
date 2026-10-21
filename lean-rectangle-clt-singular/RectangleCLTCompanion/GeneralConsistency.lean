import RectangleCLTCompanion.GeneralConsistencyNecessity
import RectangleCLTCompanion.ConsistencyUpper

/-! # The exact uniform consistency criterion at a fixed correlation gap -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

universe u

namespace RectangleCLT.Companion

noncomputable section

/-- The first assertion of Theorem 5, with its original quantifier order:
for a fixed gap and arbitrary `B_n ≥ 2` and `p_n ≥ 1`, uniform rectangle
consistency holds exactly when `B_n log(ep_n)^(3/2)/sqrt n` vanishes. -/
theorem fixedGapUniformConsistency_iff
    {c₀ : ℝ} {B : ℕ → ℝ} {p : ℕ → ℕ} (hc₀ : 0 < c₀) (hc₁ : c₀ ≤ 1)
    (hB : ∀ n, 2 ≤ B n) (hp : ∀ n, 1 ≤ p n) :
    FixedGapUniformConsistency.{u} c₀ B p ↔
      Tendsto (fun n : ℕ => B n / Real.sqrt n * dimensionLog (p n)^(3/2 : ℝ))
        atTop (𝓝 0) := by
  constructor
  · exact fixedGapUniformConsistency_necessary hc₁ hB hp
  · exact fixedGapUniformConsistency_of_rate_tendsto_zero hc₀ B p hp

end

end RectangleCLT.Companion
