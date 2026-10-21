import RectangleCLTCompanion.LowerConstruction
import RectangleCLTCompanion.LowerRectangleDistance

/-! The exact lower-scale claim in Theorem 4. The model is explicit:
its laws, independence, covariance, and attained envelope are conclusions. -/

open Filter
open scoped Topology

namespace RectangleCLT.Companion

noncomputable section

/-- The paper's explicit sharp lower constant. -/
def skewLowerScaleConstant : ℝ := Real.sqrt 2 / (4 * Real.exp 1)

/-- An explicit construction proves the existence asserted in Theorem 4.
No limit for `1-B_n^(-2)` or additional relation between p and n is imposed. -/
def SkewedTwoPointLowerScale : Prop :=
  ∀ (B : ℕ → ℝ) (p : ℕ → ℕ),
    Tendsto p atTop atTop →
    (∀ n, 2 ≤ B n) →
    Tendsto (fun n => lowerSkewRate (B n) (p n) n) atTop (𝓝 0) →
    (∀ n, 1 ≤ n → 1 ≤ p n → LowerConstructionProperties (B n) n (p n)) ∧
    skewLowerScaleConstant ≤ liminf
      (fun n => lowerConstructionDistance (B n) n (p n) / lowerSkewRate (B n) (p n) n) atTop

end

end RectangleCLT.Companion
