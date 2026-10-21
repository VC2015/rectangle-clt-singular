import RectangleCLTCompanion.LowerScaleStatement
import RectangleCLTCompanion.LowerScale

/-! The full Theorem 4, with the actual supremum rectangle distance and
all construction properties. The detecting-rectangle lower bound and the
finite upper bound are both supplied by proved probability theorems. -/

open Filter
open scoped Topology

namespace RectangleCLT.Companion

noncomputable section

/-- The sharp lower constant for the full rectangle distance of the
actual iid independent-coordinate two-point construction. -/
theorem lowerScaleRectangleDistance_liminf {B : ℕ → ℝ} {p : ℕ → ℕ}
    (hB : ∀ n, 2 ≤ B n) (hp : Tendsto p atTop atTop)
    (hr : Tendsto (fun n => lowerSkewRate (B n) (p n) n) atTop (𝓝 0)) :
    skewLowerScaleConstant ≤ liminf (fun n =>
      lowerConstructionDistance (B n) n (p n) / lowerSkewRate (B n) (p n) n) atTop := by
  have hnonneg : IsBoundedUnder (· ≥ ·) atTop (fun n =>
      rectangleError (lowerArrayLaw (B n) n (p n))
        (sumVector (lowerNormalizedRows (n := n) (p := p n))) 1
        (partialMaximumRectangle (p n) (p n) (normalMaxThreshold (p n))) /
          lowerSkewRate (B n) (p n) n) := by
    refine ⟨0, ?_⟩
    exact (lowerSkewRate_eventually_pos hB hp).mono
      (fun n hn => div_nonneg (abs_nonneg _) hn.le)
  have hupper := lowerConstructionDistance_ratio_isBoundedUnder hB hp
  have hle : ∀ᶠ n in atTop,
      rectangleError (lowerArrayLaw (B n) n (p n))
        (sumVector (lowerNormalizedRows (n := n) (p := p n))) 1
        (partialMaximumRectangle (p n) (p n) (normalMaxThreshold (p n))) /
          lowerSkewRate (B n) (p n) n ≤
      lowerConstructionDistance (B n) n (p n) / lowerSkewRate (B n) (p n) n := by
    filter_upwards [lowerSkewRate_eventually_pos hB hp] with n hn
    exact div_le_div_of_nonneg_right (lower_rectangleError_le_distance _ _ _ _) hn.le
  exact (lowerScaleRectangle_liminf hB hp hr).trans
    (liminf_le_liminf hle hnonneg hupper.isCoboundedUnder_ge)

/-- Companion Theorem 4. The canonical laws explicitly witness iid
observations, independent coordinates, covariance I and attained B_n,
with the exact lower constant sqrt(2)/(4e). -/
theorem skewedTwoPointLowerScale : SkewedTwoPointLowerScale := by
  intro B p hp hB hr
  constructor
  · intro n hn hpn
    exact lowerConstructionProperties (by linarith only [hB n]) hn hpn
  · exact lowerScaleRectangleDistance_liminf hB hp hr

end

end RectangleCLT.Companion
