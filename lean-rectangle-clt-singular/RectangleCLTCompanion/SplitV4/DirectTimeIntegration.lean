import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Integrating a genuine derivative bound with continuity at both
endpoints. Derivatives are needed only on the open interval. -/

open Set

namespace RectangleCLT.Companion.SplitV4
noncomputable section

theorem direct_time_increment_le {P D : ℝ → ℝ} {u B : ℝ}
    (hu : 0 ≤ u) (hP : ContinuousOn P (Icc (0 : ℝ) u))
    (hD : ∀ v ∈ Ioo (0 : ℝ) u, HasDerivAt P (D v) v)
    (hbound : ∀ v ∈ Ioo (0 : ℝ) u, |D v| ≤ B) :
    |P u-P 0| ≤ B*u := by
  have hone (f d : ℝ → ℝ) (hf : ContinuousOn f (Icc (0 : ℝ) u))
      (hd : ∀ v ∈ Ioo (0 : ℝ) u, HasDerivAt f (d v) v)
      (hle : ∀ v ∈ Ioo (0 : ℝ) u, d v ≤ B) : f u-f 0 ≤ B*u := by
    have hm : MonotoneOn (fun v => B*v-f v) (Icc (0 : ℝ) u) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) u)
        ((continuous_const.mul continuous_id).continuousOn.sub hf)
      · intro v hv
        rw [interior_Icc] at hv
        have hder : HasDerivAt (fun v => B*v-f v) (B-d v) v := by
          simpa only [mul_one] using ((hasDerivAt_id v).const_mul B).sub (hd v hv)
        exact hder.hasDerivWithinAt
      · intro v hv
        rw [interior_Icc] at hv
        exact sub_nonneg.mpr (hle v hv)
    have hh := hm ⟨le_rfl,hu⟩ ⟨hu,le_rfl⟩ hu
    change B*0-f 0 ≤ B*u-f u at hh
    linarith
  have hp := hone P D hP hD (fun v hv => (le_abs_self _).trans (hbound v hv))
  have hn := hone (fun v => -P v) (fun v => -D v) hP.neg
    (fun v hv => (hD v hv).neg) (fun v hv => (neg_le_abs _).trans (hbound v hv))
  change -P u- -P 0 ≤ B*u at hn
  exact abs_le.mpr ⟨by linarith, hp⟩

end
end RectangleCLT.Companion.SplitV4
