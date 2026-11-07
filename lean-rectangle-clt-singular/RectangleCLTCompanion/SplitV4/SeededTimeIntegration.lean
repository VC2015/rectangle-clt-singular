import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open Set

namespace RectangleCLT.Companion.SplitV4

noncomputable section

/-- The calibrated cubic factor costs at most one time unit; the seeded
fourth-order factor gives the exact logarithm. This primitive argument
requires derivatives only on the open interval and continuity at endpoints.
-/
theorem seeded_time_increment_le {P D : ℝ → ℝ} {ε a b : ℝ}
    (hε : 0 < ε) (ha : 0 ≤ a) (hP : ContinuousOn P (Icc (0 : ℝ) 1))
    (hD : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt P (D t) t)
    (hbound : ∀ t ∈ Ioo (0 : ℝ) 1,
      |D t| ≤ a * t / (t + ε) + b / (t + ε)) :
    |P 1 - P 0| ≤ a + b * Real.log (1 + 1 / ε) := by
  let G : ℝ → ℝ := fun t => a * t + b * Real.log (t + ε)
  have hG : ContinuousOn G (Icc (0 : ℝ) 1) := by
    apply (continuous_const.mul continuous_id).continuousOn.add
    apply continuousOn_const.mul
    exact (continuousOn_id.add continuousOn_const).log (fun t ht => by
      change t + ε ≠ 0
      linarith [ht.1])
  have hGd (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt G (a + b / (t + ε)) t := by
    have htε : t + ε ≠ 0 := by linarith [ht.1]
    convert ((hasDerivAt_id t).const_mul a).add
      ((((hasDerivAt_id t).add_const ε).log htε).const_mul b) using 1 <;> dsimp [G] <;> ring
  have hmajor (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : |D t| ≤ a + b / (t + ε) := by
    have htε : 0 < t + ε := by linarith [ht.1]
    have hratio : a * t / (t + ε) ≤ a := by
      apply (div_le_iff₀ htε).mpr
      nlinarith
    exact (hbound t ht).trans (add_le_add_right hratio _)
  have hone (f d : ℝ → ℝ) (hf : ContinuousOn f (Icc (0 : ℝ) 1))
      (hd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt f (d t) t)
      (hle : ∀ t ∈ Ioo (0 : ℝ) 1, d t ≤ a + b / (t + ε)) :
      f 1 - f 0 ≤ G 1 - G 0 := by
    have hm : MonotoneOn (fun t => G t - f t) (Icc (0 : ℝ) 1) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) 1) (hG.sub hf)
      · intro t ht
        rw [interior_Icc] at ht
        exact ((hGd t ht).sub (hd t ht)).hasDerivWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        exact sub_nonneg.mpr (hle t ht)
    have hh := hm (by norm_num : (0 : ℝ) ∈ Icc 0 1)
      (by norm_num : (1 : ℝ) ∈ Icc 0 1) (by norm_num : (0 : ℝ) ≤ 1)
    change G 0 - f 0 ≤ G 1 - f 1 at hh
    linarith
  have hplus := hone P D hP hD (fun t ht => (le_abs_self _).trans (hmajor t ht))
  have hminus := hone (fun t => -P t) (fun t => -D t) hP.neg
    (fun t ht => (hD t ht).neg) (fun t ht => (neg_le_abs _).trans (hmajor t ht))
  have hlog : Real.log (1 + ε) - Real.log ε = Real.log (1 + 1 / ε) := by
    rw [← Real.log_div (by positivity : 1 + ε ≠ 0) hε.ne']
    congr 1
    field_simp
    ring
  have he : G 1 - G 0 = a + b * Real.log (1 + 1 / ε) := by
    dsimp [G]
    simp only [mul_one, mul_zero, zero_add, add_zero]
    rw [show a + b * Real.log (1 + ε) - b * Real.log ε =
      a + b * (Real.log (1 + ε) - Real.log ε) by ring, hlog]
  rw [he] at hplus hminus
  change -P 1 - -P 0 ≤ _ at hminus
  exact abs_le.mpr ⟨by linarith, hplus⟩

end

end RectangleCLT.Companion.SplitV4
