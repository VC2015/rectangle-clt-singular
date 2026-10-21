import RectangleCLTCompanion.LowerRelativeTailError

/-! Turning the proved relative weighted-tail error into a logarithmic
error, with positivity derived rather than assumed. -/

open Set

namespace RectangleCLT.Companion

theorem lower_abs_log_of_abs_sub_one {v η : ℝ}
    (hv : |v - 1| ≤ η) (hη : η ≤ 1 / 2) :
    0 < v ∧ |Real.log v| ≤ 2 * η := by
  have hη0 : 0 ≤ η := (abs_nonneg _).trans hv
  have hvbounds := abs_le.mp hv
  have hvpos : 0 < v := by linarith
  refine ⟨hvpos, abs_le.mpr ⟨?_, ?_⟩⟩
  · have hmul := mul_le_mul_of_nonneg_left (by linarith : 1 - η ≤ v)
      (by linarith : 0 ≤ 1 + 2 * η)
    have hquad : 0 ≤ η * (1 - 2 * η) := mul_nonneg hη0 (by linarith)
    have hi : v⁻¹ ≤ 1 + 2 * η := by
      rw [← one_div]
      apply (div_le_iff₀ hvpos).mpr
      nlinarith
    linarith [Real.one_sub_inv_le_log_of_pos hvpos]
  · linarith [Real.log_le_sub_one_of_pos hvpos]

theorem lowerTiltedTailExpectation_log_error {B t : ℝ} (hB : 1 ≤ B)
    {n : ℕ} (hn : 1 ≤ n) (ht : 0 < t)
    (hs : 1 ≤ lowerTiltedTailParameter B t n)
    (hsmall : lowerRelativeTailConstant * (B * t) ≤ 1 / 2) :
    0 < lowerTiltedTailExpectation B t n ∧
      |Real.log (lowerTiltedTailExpectation B t n) -
        Real.log (normalWeightedTail (lowerTiltedTailParameter B t n))| ≤
          2 * lowerRelativeTailConstant * (B * t) := by
  have hv := lower_abs_log_of_abs_sub_one
    (lowerTiltedTailExpectation_relative_error hB hn ht hs) hsmall
  have hJ := normalWeightedTail_pos (lowerTiltedTailParameter B t n)
  have hE : 0 < lowerTiltedTailExpectation B t n := by
    have hh := mul_pos hv.1 hJ
    simpa only [div_mul_cancel₀ _ hJ.ne'] using hh
  refine ⟨hE, ?_⟩
  rw [← Real.log_div hE.ne' hJ.ne']
  simpa only [mul_assoc] using hv.2

end RectangleCLT.Companion
