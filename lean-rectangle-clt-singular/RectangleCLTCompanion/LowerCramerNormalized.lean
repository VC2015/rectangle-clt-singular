import RectangleCLTCompanion.LowerCramerBound
import RectangleCLTCompanion.LowerMaxCDFProduct

/-! The Cramér estimate in the manuscript's normalized-sum notation. -/

open Set

namespace RectangleCLT.Companion

noncomputable section

private theorem normalized_cubic_algebra {N s x k : ℝ} (hs : s ≠ 0) (hN : s ^ 2 = N) :
    N * k * (x / s) ^ 3 / 6 = k * x ^ 3 / (6 * s) := by
  rw [← hN]
  field_simp
  <;> ring

private theorem normalized_fourth_algebra {N s x B : ℝ} (hs : s ≠ 0) (hN : s ^ 2 = N) :
    N * B ^ 2 * (x / s) ^ 4 = B ^ 2 * x ^ 4 / N := by
  rw [← hN]
  field_simp
  <;> ring

private theorem normalized_threshold_algebra {N s x : ℝ} (hs : s ≠ 0) (hN : s ^ 2 = N) :
    N * (x / s) = s * x := by
  rw [← hN]
  field_simp
  <;> ring

theorem lowerCoordinateUpperTail_cramer_bound {B x : ℝ} (hB : 1 ≤ B)
    {n : ℕ} (hn : 1 ≤ n) (hx : 2 ≤ x)
    (hsmall : lowerCramerSmallConstant * (B * (x / Real.sqrt n)) ≤ 1) :
    |Real.log (lowerCoordinateUpperTail B n x / standardNormalUpperTail x) -
      (B - B⁻¹) * x ^ 3 / (6 * Real.sqrt n)| ≤
        lowerCramerRemainderConstant *
          (B * (x / Real.sqrt n) + B ^ 2 * x ^ 4 / n) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hs := Real.sqrt_pos.mpr hnpos
  have hnorm : Real.sqrt n * (x / Real.sqrt n) = x := by field_simp
  have hthreshold : (n : ℝ) * (x / Real.sqrt n) = Real.sqrt n * x := by
    exact normalized_threshold_algebra hs.ne' (Real.sq_sqrt hnpos.le)
  have hh := lowerTwoPoint_cramer_bound hB (div_pos (by linarith : 0 < x) hs)
    hn (by simpa only [hnorm] using hx) hsmall
  rw [hnorm, normalized_cubic_algebra hs.ne' (Real.sq_sqrt hnpos.le),
    normalized_fourth_algebra hs.ne' (Real.sq_sqrt hnpos.le)] at hh
  rw [lowerCoordinateUpperTail_eq_raw B hn]
  simpa only [hthreshold, lowerScalarSum] using hh

theorem lowerCoordinateUpperTail_cramer_pos {B x : ℝ} (hB : 1 ≤ B)
    {n : ℕ} (hn : 1 ≤ n) (hx : 2 ≤ x)
    (hsmall : lowerCramerSmallConstant * (B * (x / Real.sqrt n)) ≤ 1) :
    0 < lowerCoordinateUpperTail B n x := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hs := Real.sqrt_pos.mpr hnpos
  have hnorm : Real.sqrt n * (x / Real.sqrt n) = x := by field_simp
  have hthreshold : (n : ℝ) * (x / Real.sqrt n) = Real.sqrt n * x := by
    exact normalized_threshold_algebra hs.ne' (Real.sq_sqrt hnpos.le)
  have hh := lowerTwoPoint_cramer_tail_pos hB (div_pos (by linarith : 0 < x) hs)
    hn (by simpa only [hnorm] using hx) hsmall
  rw [lowerCoordinateUpperTail_eq_raw B hn]
  simpa only [hthreshold, lowerScalarSum] using hh

end

end RectangleCLT.Companion
