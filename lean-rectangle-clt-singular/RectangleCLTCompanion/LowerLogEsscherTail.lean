import RectangleCLTCompanion.LowerLogTailError
import RectangleCLTCompanion.LowerEsscherTailLimit

/-! The actual logarithmic tail ratio, decomposed into the Legendre
exponent and the two proved weighted-tail error terms. -/

open MeasureTheory ProbabilityTheory Set

namespace RectangleCLT.Companion

theorem lower_log_esscher_tail {B : ℝ} (hB : 1 ≤ B) (t x : ℝ)
    {n : ℕ} (hn : 1 ≤ n) (hE : 0 < lowerTiltedTailExpectation B t n) :
    Real.log ((lowerScalarArrayLaw B n).real
        {z | n * lowerTiltMean B t < lowerScalarSum z} / standardNormalUpperTail x) =
      (n * cgf id (lowerTwoPointLaw B) t - t * (n * lowerTiltMean B t) + x ^ 2 / 2) +
        (Real.log (lowerTiltedTailExpectation B t n) -
          Real.log (normalWeightedTail (lowerTiltedTailParameter B t n))) +
        (Real.log (normalWeightedTail (lowerTiltedTailParameter B t n)) -
          Real.log (normalWeightedTail x)) := by
  have hJ := normalWeightedTail_pos (lowerTiltedTailParameter B t n)
  have hJx := normalWeightedTail_pos x
  rw [lower_esscher_relative_tail_factorization hB t x hn]
  rw [Real.log_mul (mul_ne_zero (Real.exp_pos _).ne' (div_pos hE hJ).ne')
      (div_pos hJ hJx).ne',
    Real.log_mul (Real.exp_pos _).ne' (div_pos hE hJ).ne',
    Real.log_exp, Real.log_div hE.ne' hJ.ne', Real.log_div hJ.ne' hJx.ne']

theorem lower_log_esscher_tail_error {B t x : ℝ} (hB : 1 ≤ B)
    {n : ℕ} (hn : 1 ≤ n) (ht : 0 < t) (hx : 0 < x)
    (hs : 1 ≤ lowerTiltedTailParameter B t n)
    (hsmall : lowerRelativeTailConstant * (B * t) ≤ 1 / 2) :
    |Real.log ((lowerScalarArrayLaw B n).real
        {z | n * lowerTiltMean B t < lowerScalarSum z} / standardNormalUpperTail x) -
      (n * cgf id (lowerTwoPointLaw B) t - t * (n * lowerTiltMean B t) + x ^ 2 / 2)| ≤
        2 * lowerRelativeTailConstant * (B * t) +
          |lowerTiltedTailParameter B t n - x| / min (lowerTiltedTailParameter B t n) x := by
  have hE := lowerTiltedTailExpectation_log_error hB hn ht hs hsmall
  rw [lower_log_esscher_tail hB t x hn hE.1]
  have hh := (abs_add
    (Real.log (lowerTiltedTailExpectation B t n) -
      Real.log (normalWeightedTail (lowerTiltedTailParameter B t n)))
    (Real.log (normalWeightedTail (lowerTiltedTailParameter B t n)) -
      Real.log (normalWeightedTail x))).trans
    (add_le_add hE.2
      (log_normalWeightedTail_lipschitz (by linarith : 0 < lowerTiltedTailParameter B t n) hx))
  convert hh using 1 <;> congr 1 <;> ring

end RectangleCLT.Companion
