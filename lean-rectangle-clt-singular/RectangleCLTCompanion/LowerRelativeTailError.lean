import RectangleCLTCompanion.LowerChangeOfMeasure
import RectangleCLTCompanion.WeightedGaussianTail

/-! Relative control of the actual tilted strict-tail expectation. The
error is of order B times the scalar tilt, with no logarithm of n. -/

open MeasureTheory ProbabilityTheory Set Filter

namespace RectangleCLT.Companion

noncomputable section

def lowerTiltedTailParameter (B t : ℝ) (n : ℕ) : ℝ :=
  t * (Real.sqrt n * Real.sqrt (lowerTiltVariance B t))

def lowerTiltedTailExpectation (B t : ℝ) (n : ℕ) : ℝ :=
  ∫ z, lowerStrictTailWeight (lowerTiltedTailParameter B t n)
    (lowerTiltedStandardizedSum B t z) ∂lowerTiltedArrayLaw B t n

def lowerRelativeTailConstant : ℝ :=
  8 * scalarBerryEsseenConstant / standardNormalPDF 0

theorem lowerRelativeTailConstant_pos : 0 < lowerRelativeTailConstant := by
  exact div_pos (mul_pos (by norm_num) scalarBerryEsseenConstant_pos) (standardNormalPDF_pos 0)

theorem normalWeightedTail_ge_simple {s : ℝ} (hs : 1 ≤ s) :
    standardNormalPDF 0 / (2 * s) ≤ normalWeightedTail s := by
  have hs0 : 0 < s := by linarith
  apply le_trans _ (normalWeightedTail_mills_lower hs0)
  apply (div_le_div_iff₀ (by positivity : 0 < 2 * s) (by positivity : 0 < s ^ 2 + 1)).mpr
  have hp := standardNormalPDF_pos 0
  have hsq : 1 ≤ s ^ 2 := by nlinarith
  nlinarith

theorem lowerTiltedTailExpectation_relative_error {B t : ℝ} (hB : 1 ≤ B)
    {n : ℕ} (hn : 1 ≤ n) (ht : 0 < t)
    (hs : 1 ≤ lowerTiltedTailParameter B t n) :
    |lowerTiltedTailExpectation B t n / normalWeightedTail (lowerTiltedTailParameter B t n) - 1| ≤
      lowerRelativeTailConstant * (B * t) := by
  have hBp : 0 < B := by linarith
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hden : 0 < Real.sqrt n * Real.sqrt (lowerTiltVariance B t) :=
    mul_pos (Real.sqrt_pos.mpr hnpos) (Real.sqrt_pos.mpr (lowerTiltVariance_pos hBp t))
  have hspos : 0 < lowerTiltedTailParameter B t n := mul_pos ht hden
  have hJ := normalWeightedTail_pos (lowerTiltedTailParameter B t n)
  have hh := lowerTiltedStandardizedSum_strict_weighted_tail hB t hn hspos
  rw [← normalWeightedTail_eq_integral] at hh
  change |lowerTiltedTailExpectation B t n - normalWeightedTail (lowerTiltedTailParameter B t n)| ≤ _ at hh
  have hid : lowerTiltedTailExpectation B t n / normalWeightedTail (lowerTiltedTailParameter B t n) - 1 =
      (lowerTiltedTailExpectation B t n - normalWeightedTail (lowerTiltedTailParameter B t n)) /
        normalWeightedTail (lowerTiltedTailParameter B t n) := by field_simp
  rw [hid, abs_div, abs_of_pos hJ]
  apply (div_le_iff₀ hJ).mpr
  calc
    _ ≤ 2 * (scalarBerryEsseenConstant * (lowerTiltedNormalization B t n * (2 * B))) := hh
    _ = (lowerRelativeTailConstant * (B * t)) *
        (standardNormalPDF 0 / (2 * lowerTiltedTailParameter B t n)) := by
      unfold lowerRelativeTailConstant lowerTiltedNormalization lowerTiltedTailParameter
      field_simp [(standardNormalPDF_pos 0).ne', ht.ne', hden.ne']
      <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (normalWeightedTail_ge_simple hs)
      (mul_nonneg lowerRelativeTailConstant_pos.le (mul_nonneg hBp.le ht.le))

theorem lower_tilted_weight_relative_tendsto {B t : ℕ → ℝ} {N : ℕ → ℕ}
    (hB : ∀ᶠ k in atTop, 1 ≤ B k) (hN : ∀ᶠ k in atTop, 1 ≤ N k)
    (ht : ∀ᶠ k in atTop, 0 < t k)
    (hs : ∀ᶠ k in atTop, 1 ≤ lowerTiltedTailParameter (B k) (t k) (N k))
    (hsmall : Tendsto (fun k => B k * t k) atTop (nhds 0)) :
    Tendsto (fun k => lowerTiltedTailExpectation (B k) (t k) (N k) /
      normalWeightedTail (lowerTiltedTailParameter (B k) (t k) (N k))) atTop (nhds 1) := by
  have hz : Tendsto (fun k => lowerRelativeTailConstant * (B k * t k)) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hsmall
  have hb : ∀ᶠ k in atTop,
      ‖lowerTiltedTailExpectation (B k) (t k) (N k) /
        normalWeightedTail (lowerTiltedTailParameter (B k) (t k) (N k)) - 1‖ ≤
        lowerRelativeTailConstant * (B k * t k) := by
    filter_upwards [hB, hN, ht, hs] with k hkB hkN hkt hks
    simpa only [Real.norm_eq_abs] using
      lowerTiltedTailExpectation_relative_error hkB hkN hkt hks
  have hh := (squeeze_zero_norm' hb hz).add_const 1
  simpa only [sub_add_cancel, zero_add] using hh

end

end RectangleCLT.Companion
