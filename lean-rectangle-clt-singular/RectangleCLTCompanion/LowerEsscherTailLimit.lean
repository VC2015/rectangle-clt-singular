import RectangleCLTCompanion.LowerRelativeTailError

/-! Exact scalar tail factorization and its limit consequence. The
probability on the left is taken under the genuine original product law;
the change of measure and the Berry--Esseen step are proved imports. -/

open MeasureTheory ProbabilityTheory Set Filter

namespace RectangleCLT.Companion

noncomputable section

theorem lower_esscher_relative_tail_factorization {B : ℝ} (hB : 1 ≤ B)
    (t x : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    (lowerScalarArrayLaw B n).real {z | n * lowerTiltMean B t < lowerScalarSum z} /
        standardNormalUpperTail x =
      Real.exp (n * cgf id (lowerTwoPointLaw B) t - t * (n * lowerTiltMean B t) + x ^ 2 / 2) *
        (lowerTiltedTailExpectation B t n / normalWeightedTail (lowerTiltedTailParameter B t n)) *
        (normalWeightedTail (lowerTiltedTailParameter B t n) / normalWeightedTail x) := by
  rw [lowerScalarArrayLaw_strict_tail_standardized hB t hn,
    standardNormalUpperTail_eq_exp_mul_weighted]
  change (Real.exp _ * lowerTiltedTailExpectation B t n) /
    (Real.exp (-x ^ 2 / 2) * normalWeightedTail x) = _
  rw [Real.exp_add, show -x ^ 2 / 2 = -(x ^ 2 / 2) by ring, Real.exp_neg]
  field_simp [(normalWeightedTail_pos x).ne',
    (normalWeightedTail_pos (lowerTiltedTailParameter B t n)).ne', (Real.exp_pos (x ^ 2 / 2)).ne']
  <;> ring

theorem lower_esscher_relative_tail_tendsto {B t x : ℕ → ℝ} {N : ℕ → ℕ} {κ : ℝ}
    (hB : ∀ᶠ k in atTop, 1 ≤ B k) (hN : ∀ᶠ k in atTop, 1 ≤ N k)
    (ht : ∀ᶠ k in atTop, 0 < t k)
    (hs : ∀ᶠ k in atTop, 1 ≤ lowerTiltedTailParameter (B k) (t k) (N k))
    (hsmall : Tendsto (fun k => B k * t k) atTop (nhds 0))
    (hκ : Tendsto (fun k => N k * cgf id (lowerTwoPointLaw (B k)) (t k) -
      t k * (N k * lowerTiltMean (B k) (t k)) + (x k) ^ 2 / 2) atTop (nhds κ))
    (hJ : Tendsto (fun k => normalWeightedTail (lowerTiltedTailParameter (B k) (t k) (N k)) /
      normalWeightedTail (x k)) atTop (nhds 1)) :
    Tendsto (fun k =>
      (lowerScalarArrayLaw (B k) (N k)).real
        {z | N k * lowerTiltMean (B k) (t k) < lowerScalarSum z} /
          standardNormalUpperTail (x k)) atTop (nhds (Real.exp κ)) := by
  have he := (Real.continuous_exp.tendsto κ).comp hκ
  have hh := (he.mul (lower_tilted_weight_relative_tendsto hB hN ht hs hsmall)).mul hJ
  simp only [mul_one] at hh
  apply hh.congr'
  filter_upwards [hB, hN] with k hkB hkN
  exact (lower_esscher_relative_tail_factorization hkB (t k) (x k) hkN).symm

end

end RectangleCLT.Companion
