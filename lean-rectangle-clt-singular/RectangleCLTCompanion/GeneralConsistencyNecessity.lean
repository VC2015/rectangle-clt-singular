import RectangleCLTCompanion.LowerCriticalObstruction
import RectangleCLTCompanion.LowerCriticalDimension
import RectangleCLTCompanion.LowerAtomConsistency
import RectangleCLTCompanion.ConsistencyULift

/-!
# Necessity of the full fixed-gap consistency criterion

An atom first forces the normalized envelope to vanish. Every positive
critical dimension is then ruled out by a genuine skewed product law and
a partial rectangle; this forces the exact logarithmic criterion.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

universe u

namespace RectangleCLT.Companion

noncomputable section

lemma fixedGap_uniformConsistency_eventually_le_critical
    {c₀ : ℝ} {B : ℕ → ℝ} {p : ℕ → ℕ} (hc₁ : c₀ ≤ 1)
    (hB : ∀ n, 2 ≤ B n)
    (hδ : Tendsto (fun n : ℕ => B n / Real.sqrt n) atTop (𝓝 0))
    (hcons : FixedGapUniformConsistency.{0} c₀ B p)
    {a : ℝ} (ha : 0 < a) :
    ∀ᶠ n in atTop, p n ≤ lowerCriticalDimension a (B n / Real.sqrt n) := by
  let δ : ℕ → ℝ := fun n => B n / Real.sqrt n
  let q : ℕ → ℕ := fun n => lowerCriticalDimension a (δ n)
  have hpos : ∀ᶠ n in atTop, 0 < δ n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact div_pos (by linarith only [hB n]) (Real.sqrt_pos.2 (by exact_mod_cast hn))
  have hq : Tendsto q atTop atTop := lowerCriticalDimension_tendsto_atTop ha hδ hpos
  have hr : Tendsto (fun n => lowerSkewRate (B n) (q n) n) atTop (𝓝 (a^(3/2 : ℝ))) := by
    apply (lowerCriticalDimension_rate_tendsto ha hδ hpos).congr
    intro n
    unfold lowerSkewRate q δ
    ring
  have hapos : 0 < a^(3/2 : ℝ) := Real.rpow_pos_of_pos ha _
  have hε := lowerCriticalError_pos hapos
  have hdetect := lowerCritical_rectangleError_eventually_ge hB hq hapos hr
  filter_upwards [hcons _ hε, hdetect, eventually_ge_atTop 1] with n hc hdn hn
  by_contra hnot
  have hqp : q n ≤ p n := (lt_of_not_ge hnot).le
  have hBn : 1 ≤ B n := by linarith only [hB n]
  have hcov : covariance (lowerArrayLaw (B n) n (p n))
      (sumVector (lowerNormalizedRows (n := n) (p := p n))) = 1 :=
    lowerNormalizedRows_covariance hBn hn
  have hunit : ∀ j, covariance (lowerArrayLaw (B n) n (p n))
      (sumVector (lowerNormalizedRows (n := n) (p := p n))) j j = 1 := by
    intro j
    rw [hcov]
    simp
  have hgap : c₀ ≤ pairGap (covariance (lowerArrayLaw (B n) n (p n))
      (sumVector (lowerNormalizedRows (n := n) (p := p n)))) := by
    rw [hcov, pairGap_identity]
    exact hc₁
  have hfactor : (1 : Matrix (Fin (p n)) (Fin (p n)) ℝ) * 1 =
      covariance (lowerArrayLaw (B n) n (p n))
        (sumVector (lowerNormalizedRows (n := n) (p := p n))) := by rw [hcov]; simp
  have hupper := hc (lowerArrayLaw (B n) n (p n))
    (lowerNormalizedRows (n := n) (p := p n)) 1
    (lowerNormalizedRows_boundedIndependent hBn n (p n)) hunit hgap
    (by simpa using hfactor)
    (partialMaximumRectangle (p n) (q n) (normalMaxThreshold (q n)))
  exact (not_lt_of_ge (hdn (p n) hqp)) hupper

/-- Necessity holds uniformly over all probability spaces and all
independent centered observations, for arbitrary envelopes `B_n ≥ 2`. -/
theorem fixedGapUniformConsistency_necessary
    {c₀ : ℝ} {B : ℕ → ℝ} {p : ℕ → ℕ} (hc₁ : c₀ ≤ 1)
    (hB : ∀ n, 2 ≤ B n) (hp : ∀ n, 1 ≤ p n)
    (hcons : FixedGapUniformConsistency.{u} c₀ B p) :
    Tendsto (fun n : ℕ => B n / Real.sqrt n * dimensionLog (p n)^(3/2 : ℝ))
      atTop (𝓝 0) := by
  have hcons0 := fixedGapUniformConsistency_universe_zero hcons
  have hδ := fixedGapUniformConsistency_envelope_tendsto_zero hc₁ hB hp hcons0
  have hpos : ∀ᶠ n in atTop, 0 < B n / Real.sqrt n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact div_pos (by linarith only [hB n]) (Real.sqrt_pos.2 (by exact_mod_cast hn))
  apply lowerCriticalDimension_caps_imply_rate_tendsto_zero hp hδ hpos
  intro a ha
  exact fixedGap_uniformConsistency_eventually_le_critical hc₁ hB hδ hcons0 ha

end

end RectangleCLT.Companion
