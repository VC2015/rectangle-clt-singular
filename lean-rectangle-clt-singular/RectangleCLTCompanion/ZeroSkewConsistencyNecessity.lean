import RectangleCLTCompanion.RademacherMaximumLimit
import RectangleCLTCompanion.RademacherArray
import RectangleCLTCompanion.ConsistencyULift

/-!
# Necessity of the zero-skew dimensional threshold

The argument uses the actual Rademacher product laws. A partial rectangle
selects a critical number of coordinates inside any larger dimension.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

universe u

namespace RectangleCLT.Companion

noncomputable section

lemma zeroSkew_uniformConsistency_eventually_le_critical
    {c₀ B : ℝ} {p : ℕ → ℕ} (hc₁ : c₀ ≤ 1) (hB : 1 ≤ B)
    (hcons : ZeroSkewFixedGapUniformConsistency.{0} c₀ B p)
    {a : ℝ} (ha : 0 < a) :
    ∀ᶠ n in atTop, p n ≤ rademacherCriticalDimension a n := by
  have hdpos := rademacherCriticalDiscrepancy_pos ha
  have hε : 0 < rademacherCriticalDiscrepancy a / 2 := half_pos hdpos
  have hlim := tendsto_rademacherCriticalDimension_maximum_discrepancy ha
  filter_upwards [hcons _ hε,
    hlim.eventually (eventually_gt_nhds (half_lt_self hdpos)), eventually_ge_atTop 1]
    with n hc hd hn
  by_contra hpn
  have hqp : rademacherCriticalDimension a n ≤ p n := (lt_of_not_ge hpn).le
  let q := rademacherCriticalDimension a n
  let x := normalMaxThreshold q
  have hcov : covariance (lowerArrayLaw 1 n (p n))
      (sumVector (lowerNormalizedRows (n := n) (p := p n))) = 1 :=
    rademacherNormalizedRows_covariance hn
  have hunit : ∀ j, covariance (lowerArrayLaw 1 n (p n))
      (sumVector (lowerNormalizedRows (n := n) (p := p n))) j j = 1 := by
    intro j
    rw [hcov]
    simp
  have hgap : c₀ ≤ pairGap (covariance (lowerArrayLaw 1 n (p n))
      (sumVector (lowerNormalizedRows (n := n) (p := p n)))) := by
    rw [hcov, rademacher_pairGap_identity]
    exact hc₁
  have hfactor : (1 : Matrix (Fin (p n)) (Fin (p n)) ℝ) * 1 =
      covariance (lowerArrayLaw 1 n (p n))
        (sumVector (lowerNormalizedRows (n := n) (p := p n))) := by rw [hcov]; simp
  have hh := hc (lowerArrayLaw 1 n (p n))
    (lowerNormalizedRows (n := n) (p := p n)) 1
    (rademacherNormalizedRows_boundedIndependent hB n (p n)) hunit hgap
    (by simpa using hfactor) rademacherNormalizedRows_aggregateThird
    (partialMaximumRectangle (p n) q x)
  rw [lowerArrayLaw_partialMaximum_rectangleError 1 n hqp x,
    ← lowerCoordinateCDF_eq_one_sub_upperTail,
    standardNormalCDF_normalMaxThreshold_pow (rademacherCriticalDimension_pos ha.le n)] at hh
  change |lowerCoordinateCDF 1 n (normalMaxThreshold (rademacherCriticalDimension a n))^
      rademacherCriticalDimension a n - Real.exp (-1)| < _ at hh
  linarith [le_abs_self (lowerCoordinateCDF 1 n
    (normalMaxThreshold (rademacherCriticalDimension a n))^
      rademacherCriticalDimension a n - Real.exp (-1))]

/-- For every fixed envelope `B ≥ 1`, uniform zero-skew consistency
requires `log p = o(sqrt n)`. The probability class is selected before
its concrete Rademacher law or its detecting rectangle. -/
theorem zeroSkewFixedGapUniformConsistency_necessary
    {c₀ B : ℝ} {p : ℕ → ℕ} (hc₁ : c₀ ≤ 1) (hB : 1 ≤ B)
    (hp : ∀ n, 1 ≤ p n)
    (hcons : ZeroSkewFixedGapUniformConsistency.{u} c₀ B p) :
    Tendsto (fun n : ℕ => Real.log (p n : ℝ) / Real.sqrt n) atTop (𝓝 0) := by
  apply tendsto_log_dimension_div_sqrt_of_eventually_le_critical hp
  intro a ha
  exact zeroSkew_uniformConsistency_eventually_le_critical hc₁ hB
    (zeroSkewFixedGapUniformConsistency_universe_zero hcons) ha

end

end RectangleCLT.Companion
