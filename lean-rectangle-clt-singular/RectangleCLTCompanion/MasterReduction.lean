import RectangleCLTCompanion.Rates
import RectangleCLTCompanion.Optimization

/-!
# Conditional assembly for the unrestricted companion

The reductions below check the passage from variational estimates to the
exact stated rates. `SharpMainAssembly.lean` and `SharpMain.lean` supply the
actual estimates and close the unconditional companion CLTs.
-/

open MeasureTheory

universe u

namespace RectangleCLT.Companion

noncomputable section

/-- The main analytic bound required in Appendix D, for every admissible
bandwidth and every rectangle. No covariance nondegeneracy is assumed. -/
def VariationalEstimate (a C : ℝ) : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p n : ℕ), 1 ≤ p → 1 ≤ n →
    ∀ (ξ : Fin n → Ω → Vector p) (δ : ℝ) (A : Matrix (Fin p) (Fin p) ℝ),
      BoundedIndependentHypotheses μ ξ δ →
      (∀ j, covariance μ (sumVector ξ) j j = 1) →
      A * A.transpose = covariance μ (sumVector ξ) →
      ∀ (R : Rect p) (h : ℝ), a * δ ≤ h →
        rectangleError μ (sumVector ξ) A R ≤ C *
          (δ * dimensionLog p * Real.sqrt (dimensionLog p) +
            δ ^ 2 * (dimensionLog p * Real.sqrt (dimensionLog p)) / h *
              comparisonLog (dimensionLog p) h +
            h * Real.sqrt (dimensionLog p) *
              kappa (dimensionLog p) (pairGap (covariance μ (sumVector ξ))))

/-- The fourth-order-only analytic obligation when the full aggregate
third-moment tensor vanishes. It includes all mixed third moments. -/
def ZeroSkewVariationalEstimate (a C : ℝ) : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p n : ℕ), 1 ≤ p → 1 ≤ n →
    ∀ (ξ : Fin n → Ω → Vector p) (δ : ℝ) (A : Matrix (Fin p) (Fin p) ℝ),
      BoundedIndependentHypotheses μ ξ δ →
      (∀ j, covariance μ (sumVector ξ) j j = 1) →
      A * A.transpose = covariance μ (sumVector ξ) →
      AggregateThirdMomentsVanish μ ξ →
      ∀ (R : Rect p) (h : ℝ), a * δ ≤ h →
        rectangleError μ (sumVector ξ) A R ≤ C *
          (δ ^ 2 * (dimensionLog p * Real.sqrt (dimensionLog p)) / h *
              (1 + comparisonLog (dimensionLog p) h) +
            h * Real.sqrt (dimensionLog p) *
              kappa (dimensionLog p) (pairGap (covariance μ (sumVector ξ))))

/-- Combining any raw rate bound with the probability bound by one.
The enlarged constant also handles the saturated regime. -/
theorem saturate_rate {error rate C : ℝ} (herror : error ≤ 1)
    (hrate : 0 ≤ rate) (hbound : error ≤ C * rate) :
    error ≤ max 1 C * min 1 rate := by
  by_cases hbig : 1 ≤ rate
  · rw [min_eq_left hbig, mul_one]
    exact herror.trans (le_max_left _ _)
  · rw [min_eq_right (le_of_not_ge hbig)]
    exact hbound.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hrate)

/-- A proved variational estimate would imply the gap-sensitive CLT.
The analytic estimate is explicitly present as `hmaster` in this theorem. -/
theorem gapSensitiveCLT_of_variational {a C : ℝ}
    (ha : 1 ≤ a) (hC : 0 ≤ C) (hmaster : VariationalEstimate.{u} a C) :
    GapSensitiveCLT.{u} (max 1 (C * (a + 3 / a))) := by
  intro Ω _ μ _ p n hp hn ξ δ A hdata hunit hfactor R
  let L := dimensionLog p
  let κ := kappa L (pairGap (covariance μ (sumVector ξ)))
  let E := gapLog L δ κ
  have hδ := hdata.delta_pos hp hunit
  have hL1 : 1 ≤ L := log_exp_mul_nat_ge_one hp
  have hL : 0 < L := by linarith
  have hκ : 0 < κ := kappa_pos hL
  have hκL : κ ≤ L := kappa_le _ _
  have hE : 1 ≤ E := one_le_gapLog _ _ _
  have hlog : max 0 (Real.log (Real.sqrt κ / (δ * L))) ≤ E := by
    dsimp [E, gapLog, logPlus]
    linarith
  have hm := gap_rate_of_variational ha hC hδ hL hκ hκL hE hlog
    (fun h hh => hmaster μ p n hp hn ξ δ A hdata hunit hfactor R h hh)
  have hK : 1 ≤ a + 3 / a := by
    have hapos : 0 < a := by linarith
    have : 0 ≤ 3 / a := div_nonneg (by norm_num) hapos.le
    linarith
  have hx : 0 ≤ δ * L * Real.sqrt L := by positivity
  have hraw : rectangleError μ (sumVector ξ) A R ≤
      (C * (a + 3 / a)) * gapRate δ L (pairGap (covariance μ (sumVector ξ))) := by
    apply hm.trans
    have hmul := mul_le_mul_of_nonneg_right hK hx
    have hpw := rpow_three_halves_eq_mul_sqrt hL
    unfold gapRate
    rw [hpw]
    dsimp only [κ, E] at hm ⊢
    nlinarith [mul_le_mul_of_nonneg_left hmul hC]
  exact saturate_rate (rectangleError_le_one μ (sumVector ξ) A R)
    (gapRate_nonneg hδ.le hL.le) hraw

/-- The cancellation CLT also remains conditional on its fourth-order
variational estimate; the probability inputs contain no such estimate. -/
theorem zeroSkewCLT_of_variational {a C : ℝ}
    (ha : 1 ≤ a) (hC : 0 ≤ C) (hmaster : ZeroSkewVariationalEstimate.{u} a C) :
    ZeroSkewCLT.{u} (max 1 (C * (a + 3 / a))) := by
  intro Ω _ μ _ p n hp hn ξ δ A hdata hunit hfactor hthird R
  let L := dimensionLog p
  let κ := kappa L (pairGap (covariance μ (sumVector ξ)))
  let E := gapLog L δ κ
  have hδ := hdata.delta_pos hp hunit
  have hL1 : 1 ≤ L := log_exp_mul_nat_ge_one hp
  have hL : 0 < L := by linarith
  have hκ : 0 < κ := kappa_pos hL
  have hκL : κ ≤ L := kappa_le _ _
  have hE : 1 ≤ E := one_le_gapLog _ _ _
  have hlog : max 0 (Real.log (Real.sqrt κ / (δ * L))) ≤ E := by
    dsimp [E, gapLog, logPlus]
    linarith
  have hm := zeroSkew_rate_of_variational ha hC hδ hL hκ hκL hE hlog
    (fun h hh => hmaster μ p n hp hn ξ δ A hdata hunit hfactor hthird R h hh)
  have hraw : rectangleError μ (sumVector ξ) A R ≤
      (C * (a + 3 / a)) * zeroSkewRate δ L (pairGap (covariance μ (sumVector ξ))) := by
    simpa only [zeroSkewRate, κ, E] using hm
  exact saturate_rate (rectangleError_le_one μ (sumVector ξ) A R)
    (zeroSkewRate_nonneg hδ.le hL.le) hraw

end

end RectangleCLT.Companion
