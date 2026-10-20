import RectangleCLT.LocalMoments
import RectangleCLT.LocalOptimization

/-!
# Reduction of the local covariance CLT to its analytic master estimate

The local master estimate uses the intrinsic covariance parameters of the
actual observation sum, with no full spectral lower bound. This file proves
the generic optimization implication. `Main.lean` supplies the master estimate
as `mainCLTMasterEstimate` and proves the resulting main CLT.
-/

open MeasureTheory

universe u

namespace RectangleCLT

/-- The selected local alternatives of the manuscript's master bound, for
actual rectangle probabilities and every admissible bandwidth. The proposition
is proved by `mainCLTMasterEstimate` in `Main.lean`, rather than assumed as an axiom. -/
def LocalMasterEstimate (C : ℝ) : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p n : ℕ), 1 ≤ p → 1 ≤ n →
    ∀ (ξ : Fin n → Ω → Vector p) (δ : ℝ)
      (A : Matrix (Fin p) (Fin p) ℝ),
      BoundedIndependentHypotheses μ ξ δ →
      LocalCovarianceHypotheses (covariance μ (sumVector ξ)) →
      A * A.transpose = covariance μ (sumVector ξ) →
      ∀ (R : Rect p) (h : ℝ), 12 * δ ≤ h →
        let Q := covariance μ (sumVector ξ)
        rectangleError μ (sumVector ξ) A R ≤ C *
          (gamma3 μ ξ * dimensionLog p * Real.sqrt (dimensionLog p) / (pairGap Q * a3 Q) +
            gamma4 μ ξ * dimensionLog p * Real.sqrt (dimensionLog p) /
              (h * Real.rpow (pairGap Q * a3 Q * a4 Q) (2 / 3 : ℝ)) +
            h * Real.sqrt (dimensionLog p) / pairGap Q)

/-- A proof of the local analytic master estimate suffices to establish the
new main theorem with the explicit absolute factor `max 1 (13*C)`.
This generic implication retains its estimate as an assumption; `Main.lean`
provides that assumption by a checked proof. -/
theorem localRectangleCLT_of_master {C : ℝ} (hC : 0 ≤ C)
    (hmaster : LocalMasterEstimate.{u} C) :
    LocalRectangleCLT.{u} (max 1 (13 * C)) := by
  intro Ω _ μ _ p n hp hn ξ δ A hdata hlocal hfactor R
  apply local_rate_of_master
    (hdata.delta_pos hp hlocal.unit_diagonal)
    (gamma3_nonneg μ ξ) (gamma4_nonneg μ ξ)
    (log_exp_mul_nat_ge_one hp)
    (hlocal.pairGap_pos hp) (hlocal.a3_pos hp) hlocal.a4_pos hC
    (rectangleError_le_one μ (sumVector ξ) A R)
  exact hmaster μ p n hp hn ξ δ A hdata hlocal hfactor R

/-- Conditional existential form with the absolute constant outside all data
quantifiers. This theorem retains its local master-estimate assumption. -/
theorem localRectangleCLTExists_of_master {C : ℝ} (hC : 0 ≤ C)
    (hmaster : LocalMasterEstimate.{u} C) : LocalRectangleCLTExists.{u} :=
  ⟨max 1 (13 * C), le_max_left _ _, localRectangleCLT_of_master hC hmaster⟩

end RectangleCLT
