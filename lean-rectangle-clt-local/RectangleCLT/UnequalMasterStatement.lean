import RectangleCLT.GeneralStatement
import RectangleCLT.ProxyCovariance

/-! The exact unequal-covariance master expression. Optional entries are
omitted at zero covariance parameters; short-scale entries are always
available. These definitions do not assert the analytic estimate. -/

open MeasureTheory

universe u

namespace RectangleCLT

noncomputable section

def masterSecondCoefficient (L b c h : ℝ) : ℝ :=
  optionalMin b (Real.sqrt L / b) (min (Real.sqrt L / c) (1 / h))

def masterThirdCoefficient (L b c a₃ h : ℝ) : ℝ :=
  optionalMin b (L / b ^ 2) (optionalMin a₃ (L / (c * a₃)) (1 / h ^ 2))

def masterFourthCoefficient (L b c a₃ a₄ h : ℝ) : ℝ :=
  optionalMin b (L / (b ^ 2 * h))
    (optionalMin (a₃ * a₄) (L / ((c * a₃ * a₄) ^ (2 / 3 : ℝ) * h))
      (1 / h ^ 3))

def unequalMasterRate (δ γ₃ γ₄ Δ L b c a₃ a₄ cstar h : ℝ) : ℝ :=
  Real.sqrt L *
    (Δ * masterSecondCoefficient L b c h +
      γ₃ * masterThirdCoefficient L b c a₃ h +
      γ₄ * masterFourthCoefficient L b c a₃ a₄ h + h / cstar)

def unequalMasterDataRate {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (δ : ℝ)
    (Q : Matrix (Fin p) (Fin p) ℝ) (h : ℝ) : ℝ :=
  unequalMasterRate δ (gamma3 μ ξ) (gamma4 μ ξ)
    (proxyCovarianceDiscrepancy (covariance μ (sumVector ξ)) Q)
    (dimensionLog p) (fullCovarianceScale Q) (pairGap Q) (a3 Q) (a4 Q)
    (min (pairGap (covariance μ (sumVector ξ))) (pairGap Q)) h

/-- Lemma 10, including every unequal-covariance branch. The gap is
positive at both endpoints; local eigenvalues may vanish. -/
def UnequalMasterEstimate (C : ℝ) : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p n : ℕ), 1 ≤ p → 1 ≤ n →
    ∀ (ξ : Fin n → Ω → Vector p) (δ : ℝ) (A : Matrix (Fin p) (Fin p) ℝ),
      BoundedIndependentHypotheses μ ξ δ →
      (∀ j, covariance μ (sumVector ξ) j j = 1) →
      (∀ j, (A * A.transpose) j j = 1) →
      0 < min (pairGap (covariance μ (sumVector ξ))) (pairGap (A * A.transpose)) →
      ∀ (R : Rect p) (h : ℝ), 12 * δ ≤ h →
        rectangleError μ (sumVector ξ) A R ≤
          C * unequalMasterDataRate μ ξ δ (A * A.transpose) h

theorem le_mul_optionalMin {x C parameter candidate fallback : ℝ}
    (hC : 0 ≤ C) (hf : x ≤ C * fallback)
    (hc : 0 < parameter → x ≤ C * candidate) :
    x ≤ C * optionalMin parameter candidate fallback := by
  unfold optionalMin
  split_ifs with hp
  · rw [mul_min_of_nonneg _ _ hC]
    exact le_min (hc hp) hf
  · exact hf

theorem masterSecondCoefficient_nonneg {L b c h : ℝ}
    (hc : 0 < c) (hh : 0 < h) : 0 ≤ masterSecondCoefficient L b c h := by
  apply optionalMin_nonneg
  · exact le_min (by positivity) (by positivity)
  · intro hb
    positivity

theorem masterThirdCoefficient_nonneg {L b c a₃ h : ℝ}
    (hL : 0 ≤ L) (hc : 0 < c) (hh : 0 < h) :
    0 ≤ masterThirdCoefficient L b c a₃ h := by
  apply optionalMin_nonneg
  · apply optionalMin_nonneg
    · positivity
    · intro ha₃
      positivity
  · intro hb
    positivity

theorem masterFourthCoefficient_nonneg {L b c a₃ a₄ h : ℝ}
    (hL : 0 ≤ L) (hc : 0 < c) (hh : 0 < h) :
    0 ≤ masterFourthCoefficient L b c a₃ a₄ h := by
  apply optionalMin_nonneg
  · apply optionalMin_nonneg
    · positivity
    · intro ha₃₄
      have hprod : 0 ≤ c * a₃ * a₄ := by
        simpa only [mul_assoc] using mul_nonneg hc.le ha₃₄.le
      exact div_nonneg hL (mul_nonneg (Real.rpow_nonneg hprod _) hh.le)
  · intro hb
    positivity

end

end RectangleCLT
