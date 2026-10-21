import RectangleCLT.LocalStatement
import RectangleCLT.GlobalCovariance

/-! The exact positive-pair-gap general bound. A linear entry is omitted
when its covariance denominator vanishes; the fractional-moment entries
remain available without three- or four-coordinate nondegeneracy. -/

open MeasureTheory

universe u

namespace RectangleCLT

noncomputable section

/-- Minimize over an optional covariance-dependent entry and an always
available entry. The former is available only for a positive parameter. -/
def optionalMin (parameter candidate fallback : ℝ) : ℝ :=
  if 0 < parameter then min candidate fallback else fallback

theorem optionalMin_le_fallback (parameter candidate fallback : ℝ) :
    optionalMin parameter candidate fallback ≤ fallback := by
  unfold optionalMin
  split_ifs
  · exact min_le_right _ _
  · exact le_rfl

theorem optionalMin_le_candidate {parameter : ℝ} (h : 0 < parameter)
    (candidate fallback : ℝ) : optionalMin parameter candidate fallback ≤ candidate := by
  rw [optionalMin, if_pos h]
  exact min_le_left _ _

theorem optionalMin_nonneg {parameter candidate fallback : ℝ}
    (hfall : 0 ≤ fallback) (hcand : 0 < parameter → 0 ≤ candidate) :
    0 ≤ optionalMin parameter candidate fallback := by
  unfold optionalMin
  split_ifs with hp
  · exact le_min (hcand hp) hfall
  · exact hfall

/-- The exact three alternatives in the general cubic rate `R₃`. -/
def generalThirdRate (γ₃ L b c a₃ : ℝ) : ℝ :=
  optionalMin b (γ₃ * L * Real.sqrt L / b ^ 2)
    (optionalMin a₃ (γ₃ * L * Real.sqrt L / (c * a₃))
      (γ₃ ^ (1 / 3 : ℝ) * Real.sqrt L / c ^ (2 / 3 : ℝ)))

/-- The exact three alternatives in the general fourth-moment rate `R₄`.
Here `b` is a square root and `a₃,a₄` are eigenvalues. -/
def generalFourthRate (γ₄ L b c a₃ a₄ : ℝ) : ℝ :=
  optionalMin b (Real.sqrt γ₄ * L / (b * Real.sqrt c))
    (optionalMin (a₃ * a₄)
      (Real.sqrt γ₄ * L / (c ^ (5 / 6 : ℝ) * (a₃ * a₄) ^ (1 / 3 : ℝ)))
      (γ₄ ^ (1 / 4 : ℝ) * Real.sqrt L / c ^ (3 / 4 : ℝ)))

def generalCoefficientRate (δ γ₃ γ₄ L b c a₃ a₄ : ℝ) : ℝ :=
  generalThirdRate γ₃ L b c a₃ + generalFourthRate γ₄ L b c a₃ a₄ +
    δ * Real.sqrt L / c

theorem generalThirdRate_nonneg {γ₃ L b c a₃ : ℝ}
    (hγ₃ : 0 ≤ γ₃) (hL : 0 ≤ L) (hc : 0 < c) :
    0 ≤ generalThirdRate γ₃ L b c a₃ := by
  unfold generalThirdRate
  apply optionalMin_nonneg
  · apply optionalMin_nonneg
    · exact div_nonneg (mul_nonneg (Real.rpow_nonneg hγ₃ _) (Real.sqrt_nonneg _))
        (Real.rpow_nonneg hc.le _)
    · intro ha₃
      positivity
  · intro hb
    positivity

theorem generalFourthRate_nonneg {γ₄ L b c a₃ a₄ : ℝ}
    (hγ₄ : 0 ≤ γ₄) (hL : 0 ≤ L) (hc : 0 < c) :
    0 ≤ generalFourthRate γ₄ L b c a₃ a₄ := by
  unfold generalFourthRate
  apply optionalMin_nonneg
  · apply optionalMin_nonneg
    · positivity
    · intro ha₃₄
      exact div_nonneg (mul_nonneg (Real.sqrt_nonneg _) hL)
        (mul_nonneg (Real.rpow_nonneg hc.le _) (Real.rpow_nonneg ha₃₄.le _))
  · intro hb
    positivity

theorem generalCoefficientRate_nonneg {δ γ₃ γ₄ L b c a₃ a₄ : ℝ}
    (hδ : 0 ≤ δ) (hγ₃ : 0 ≤ γ₃) (hγ₄ : 0 ≤ γ₄)
    (hL : 0 ≤ L) (hc : 0 < c) :
    0 ≤ generalCoefficientRate δ γ₃ γ₄ L b c a₃ a₄ :=
  add_nonneg
    (add_nonneg (generalThirdRate_nonneg hγ₃ hL hc) (generalFourthRate_nonneg hγ₄ hL hc))
    (div_nonneg (mul_nonneg hδ (Real.sqrt_nonneg _)) hc.le)

def generalBoundedRate {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (δ : ℝ)
    (Q : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  generalCoefficientRate δ (gamma3 μ ξ) (gamma4 μ ξ) (dimensionLog p)
    (fullCovarianceScale Q) (pairGap Q) (a3 Q) (a4 Q)

/-- Proposition 2 with its exact pair-gap-only hypothesis. No local
covariance positivity and no analytic estimate is part of the data. -/
def GeneralRectangleCLT (C : ℝ) : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p n : ℕ), 1 ≤ p → 1 ≤ n →
    ∀ (ξ : Fin n → Ω → Vector p) (δ : ℝ) (A : Matrix (Fin p) (Fin p) ℝ),
      BoundedIndependentHypotheses μ ξ δ →
      (∀ j, covariance μ (sumVector ξ) j j = 1) →
      0 < pairGap (covariance μ (sumVector ξ)) →
      A * A.transpose = covariance μ (sumVector ξ) →
      ∀ R : Rect p,
        rectangleError μ (sumVector ξ) A R ≤
          C * min 1 (generalBoundedRate μ ξ δ (covariance μ (sumVector ξ)))

def GeneralRectangleCLTExists : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ GeneralRectangleCLT.{u} C

end

end RectangleCLT
