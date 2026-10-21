import RectangleCLT.ProxyStatement
import RectangleCLT.GeneralRateBounds
import RectangleCLT.GaussianComparisonCoefficient
import RectangleCLT.LocalReduction

/-! Exact general and combined proxy targets. Covariance coefficients are
computed only from the reference matrix. The Gaussian component is genuine
and independent of the entire observation array. -/

open MeasureTheory

universe u

namespace RectangleCLT

noncomputable section

def generalProxyCoefficientRate (δ γ₃ γ₄ Δ L b c a₃ a₄ : ℝ) : ℝ :=
  generalCoefficientRate δ γ₃ γ₄ L b c a₃ a₄ +
    Δ * L * gaussianComparisonCoefficient b c

def refinedProxyCoefficientRate (δ γ₃ γ₄ Δ L b c a₃ a₄ : ℝ) : ℝ :=
  combinedCoefficientRate δ γ₃ γ₄ L b c a₃ a₄ +
    Δ * L * gaussianComparisonCoefficient b c

def generalProxyRate {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (G : Ω → Vector p)
    (δ : ℝ) (Q : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  generalProxyCoefficientRate δ (gamma3 μ ξ) (gamma4 μ ξ)
    (proxyCovarianceDiscrepancy (covariance μ (sumWithGaussian ξ G)) Q)
    (dimensionLog p) (fullCovarianceScale Q) (pairGap Q) (a3 Q) (a4 Q)

def refinedProxyRate {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (G : Ω → Vector p)
    (δ : ℝ) (Q : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  refinedProxyCoefficientRate δ (gamma3 μ ξ) (gamma4 μ ξ)
    (proxyCovarianceDiscrepancy (covariance μ (sumWithGaussian ξ G)) Q)
    (dimensionLog p) (fullCovarianceScale Q) (pairGap Q) (a3 Q) (a4 Q)

/-- Proposition 4: only a positive gap of the fixed proxy is required.
The moment denominators are omitted at zero through the exact `R₃,R₄`. -/
def GeneralCovarianceProxyCLT (C : ℝ) : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p n : ℕ), 1 ≤ p → 1 ≤ n →
    ∀ (ξ : Fin n → Ω → Vector p) (G : Ω → Vector p) (δ : ℝ)
      (B A_S A_Q : Matrix (Fin p) (Fin p) ℝ),
      ProxyHypotheses μ ξ G δ B →
      (∀ j, covariance μ (sumWithGaussian ξ G) j j = 1) →
      (∀ j, (A_Q * A_Q.transpose) j j = 1) →
      0 < pairGap (A_Q * A_Q.transpose) →
      A_S * A_S.transpose = covariance μ (sumWithGaussian ξ G) →
      ∀ R : Rect p,
        max (rectangleError μ (sumWithGaussian ξ G) A_S R)
          (rectangleError μ (sumWithGaussian ξ G) A_Q R) ≤
        C * min 1 (generalProxyRate μ ξ G δ (A_Q * A_Q.transpose))

/-- Proposition 3: combined moment coefficients and the exact minimum
of global and pair-gap covariance costs, under Theorem 2's hypotheses. -/
def RefinedCovarianceProxyCLT (C : ℝ) : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p n : ℕ), 1 ≤ p → 1 ≤ n →
    ∀ (ξ : Fin n → Ω → Vector p) (G : Ω → Vector p) (δ : ℝ)
      (B A_S A_Q : Matrix (Fin p) (Fin p) ℝ),
      ProxyHypotheses μ ξ G δ B →
      (∀ j, covariance μ (sumWithGaussian ξ G) j j = 1) →
      LocalCovarianceHypotheses (A_Q * A_Q.transpose) →
      A_S * A_S.transpose = covariance μ (sumWithGaussian ξ G) →
      ∀ R : Rect p,
        max (rectangleError μ (sumWithGaussian ξ G) A_S R)
          (rectangleError μ (sumWithGaussian ξ G) A_Q R) ≤
        C * min 1 (refinedProxyRate μ ξ G δ (A_Q * A_Q.transpose))

def RefinedCovarianceProxyCLTExists : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ RefinedCovarianceProxyCLT.{u} C

theorem generalProxyCoefficientRate_le_refined
    {δ γ₃ γ₄ Δ L b c a₃ a₄ : ℝ}
    (hγ₃ : 0 ≤ γ₃) (hγ₄ : 0 ≤ γ₄) (hL : 0 ≤ L)
    (hc : 0 < c) (ha₃ : 0 < a₃) (ha₄ : 0 < a₄) :
    generalProxyCoefficientRate δ γ₃ γ₄ Δ L b c a₃ a₄ ≤
      refinedProxyCoefficientRate δ γ₃ γ₄ Δ L b c a₃ a₄ :=
  add_le_add_right (generalCoefficientRate_le_combined hγ₃ hγ₄ hL hc ha₃ ha₄) _

/-- A scalar consequence of the general proxy theorem, with the same
constant. The general theorem premise is deliberately explicit here. -/
theorem refinedCovarianceProxyCLT_of_general {C : ℝ} (hC : 0 ≤ C)
    (hgeneral : GeneralCovarianceProxyCLT.{u} C) : RefinedCovarianceProxyCLT.{u} C := by
  intro Ω _ μ _ p n hp hn ξ G δ B A_S A_Q h hunit hQ hfactor R
  have hc := hQ.pairGap_pos hp
  have hh := hgeneral μ p n hp hn ξ G δ B A_S A_Q h hunit
    hQ.unit_diagonal hc hfactor R
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ hC
  apply min_le_min le_rfl
  exact generalProxyCoefficientRate_le_refined (gamma3_nonneg μ ξ) (gamma4_nonneg μ ξ)
    (zero_le_one.trans (log_exp_mul_nat_ge_one hp)) hc (hQ.a3_pos hp) hQ.a4_pos

theorem refinedProxyCoefficientRate_le_eigenvalue
    {δ γ₃ γ₄ Δ L b c a₃ a₄ : ℝ}
    (hδ : 0 ≤ δ) (hγ₃ : 0 ≤ γ₃) (hΔ : 0 ≤ Δ) (hL : 0 ≤ L)
    (hb : 0 < b) (hbc : b ^ 2 ≤ c) :
    refinedProxyCoefficientRate δ γ₃ γ₄ Δ L b c a₃ a₄ ≤
      (γ₃ * L * Real.sqrt L + Real.sqrt γ₄ * L + δ * Real.sqrt L) / b ^ 2 +
        Δ * L / b := by
  apply add_le_add
    (combinedCoefficientRate_le_eigenvalueRate hδ hγ₃ hL hb hbc)
  exact (mul_le_mul_of_nonneg_left (gaussianComparisonCoefficient_le_global hb)
    (mul_nonneg hΔ hL)).trans_eq (by ring)

/-- Corollary 4 from the refined proxy theorem. Its denominator is the
minimum eigenvalue itself, namely `b²`, while the covariance cost is `ΔL/b`. -/
theorem proxyEigenvalueRectangleCLT_of_refined {C : ℝ} (hC : 0 ≤ C)
    (hrefined : RefinedCovarianceProxyCLT.{u} C)
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p n : ℕ} (hp : 1 ≤ p) (hn : 1 ≤ n)
    (ξ : Fin n → Ω → Vector p) (G : Ω → Vector p) (δ : ℝ)
    (B A_S A_Q : Matrix (Fin p) (Fin p) ℝ)
    (h : ProxyHypotheses μ ξ G δ B)
    (hunit : ∀ j, covariance μ (sumWithGaussian ξ G) j j = 1)
    (hQ : LocalCovarianceHypotheses (A_Q * A_Q.transpose))
    (hfactor : A_S * A_S.transpose = covariance μ (sumWithGaussian ξ G))
    (hb : 0 < fullCovarianceScale (A_Q * A_Q.transpose)) (R : Rect p) :
    let Q := A_Q * A_Q.transpose
    let Δ := proxyCovarianceDiscrepancy (covariance μ (sumWithGaussian ξ G)) Q
    max (rectangleError μ (sumWithGaussian ξ G) A_S R)
      (rectangleError μ (sumWithGaussian ξ G) A_Q R) ≤ C * min 1
      ((gamma3 μ ξ * dimensionLog p * Real.sqrt (dimensionLog p) +
        Real.sqrt (gamma4 μ ξ) * dimensionLog p + δ * Real.sqrt (dimensionLog p)) /
          fullCovarianceScale Q ^ 2 + Δ * dimensionLog p / fullCovarianceScale Q) := by
  let Q := A_Q * A_Q.transpose
  have hbc : fullCovarianceScale Q ^ 2 ≤ pairGap Q := by
    rw [fullCovarianceScale_sq (by omega : 0 < p) hQ.posSemidef]
    exact fullEigenvalue_le_pairGap (by omega) hQ.posSemidef hQ.unit_diagonal
  have hh := hrefined μ p n hp hn ξ G δ B A_S A_Q h hunit hQ hfactor R
  have hrate := refinedProxyCoefficientRate_le_eigenvalue
    (γ₄ := gamma4 μ ξ) (a₃ := a3 Q) (a₄ := a4 Q)
    h.boundedIndependent.delta_nonneg
    (gamma3_nonneg μ ξ) (proxyCovarianceDiscrepancy_nonneg (covariance μ (sumWithGaussian ξ G)) Q)
    (zero_le_one.trans (log_exp_mul_nat_ge_one hp)) hb hbc
  have hbnd := hh.trans (mul_le_mul_of_nonneg_left (min_le_min le_rfl hrate) hC)
  exact hbnd

end

end RectangleCLT
