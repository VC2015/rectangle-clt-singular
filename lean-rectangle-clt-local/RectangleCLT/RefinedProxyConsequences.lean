import RectangleCLT.GeneralProxyMain

/-! The completed combined proxy bound and its full-eigenvalue consequence.
The general proxy proof supplies every analytic input. -/

open MeasureTheory

universe u

namespace RectangleCLT

noncomputable section

/-- Proposition 3, with independently selected global/local moment
coefficients and the full Gaussian comparison minimum. -/
theorem refinedCovarianceProxyCLT :
    RefinedCovarianceProxyCLT.{u} generalProxyConstant :=
  refinedCovarianceProxyCLT_of_general
    (zero_le_one.trans generalProxyConstant_ge_one) generalCovarianceProxyCLT

theorem refinedCovarianceProxyCLTExists : RefinedCovarianceProxyCLTExists.{u} :=
  ⟨generalProxyConstant, generalProxyConstant_ge_one, refinedCovarianceProxyCLT⟩

/-- Corollary 4. The moment denominator is `b²`, the actual minimum
full eigenvalue; the covariance comparison term has denominator `b`. -/
theorem proxyEigenvalueRectangleCLT
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
      (rectangleError μ (sumWithGaussian ξ G) A_Q R) ≤ generalProxyConstant * min 1
      ((gamma3 μ ξ * dimensionLog p * Real.sqrt (dimensionLog p) +
        Real.sqrt (gamma4 μ ξ) * dimensionLog p + δ * Real.sqrt (dimensionLog p)) /
          fullCovarianceScale Q ^ 2 + Δ * dimensionLog p / fullCovarianceScale Q) :=
  proxyEigenvalueRectangleCLT_of_refined
    (zero_le_one.trans generalProxyConstant_ge_one) refinedCovarianceProxyCLT
    μ hp hn ξ G δ B A_S A_Q h hunit hQ hfactor hb R

end

end RectangleCLT
