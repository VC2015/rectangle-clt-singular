import RectangleCLT.LocalStatement
import RectangleCLT.ProxyCovariance

/-! The exact local covariance-proxy target, including an independent
Gaussian component and both Gaussian comparison targets. These definitions
state the target; they do not themselves assert that it has been proved. -/

open MeasureTheory ProbabilityTheory

universe u

namespace RectangleCLT

noncomputable section

def sumWithGaussian {Ω : Type u} {p n : ℕ}
    (ξ : Fin n → Ω → Vector p) (G : Ω → Vector p) (ω : Ω) : Vector p :=
  sumVector ξ ω + G ω

/-- The paper's probabilistic data. The Gaussian component is a genuine
linear-image Gaussian law, independent of the whole observation array. -/
structure ProxyHypotheses {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (G : Ω → Vector p)
    (δ : ℝ) (B : Matrix (Fin p) (Fin p) ℝ) : Prop where
  boundedIndependent : BoundedIndependentHypotheses μ ξ δ
  measurableGaussian : Measurable G
  gaussianLaw_eq : μ.map G = gaussianLaw B
  independentGaussian : IndepFun (fun ω i => ξ i ω) G μ

/-- Exactly the three local moment terms and the maximum-entry covariance
discrepancy term of Theorem 2. -/
def proxyLocalRate {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (G : Ω → Vector p)
    (δ : ℝ) (Q : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  localRateWithParameters μ ξ δ (pairGap Q) (a3 Q) (a4 Q) +
    proxyCovarianceDiscrepancy (covariance μ (sumWithGaussian ξ G)) Q *
      dimensionLog p / pairGap Q

/-- Covariance-proxy Theorem 2, with the universal constant outside every
model and dimension, and both actual and proxy Gaussian targets. -/
def LocalCovarianceProxyCLT (C : ℝ) : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p n : ℕ), 1 ≤ p → 1 ≤ n →
    ∀ (ξ : Fin n → Ω → Vector p) (G : Ω → Vector p) (δ : ℝ)
      (B A_S A_Σ : Matrix (Fin p) (Fin p) ℝ),
      ProxyHypotheses μ ξ G δ B →
      (∀ j, covariance μ (sumWithGaussian ξ G) j j = 1) →
      LocalCovarianceHypotheses (A_Σ * A_Σ.transpose) →
      A_S * A_S.transpose = covariance μ (sumWithGaussian ξ G) →
      ∀ R : Rect p,
        max (rectangleError μ (sumWithGaussian ξ G) A_S R)
          (rectangleError μ (sumWithGaussian ξ G) A_Σ R) ≤
        C * min 1 (proxyLocalRate μ ξ G δ (A_Σ * A_Σ.transpose))

def LocalCovarianceProxyCLTExists : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ LocalCovarianceProxyCLT.{u} C

end

end RectangleCLT
