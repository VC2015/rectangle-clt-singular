import RectangleCLT.GeneralRateBounds
import RectangleCLT.GaussianComponentClosureCoupling

/-!
# The general moment bound with an independent Gaussian component

The covariance-restored finite arrays have exactly the covariance of the
original Gaussian-convolved sum. Their signed third tensor is unchanged;
their extra fourth moments, envelope, and coupling cost vanish. Thus every
alternative in the general rate passes to the limit with fixed covariance
parameters, including zero full, three-, or four-coordinate eigenvalues.

This module proves the closure implication from the bounded general CLT.
The public unconditional instance is assembled in the main module.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

universe u

namespace RectangleCLT

noncomputable section

/-- Lemma 11 for the full general rate. The moments concern only the
bounded observations; all covariance parameters concern the total sum. -/
def GeneralGaussianRectangleCLT (C : ℝ) : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p n : ℕ), 1 ≤ p → 1 ≤ n →
    ∀ (ξ : Fin n → Ω → Vector p) (G : Ω → Vector p) (δ : ℝ)
      (B A : Matrix (Fin p) (Fin p) ℝ),
      ProxyHypotheses μ ξ G δ B →
      (∀ j, covariance μ (sumWithGaussian ξ G) j j = 1) →
      0 < pairGap (covariance μ (sumWithGaussian ξ G)) →
      A * A.transpose = covariance μ (sumWithGaussian ξ G) →
      ∀ R : Rect p,
        rectangleError μ (sumWithGaussian ξ G) A R ≤
          C * min 1 (generalBoundedRate μ ξ δ (covariance μ (sumWithGaussian ξ G)))

def GeneralGaussianRectangleCLTExists : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ GeneralGaussianRectangleCLT.{u} C

/-- Covariance-preserving closure of the actual bounded general theorem.
Only its universe-zero instance is needed: all finite approximating
arrays live on finite products of Euclidean spaces. -/
theorem generalGaussianRectangleCLT_of_bounded {C : ℝ} (hC : 0 ≤ C)
    (hgeneral : GeneralRectangleCLT.{0} C) : GeneralGaussianRectangleCLT.{u} C := by
  intro Ω _ μ _ p n hp hn ξ G δ B A h hunit hgap hfactor R
  let Q := covariance μ (sumWithGaussian ξ G)
  let L := dimensionLog p
  let b := fullCovarianceScale Q
  let c := pairGap Q
  let a₃ := a3 Q
  let a₄ := a4 Q
  let M := gaussianComponentFourthMoment B
  have hL : 0 ≤ L := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hc : 0 < c := hgap
  have hAdiag : ∀ j, (A * A.transpose) j j = 1 := by
    intro j
    rw [hfactor]
    exact hunit j
  have hfinite : ∀ k : ℕ, 1 ≤ k →
      rectangleError μ (sumWithGaussian ξ G) A R ≤
        C * min 1
          (generalCoefficientRate (gaussianComponentEnvelopeUpper δ M k) (gamma3 μ ξ)
            (gaussianComponentFourthUpper (gamma4 μ ξ) M k) L b c a₃ a₄) +
          gaussianComponentCouplingUpper p M k := by
    intro k hk
    have hk₀ : k ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hk)
    let ν := gaussianComponentRestoredMarginal μ ξ B k
    let μk := Measure.pi ν
    let η := gaussianComponentRestoredArray (p := p) (n := n) k
    let δk := gaussianComponentEnvelopeUpper δ M k
    let r := generalCoefficientRate δk (gamma3 μ ξ)
      (gaussianComponentFourthUpper (gamma4 μ ξ) M k) L b c a₃ a₄
    letI (i : Fin n ⊕ (Fin (k ^ 6) ⊕ Fin p)) : IsProbabilityMeasure (ν i) :=
      gaussianComponentRestoredMarginal_isProbability μ ξ h.boundedIndependent.measurable B k i
    have hη : BoundedIndependentHypotheses μk η δk :=
      gaussianComponentRestoredArray_boundedIndependent μ ξ h.boundedIndependent hp B hk₀
    have hcov : covariance μk (sumVector η) = Q := by
      exact (gaussianComponentRestoredArray_covariance μ ξ h.boundedIndependent hp B hk₀).trans
        h.covariance_sumWithGaussian.symm
    have hunitk : ∀ j, covariance μk (sumVector η) j j = 1 := by
      intro j
      rw [hcov]
      exact hunit j
    have hgapk : 0 < pairGap (covariance μk (sumVector η)) := by
      rw [hcov]
      exact hgap
    have hfactork : A * A.transpose = covariance μk (sumVector η) :=
      hfactor.trans hcov.symm
    have hγ₃ : gamma3 μk η = gamma3 μ ξ :=
      gaussianComponentRestoredArray_gamma3 μ ξ h.boundedIndependent.measurable B k
    have hγ₄ : gamma4 μk η ≤ gaussianComponentFourthUpper (gamma4 μ ξ) M k :=
      gaussianComponentRestoredArray_gamma4_le μ ξ h.boundedIndependent.measurable hp B hk₀
    have hrate : generalBoundedRate μk η δk (covariance μk (sumVector η)) ≤ r := by
      unfold generalBoundedRate
      rw [hcov, hγ₃]
      exact generalCoefficientRate_mono le_rfl (gamma4_nonneg μk η) hγ₄ hL hc
    have hboxes (lo hi : Vector p) :
        rectangleError μk (sumVector η) A (Rect.closedBox lo hi) ≤ C * min 1 r := by
      have hb := hgeneral μk p (n + (k ^ 6 + p)) hp (by omega)
        η δk A hη hunitk hgapk hfactork (Rect.closedBox lo hi)
      exact hb.trans (mul_le_mul_of_nonneg_left (min_le_min_left 1 hrate) hC)
    have hleft := gaussianComponentRaw_rectangle_transfer μ ξ G hp B h hk₀
      A hAdiag hboxes R
    simpa only [r, δk, gaussianComponentCouplingUpper, gaussianComponentRestorationError,
      M, add_assoc] using hleft
  have hlimit := generalGaussianComponent_bound_passage p h.boundedIndependent.delta_nonneg
    hfinite
  exact hlimit

end

end RectangleCLT
