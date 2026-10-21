import RectangleCLT.RefinedProxyStatement
import RectangleCLT.GaussianComponentClosureCoupling

/-! Covariance-preserving closure of the general proxy bound. The finite
arrays keep the total covariance and proxy discrepancy fixed, preserve
the signed third tensor, and have vanishing additional fourth moments. -/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

universe u

namespace RectangleCLT

noncomputable section

/-- The bounded version of Proposition 4 with both Gaussian targets.
No nondegeneracy condition is imposed on the true covariance. -/
def GeneralBoundedCovarianceProxyCLT (C : ℝ) : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p n : ℕ), 1 ≤ p → 1 ≤ n →
    ∀ (ξ : Fin n → Ω → Vector p) (δ : ℝ)
      (A_S A_Q : Matrix (Fin p) (Fin p) ℝ),
      BoundedIndependentHypotheses μ ξ δ →
      (∀ j, covariance μ (sumVector ξ) j j = 1) →
      (∀ j, (A_Q * A_Q.transpose) j j = 1) →
      0 < pairGap (A_Q * A_Q.transpose) →
      A_S * A_S.transpose = covariance μ (sumVector ξ) →
      ∀ R : Rect p,
        max (rectangleError μ (sumVector ξ) A_S R)
          (rectangleError μ (sumVector ξ) A_Q R) ≤ C * min 1
          (generalProxyCoefficientRate δ (gamma3 μ ξ) (gamma4 μ ξ)
            (proxyCovarianceDiscrepancy (covariance μ (sumVector ξ)) (A_Q * A_Q.transpose))
            (dimensionLog p) (fullCovarianceScale (A_Q * A_Q.transpose))
            (pairGap (A_Q * A_Q.transpose)) (a3 (A_Q * A_Q.transpose))
            (a4 (A_Q * A_Q.transpose)))

theorem generalProxyGaussianComponent_bound_passage
    {error C δ γ₃ γ₄ Δ L b c a₃ a₄ M : ℝ} (p : ℕ) (hδ : 0 ≤ δ)
    (hbound : ∀ k : ℕ, 1 ≤ k →
      error ≤ C * min 1
        (generalProxyCoefficientRate (gaussianComponentEnvelopeUpper δ M k) γ₃
          (gaussianComponentFourthUpper γ₄ M k) Δ L b c a₃ a₄) +
        gaussianComponentCouplingUpper p M k) :
    error ≤ C * min 1 (generalProxyCoefficientRate δ γ₃ γ₄ Δ L b c a₃ a₄) := by
  have hr := (generalCoefficientRate_tendsto
    (gaussianComponentEnvelopeUpper_tendsto δ M hδ)
    (gaussianComponentFourthUpper_tendsto γ₄ M) γ₃ L b c a₃ a₄).add_const
      (Δ * L * gaussianComparisonCoefficient b c)
  have hlim := (((tendsto_const_nhds (x := (1 : ℝ))).min hr).const_mul C).add
    (gaussianComponentCouplingUpper_tendsto p M)
  have he : ∀ᶠ k : ℕ in atTop,
      error ≤ C * min 1
        (generalProxyCoefficientRate (gaussianComponentEnvelopeUpper δ M k) γ₃
          (gaussianComponentFourthUpper γ₄ M k) Δ L b c a₃ a₄) +
        gaussianComponentCouplingUpper p M k := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    exact hbound k hk
  simpa only [generalProxyCoefficientRate, add_zero] using ge_of_tendsto hlim he

/-- Proposition 4 for an arbitrary genuine independent Gaussian component,
conditional only on the actual bounded both-target theorem. This closure
does not assume any analytic cap or approximation input for the data. -/
theorem generalCovarianceProxyCLT_of_bounded {C : ℝ} (hC : 0 ≤ C)
    (hbounded : GeneralBoundedCovarianceProxyCLT.{0} C) :
    GeneralCovarianceProxyCLT.{u} C := by
  intro Ω _ μ _ p n hp hn ξ G δ B A_S A_Q h hunit hdiag hc hfactor R
  let Q := A_Q * A_Q.transpose
  let L := dimensionLog p
  let b := fullCovarianceScale Q
  let c := pairGap Q
  let a₃ := a3 Q
  let a₄ := a4 Q
  let M := gaussianComponentFourthMoment B
  let Δ := proxyCovarianceDiscrepancy (covariance μ (sumWithGaussian ξ G)) Q
  have hL : 0 ≤ L := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hSdiag : ∀ j, (A_S * A_S.transpose) j j = 1 := by
    intro j
    rw [hfactor]
    exact hunit j
  have hfinite : ∀ k : ℕ, 1 ≤ k →
      max (rectangleError μ (sumWithGaussian ξ G) A_S R)
        (rectangleError μ (sumWithGaussian ξ G) A_Q R) ≤
      C * min 1
        (generalProxyCoefficientRate (gaussianComponentEnvelopeUpper δ M k) (gamma3 μ ξ)
          (gaussianComponentFourthUpper (gamma4 μ ξ) M k) Δ L b c a₃ a₄) +
        gaussianComponentCouplingUpper p M k := by
    intro k hk
    have hk₀ : k ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hk)
    let ν := gaussianComponentRestoredMarginal μ ξ B k
    let μk := Measure.pi ν
    let η := gaussianComponentRestoredArray (p := p) (n := n) k
    let δk := gaussianComponentEnvelopeUpper δ M k
    let r := generalProxyCoefficientRate δk (gamma3 μ ξ)
      (gaussianComponentFourthUpper (gamma4 μ ξ) M k) Δ L b c a₃ a₄
    letI (i : Fin n ⊕ (Fin (k ^ 6) ⊕ Fin p)) : IsProbabilityMeasure (ν i) :=
      gaussianComponentRestoredMarginal_isProbability μ ξ h.boundedIndependent.measurable B k i
    have hη : BoundedIndependentHypotheses μk η δk :=
      gaussianComponentRestoredArray_boundedIndependent μ ξ h.boundedIndependent hp B hk₀
    have hcov : covariance μk (sumVector η) = covariance μ (sumWithGaussian ξ G) := by
      exact (gaussianComponentRestoredArray_covariance μ ξ h.boundedIndependent hp B hk₀).trans
        h.covariance_sumWithGaussian.symm
    have hunitk : ∀ j, covariance μk (sumVector η) j j = 1 := by
      intro j
      rw [hcov]
      exact hunit j
    have hfactork : A_S * A_S.transpose = covariance μk (sumVector η) :=
      hfactor.trans hcov.symm
    have hγ₃ : gamma3 μk η = gamma3 μ ξ :=
      gaussianComponentRestoredArray_gamma3 μ ξ h.boundedIndependent.measurable B k
    have hγ₄ : gamma4 μk η ≤ gaussianComponentFourthUpper (gamma4 μ ξ) M k :=
      gaussianComponentRestoredArray_gamma4_le μ ξ h.boundedIndependent.measurable hp B hk₀
    have hrate : generalProxyCoefficientRate δk (gamma3 μk η) (gamma4 μk η)
        (proxyCovarianceDiscrepancy (covariance μk (sumVector η)) Q)
        L b c a₃ a₄ ≤ r := by
      unfold generalProxyCoefficientRate
      rw [hcov, hγ₃]
      exact add_le_add_right (generalCoefficientRate_mono le_rfl
        (gamma4_nonneg μk η) hγ₄ hL hc) _
    have hboxes (lo hi : Vector p) :
        max (rectangleError μk (sumVector η) A_S (Rect.closedBox lo hi))
          (rectangleError μk (sumVector η) A_Q (Rect.closedBox lo hi)) ≤ C * min 1 r := by
      have hb := hbounded μk p (n + (k ^ 6 + p)) hp (by omega)
        η δk A_S A_Q hη hunitk hdiag hc hfactork (Rect.closedBox lo hi)
      exact hb.trans (mul_le_mul_of_nonneg_left (min_le_min_left 1 hrate) hC)
    have hleft := gaussianComponentRaw_rectangle_transfer μ ξ G hp B h hk₀
      A_S hSdiag (fun lo hi => (le_max_left _ _).trans (hboxes lo hi)) R
    have hright := gaussianComponentRaw_rectangle_transfer μ ξ G hp B h hk₀
      A_Q hdiag (fun lo hi => (le_max_right _ _).trans (hboxes lo hi)) R
    have hb := max_le hleft hright
    simpa only [r, δk, gaussianComponentCouplingUpper, gaussianComponentRestorationError,
      M, add_assoc] using hb
  exact generalProxyGaussianComponent_bound_passage p h.boundedIndependent.delta_nonneg hfinite

end

end RectangleCLT
