import RectangleCLT.GaussianComponentClosureCoupling
import RectangleCLT.GaussianComponentClosureLimits
import RectangleCLT.ProxyBounded

/-!
# Covariance-proxy CLT with a genuine independent Gaussian component

The finite approximating array contains the original observations, tiny
truncated Gaussian increments, and bounded symmetric covariance-restoring
columns. Its covariance is exactly the original covariance at every
stage, so the proxy is fixed throughout. The signed third tensor is
unchanged. The extra envelope, fourth moments, and coupling cost vanish.

This module assembles proved finite-array identities and the bounded
proxy theorem. No analytic cap or Gaussian-approximation estimate is an
assumption of the public theorem.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

universe u

namespace RectangleCLT

noncomputable section

theorem boundedProxyBothTargetsConstant_ge_one :
    1 ≤ boundedProxyBothTargetsConstant := by
  unfold boundedProxyBothTargetsConstant
  linarith [boundedProxyConstant_ge_two, gaussianComparisonLocalConstant_ge_two]

/-- The exact Theorem 2 statement, including both Gaussian targets and an
arbitrary independent, possibly singular Gaussian component. -/
theorem localCovarianceProxyCLT :
    LocalCovarianceProxyCLT.{u} boundedProxyBothTargetsConstant := by
  intro Ω _ μ _ p n hp hn ξ G δ B A_S A_Q h hunit hproxy hfactor R
  let Q := A_Q * A_Q.transpose
  let L := dimensionLog p
  let c := pairGap Q
  let a₃ := a3 Q
  let a₄ := a4 Q
  let M := gaussianComponentFourthMoment B
  let Δ := proxyCovarianceDiscrepancy (covariance μ (sumWithGaussian ξ G)) Q
  let T := gamma3 μ ξ * L * Real.sqrt L / (c * a₃) + Δ * L / c
  let U := L / (Real.rpow c (5 / 6 : ℝ) * Real.rpow (a₃ * a₄) (1 / 3 : ℝ))
  let V := Real.sqrt L / c
  let C := boundedProxyBothTargetsConstant
  have hC : 0 ≤ C := zero_le_one.trans boundedProxyBothTargetsConstant_ge_one
  have hc : 0 < c := hproxy.pairGap_pos hp
  have ha₃ : 0 < a₃ := hproxy.a3_pos hp
  have ha₄ : 0 < a₄ := hproxy.a4_pos
  have hL : 0 ≤ L := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hU : 0 ≤ U := div_nonneg hL
    (mul_nonneg (Real.rpow_nonneg hc.le _)
      (Real.rpow_nonneg (mul_nonneg ha₃.le ha₄.le) _))
  have hSdiag : ∀ j, (A_S * A_S.transpose) j j = 1 := by
    intro j
    rw [hfactor]
    exact hunit j
  have hfinite : ∀ k : ℕ, 1 ≤ k →
      max (rectangleError μ (sumWithGaussian ξ G) A_S R)
        (rectangleError μ (sumWithGaussian ξ G) A_Q R) ≤
      C * min 1 (T + U * Real.sqrt
        (gaussianComponentFourthUpper (gamma4 μ ξ) M k) +
          V * gaussianComponentEnvelopeUpper δ M k) +
        gaussianComponentCouplingUpper p M k := by
    intro k hk
    have hk₀ : k ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hk)
    let ν := gaussianComponentRestoredMarginal μ ξ B k
    let μk := Measure.pi ν
    let η := gaussianComponentRestoredArray (p := p) (n := n) k
    let δk := gaussianComponentEnvelopeUpper δ M k
    let r := T + U * Real.sqrt (gaussianComponentFourthUpper (gamma4 μ ξ) M k) + V * δk
    letI (i : Fin n ⊕ (Fin (k ^ 6) ⊕ Fin p)) : IsProbabilityMeasure (ν i) :=
      gaussianComponentRestoredMarginal_isProbability μ ξ h.boundedIndependent.measurable B k i
    have hη : BoundedIndependentHypotheses μk η δk :=
      gaussianComponentRestoredArray_boundedIndependent μ ξ h.boundedIndependent hp B hk₀
    have hcov : covariance μk (sumVector η) = covariance μ (sumWithGaussian ξ G) := by
      rw [gaussianComponentRestoredArray_covariance μ ξ h.boundedIndependent hp B hk₀,
        h.covariance_sumWithGaussian]
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
    have hsqrt : Real.sqrt (gamma4 μk η) ≤
        Real.sqrt (gaussianComponentFourthUpper (gamma4 μ ξ) M k) :=
      Real.sqrt_le_sqrt hγ₄
    have hrate : boundedProxyLocalRate μk η δk Q ≤ r := by
      calc
        boundedProxyLocalRate μk η δk Q =
            T + U * Real.sqrt (gamma4 μk η) + V * δk := by
          unfold boundedProxyLocalRate localRateWithParameters
          rw [hγ₃, hcov]
          dsimp [T, U, V, Δ, Q, L, c, a₃, a₄]
          ring
        _ ≤ r := by
          dsimp [r]
          exact add_le_add_right (add_le_add_left
            (mul_le_mul_of_nonneg_left hsqrt hU) T) _
    have hboxes (lo hi : Vector p) :
        max (rectangleError μk (sumVector η) A_S (Rect.closedBox lo hi))
          (rectangleError μk (sumVector η) A_Q (Rect.closedBox lo hi)) ≤
            C * min 1 r := by
      have hb := boundedProxyBothTargets μk η δk hη hp hunitk A_S A_Q hproxy
        hfactork (Rect.closedBox lo hi)
      exact hb.trans (mul_le_mul_of_nonneg_left (min_le_min_left 1 hrate) hC)
    have hleft := gaussianComponentRaw_rectangle_transfer μ ξ G hp B h hk₀
      A_S hSdiag (fun lo hi => (le_max_left _ _).trans (hboxes lo hi)) R
    have hright := gaussianComponentRaw_rectangle_transfer μ ξ G hp B h hk₀
      A_Q hproxy.unit_diagonal (fun lo hi => (le_max_right _ _).trans (hboxes lo hi)) R
    have hb := max_le hleft hright
    simpa only [r, δk, gaussianComponentCouplingUpper, gaussianComponentRestorationError,
      M, add_assoc] using hb
  have hlimit := gaussianComponent_bound_passage p h.boundedIndependent.delta_nonneg hfinite
  have hexact : T + U * Real.sqrt (gamma4 μ ξ) + V * δ =
      proxyLocalRate μ ξ G δ Q := by
    unfold proxyLocalRate localRateWithParameters
    dsimp [T, U, V, Δ, Q, L, c, a₃, a₄]
    ring
  rw [hexact] at hlimit
  exact hlimit

/-- One fixed universal constant works for every model and dimension in
the full covariance-proxy theorem. -/
theorem localCovarianceProxyCLTExists : LocalCovarianceProxyCLTExists.{u} :=
  ⟨boundedProxyBothTargetsConstant, boundedProxyBothTargetsConstant_ge_one,
    localCovarianceProxyCLT⟩

end

end RectangleCLT
