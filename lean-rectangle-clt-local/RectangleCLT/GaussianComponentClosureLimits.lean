import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Real.Sqrt

/-! Scalar limits for the exact Gaussian-component approximation.
These lemmas only pass already established numerical bounds to a limit.
They do not assume or assert an analytic Gaussian-approximation theorem. -/

open Filter
open scoped Topology

namespace RectangleCLT

noncomputable section

def gaussianComponentEnvelopeUpper (δ M : ℝ) (k : ℕ) : ℝ :=
  max δ (max (k : ℝ)⁻¹ (Real.sqrt (M / (k : ℝ) ^ 4)))

def gaussianComponentFourthUpper (γ M : ℝ) (k : ℕ) : ℝ :=
  γ + M / (k : ℝ) ^ 6 + (M / (k : ℝ) ^ 4) ^ 2

def gaussianComponentCouplingUpper (p : ℕ) (M : ℝ) (k : ℕ) : ℝ :=
  M / (k : ℝ) ^ 2 + 4 * p * (p * Real.sqrt (M / (k : ℝ) ^ 4))

theorem gaussianComponent_const_div_pow_tendsto_zero (M : ℝ)
    {m : ℕ} (hm : 0 < m) :
    Tendsto (fun k : ℕ => M / (k : ℝ) ^ m) atTop (𝓝 0) := by
  have h := (tendsto_const_nhds (x := M)).mul
    (tendsto_inverse_atTop_nhds_zero_nat.pow m)
  simpa only [div_eq_mul_inv, inv_pow, zero_pow (Nat.ne_of_gt hm), mul_zero] using h

theorem gaussianComponentEnvelopeUpper_tendsto (δ M : ℝ) (hδ : 0 ≤ δ) :
    Tendsto (gaussianComponentEnvelopeUpper δ M) atTop (𝓝 δ) := by
  have hM := (gaussianComponent_const_div_pow_tendsto_zero M (by decide : 0 < 4)).sqrt
  have h := (tendsto_const_nhds (x := δ)).max
    (tendsto_inverse_atTop_nhds_zero_nat.max hM)
  simpa only [gaussianComponentEnvelopeUpper, Real.sqrt_zero, max_self,
    max_eq_left hδ] using h

theorem gaussianComponentFourthUpper_tendsto (γ M : ℝ) :
    Tendsto (gaussianComponentFourthUpper γ M) atTop (𝓝 γ) := by
  have h₆ := gaussianComponent_const_div_pow_tendsto_zero M (by decide : 0 < 6)
  have h₄ := gaussianComponent_const_div_pow_tendsto_zero M (by decide : 0 < 4)
  have h := ((tendsto_const_nhds (x := γ)).add h₆).add (h₄.pow 2)
  simpa only [gaussianComponentFourthUpper, zero_pow (by decide : 2 ≠ 0), add_zero] using h

theorem gaussianComponentCouplingUpper_tendsto (p : ℕ) (M : ℝ) :
    Tendsto (gaussianComponentCouplingUpper p M) atTop (𝓝 0) := by
  have h₂ := gaussianComponent_const_div_pow_tendsto_zero M (by decide : 0 < 2)
  have h₄ := (gaussianComponent_const_div_pow_tendsto_zero M (by decide : 0 < 4)).sqrt
  have h := h₂.add ((h₄.const_mul (p : ℝ)).const_mul (4 * (p : ℝ)))
  simpa only [gaussianComponentCouplingUpper, Real.sqrt_zero, mul_zero, add_zero] using h

/-- A saturated error bound survives the exact finite Gaussian splitting,
truncation, and covariance-restoration limit. -/
theorem gaussianComponent_bound_passage
    {error C T U V γ δ M : ℝ} (p : ℕ) (hδ : 0 ≤ δ)
    (hbound : ∀ k : ℕ, 1 ≤ k →
      error ≤ C * min 1 (T + U * Real.sqrt (gaussianComponentFourthUpper γ M k) +
        V * gaussianComponentEnvelopeUpper δ M k) +
          gaussianComponentCouplingUpper p M k) :
    error ≤ C * min 1 (T + U * Real.sqrt γ + V * δ) := by
  have hF := (gaussianComponentFourthUpper_tendsto γ M).sqrt
  have hδlim := gaussianComponentEnvelopeUpper_tendsto δ M hδ
  have hrate := ((tendsto_const_nhds (x := T)).add (hF.const_mul U)).add
    (hδlim.const_mul V)
  have hsaturated := ((tendsto_const_nhds (x := 1)).min hrate).const_mul C
  have hlimit := hsaturated.add (gaussianComponentCouplingUpper_tendsto p M)
  have heventual : ∀ᶠ k : ℕ in atTop,
      error ≤ C * min 1 (T + U * Real.sqrt (gaussianComponentFourthUpper γ M k) +
        V * gaussianComponentEnvelopeUpper δ M k) +
          gaussianComponentCouplingUpper p M k := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    exact hbound k hk
  simpa only [add_zero] using ge_of_tendsto hlimit heventual

end

end RectangleCLT
