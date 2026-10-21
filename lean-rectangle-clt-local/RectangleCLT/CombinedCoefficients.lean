import RectangleCLT.LocalOptimization
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp

/-!
# The manuscript's combined local/global coefficients

This file proves the coefficient comparisons in Proposition 6.3 and the
scalar implication behind its eigenvalue corollary. A denominator containing
the full scale is omitted when that scale is zero. In particular the local
branch remains finite for a singular full covariance.

These are algebraic results. The analytic full-eigenvalue alternatives
and the actual combined CLT are assembled in `CombinedMain.lean`.
-/

namespace RectangleCLT

noncomputable section

def combinedThirdCoefficient (b c a₃ : ℝ) : ℝ :=
  if 0 < b then min (1 / b ^ 2) (1 / (c * a₃)) else 1 / (c * a₃)

def combinedFourthCoefficient (b c a₃ a₄ : ℝ) : ℝ :=
  if 0 < b then min (1 / b) (1 / localFourthScale c a₃ a₄)
  else 1 / localFourthScale c a₃ a₄

/-- The exact three terms in the combined bound. -/
def combinedCoefficientRate (δ γ₃ γ₄ L b c a₃ a₄ : ℝ) : ℝ :=
  γ₃ * L * Real.sqrt L * combinedThirdCoefficient b c a₃ +
    Real.sqrt γ₄ * L / Real.sqrt c * combinedFourthCoefficient b c a₃ a₄ +
    δ * Real.sqrt L / c

theorem combinedThirdCoefficient_nonneg {b c a₃ : ℝ}
    (hc : 0 < c) (ha₃ : 0 < a₃) : 0 ≤ combinedThirdCoefficient b c a₃ := by
  unfold combinedThirdCoefficient
  split_ifs <;> positivity

theorem combinedFourthCoefficient_nonneg {b c a₃ a₄ : ℝ}
    (hc : 0 < c) (ha₃ : 0 < a₃) (ha₄ : 0 < a₄) :
    0 ≤ combinedFourthCoefficient b c a₃ a₄ := by
  have hd := localFourthScale_pos hc ha₃ ha₄
  unfold combinedFourthCoefficient
  split_ifs <;> positivity

theorem combinedCoefficientRate_nonneg {δ γ₃ γ₄ L b c a₃ a₄ : ℝ}
    (hδ : 0 ≤ δ) (hγ₃ : 0 ≤ γ₃) (hL : 0 ≤ L)
    (hc : 0 < c) (ha₃ : 0 < a₃) (ha₄ : 0 < a₄) :
    0 ≤ combinedCoefficientRate δ γ₃ γ₄ L b c a₃ a₄ := by
  have hβ₃ := combinedThirdCoefficient_nonneg (b := b) hc ha₃
  have hβ₄ := combinedFourthCoefficient_nonneg (b := b) hc ha₃ ha₄
  unfold combinedCoefficientRate
  positivity

theorem combinedThirdCoefficient_le_local (b c a₃ : ℝ) :
    combinedThirdCoefficient b c a₃ ≤ 1 / (c * a₃) := by
  unfold combinedThirdCoefficient
  split_ifs
  · exact min_le_right _ _
  · exact le_rfl

theorem combinedFourthCoefficient_le_local (b c a₃ a₄ : ℝ) :
    combinedFourthCoefficient b c a₃ a₄ ≤ 1 / localFourthScale c a₃ a₄ := by
  unfold combinedFourthCoefficient
  split_ifs
  · exact min_le_right _ _
  · exact le_rfl

theorem combinedThirdCoefficient_le_global {b : ℝ} (hb : 0 < b) (c a₃ : ℝ) :
    combinedThirdCoefficient b c a₃ ≤ 1 / b ^ 2 := by
  simp only [combinedThirdCoefficient, if_pos hb]
  exact min_le_left _ _

theorem combinedFourthCoefficient_le_global {b : ℝ} (hb : 0 < b) (c a₃ a₄ : ℝ) :
    combinedFourthCoefficient b c a₃ a₄ ≤ 1 / b := by
  simp only [combinedFourthCoefficient, if_pos hb]
  exact min_le_left _ _

@[simp] theorem combinedThirdCoefficient_zero (c a₃ : ℝ) :
    combinedThirdCoefficient 0 c a₃ = 1 / (c * a₃) := by
  simp [combinedThirdCoefficient]

@[simp] theorem combinedFourthCoefficient_zero (c a₃ a₄ : ℝ) :
    combinedFourthCoefficient 0 c a₃ a₄ = 1 / localFourthScale c a₃ a₄ := by
  simp [combinedFourthCoefficient]

/-- The fourth-moment global coefficient is `1/(b*sqrt c)`, before using
the spectral hierarchy `b² ≤ c` to bound it by `b⁻²`. -/
theorem globalFourthCoefficient_le_inv_sq {b c : ℝ}
    (hb : 0 < b) (hbc : b ^ 2 ≤ c) :
    1 / (b * Real.sqrt c) ≤ 1 / b ^ 2 := by
  have hs : b ≤ Real.sqrt c := Real.le_sqrt_of_sq_le hbc
  apply one_div_le_one_div_of_le (sq_pos_of_pos hb)
  simpa only [pow_two] using mul_le_mul_of_nonneg_left hs hb.le

theorem combinedFourthCoefficient_div_sqrt_le_inv_sq {b c : ℝ}
    (hb : 0 < b) (hbc : b ^ 2 ≤ c) (a₃ a₄ : ℝ) :
    combinedFourthCoefficient b c a₃ a₄ / Real.sqrt c ≤ 1 / b ^ 2 := by
  have hc : 0 < c := (sq_pos_of_pos hb).trans_le hbc
  calc
    _ ≤ (1 / b) / Real.sqrt c := div_le_div_of_nonneg_right
      (combinedFourthCoefficient_le_global hb c a₃ a₄) (Real.sqrt_nonneg c)
    _ = 1 / (b * Real.sqrt c) := by rw [div_div]
    _ ≤ 1 / b ^ 2 := globalFourthCoefficient_le_inv_sq hb hbc

/-- At a singular full covariance, the combined scalar rate reduces exactly
to the already certified local expression. -/
theorem combinedCoefficientRate_zero_eq_local {δ γ₃ γ₄ L c a₃ a₄ : ℝ}
    (hc : 0 < c) (ha₃ : 0 < a₃) (ha₄ : 0 < a₄) :
    combinedCoefficientRate δ γ₃ γ₄ L 0 c a₃ a₄ =
      γ₃ * L * Real.sqrt L / (c * a₃) +
        Real.sqrt γ₄ * L /
          (Real.rpow c (5 / 6 : ℝ) * Real.rpow (a₃ * a₄) (1 / 3 : ℝ)) +
        δ * Real.sqrt L / c := by
  rw [combinedCoefficientRate, combinedThirdCoefficient_zero,
    combinedFourthCoefficient_zero, ← sqrt_mul_localFourthScale hc ha₃ ha₄]
  simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
  ring

/-- Coefficient comparison for the eigenvalue-form corollary. This proves
exactly the three scalar comparisons used in the paper; no rectangle-error
estimate is assumed or concluded. -/
theorem combinedCoefficientRate_le_eigenvalueRate {δ γ₃ γ₄ L b c a₃ a₄ : ℝ}
    (hδ : 0 ≤ δ) (hγ₃ : 0 ≤ γ₃) (hL : 0 ≤ L)
    (hb : 0 < b) (hbc : b ^ 2 ≤ c) :
    combinedCoefficientRate δ γ₃ γ₄ L b c a₃ a₄ ≤
      (γ₃ * L * Real.sqrt L + Real.sqrt γ₄ * L + δ * Real.sqrt L) / b ^ 2 := by
  have hb₂ : 0 < b ^ 2 := sq_pos_of_pos hb
  have hc : 0 < c := hb₂.trans_le hbc
  have hthird : γ₃ * L * Real.sqrt L * combinedThirdCoefficient b c a₃ ≤
      (γ₃ * L * Real.sqrt L) / b ^ 2 := by
    simpa only [div_eq_mul_inv, one_mul] using
      mul_le_mul_of_nonneg_left (combinedThirdCoefficient_le_global hb c a₃)
        (show 0 ≤ γ₃ * L * Real.sqrt L by positivity)
  have hfourth : Real.sqrt γ₄ * L / Real.sqrt c *
      combinedFourthCoefficient b c a₃ a₄ ≤ (Real.sqrt γ₄ * L) / b ^ 2 := by
    calc
      _ = (Real.sqrt γ₄ * L) *
          (combinedFourthCoefficient b c a₃ a₄ / Real.sqrt c) := by ring
      _ ≤ (Real.sqrt γ₄ * L) * (1 / b ^ 2) :=
        mul_le_mul_of_nonneg_left
          (combinedFourthCoefficient_div_sqrt_le_inv_sq hb hbc a₃ a₄)
          (by positivity)
      _ = _ := by ring
  have henvelope : δ * Real.sqrt L / c ≤ (δ * Real.sqrt L) / b ^ 2 := by
    have hi := one_div_le_one_div_of_le hb₂ hbc
    simpa only [div_eq_mul_inv, one_mul] using
      mul_le_mul_of_nonneg_left hi (show 0 ≤ δ * Real.sqrt L by positivity)
  unfold combinedCoefficientRate
  calc
    _ ≤ (γ₃ * L * Real.sqrt L) / b ^ 2 + (Real.sqrt γ₄ * L) / b ^ 2 +
        (δ * Real.sqrt L) / b ^ 2 := add_le_add (add_le_add hthird hfourth) henvelope
    _ = _ := by ring

/-- Bounded moments recover the Aronow--Lopatto scalar rate from the combined
coefficient expression, with an explicit factor three. -/
theorem combinedCoefficientRate_le_aronowLopattoRate {δ γ₃ γ₄ L b c a₃ a₄ : ℝ}
    (hδ : 0 ≤ δ) (hγ₃₀ : 0 ≤ γ₃) (hγ₃ : γ₃ ≤ δ) (hγ₄ : γ₄ ≤ δ ^ 2)
    (hL : 1 ≤ L) (hb : 0 < b) (hbc : b ^ 2 ≤ c) :
    combinedCoefficientRate δ γ₃ γ₄ L b c a₃ a₄ ≤
      3 * (δ * L * Real.sqrt L / b ^ 2) := by
  calc
    _ ≤ (γ₃ * L * Real.sqrt L + Real.sqrt γ₄ * L + δ * Real.sqrt L) / b ^ 2 :=
      combinedCoefficientRate_le_eigenvalueRate hδ hγ₃₀ (by linarith) hb hbc
    _ ≤ (3 * δ * L * Real.sqrt L) / b ^ 2 :=
      div_le_div_of_nonneg_right
        (rate_numerator_le_three_delta_log_sqrt hδ hγ₃ hγ₄ hL) (sq_nonneg b)
    _ = _ := by ring

/-- Aggregate third-moment cancellation saves the factor `sqrt L` in the
scalar eigenvalue recovery. -/
theorem combinedCoefficientRate_le_cancellationRate {δ γ₃ γ₄ L b c a₃ a₄ : ℝ}
    (hδ : 0 ≤ δ) (hγ₃ : γ₃ = 0) (hγ₄ : γ₄ ≤ δ ^ 2)
    (hL : 1 ≤ L) (hb : 0 < b) (hbc : b ^ 2 ≤ c) :
    combinedCoefficientRate δ γ₃ γ₄ L b c a₃ a₄ ≤
      2 * (δ * L / b ^ 2) := by
  calc
    _ ≤ (γ₃ * L * Real.sqrt L + Real.sqrt γ₄ * L + δ * Real.sqrt L) / b ^ 2 :=
      combinedCoefficientRate_le_eigenvalueRate hδ (by simp [hγ₃]) (by linarith) hb hbc
    _ ≤ (2 * δ * L) / b ^ 2 := div_le_div_of_nonneg_right
      (rate_numerator_le_two_delta_log_of_third_eq_zero hδ hγ₃ hγ₄ hL) (sq_nonneg b)
    _ = _ := by ring

end

end RectangleCLT
