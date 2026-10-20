import RectangleCLT.CombinedCoefficients

/-!
# Scalar optimization of the combined master expression

The analytic master estimate is an explicit hypothesis of the optimization
lemmas below. None of these implications proves that estimate for a random
vector. The actual Gaussian derivative alternatives remain a separate
analytic obligation.
-/

namespace RectangleCLT

/-- Elementary optimization with a balancing scale whose two contributions
are equal. The estimate covers a vanishing fourth-order term. -/
theorem rate_of_balanced_master {error δ T F K B t C : ℝ}
    (hδ : 0 < δ) (hT : 0 ≤ T) (hK : 0 ≤ K) (hB : 0 ≤ B) (ht : 0 ≤ t)
    (hF : F = B * t) (hbalance : K * t = B) (hC : 0 ≤ C)
    (hunit : error ≤ 1)
    (hmaster : ∀ h : ℝ, 12 * δ ≤ h → error ≤ C * (T + F / h + K * h)) :
    error ≤ max 1 (13 * C) * min 1 (T + B + K * δ) := by
  have hband : 0 < 12 * (δ + t) := by positivity
  have hadmissible : 12 * δ ≤ 12 * (δ + t) := by linarith
  have hfourth : F / (12 * (δ + t)) ≤ B / 12 := by
    apply (div_le_iff₀ hband).mpr
    rw [hF]
    nlinarith [mul_nonneg hB hδ.le]
  have hendpoint : K * (12 * (δ + t)) = 12 * (K * δ + B) := by
    rw [show K * (12 * (δ + t)) = 12 * (K * δ + K * t) by ring, hbalance]
  have hrate : 0 ≤ T + B + K * δ := by positivity
  apply le_max_mul_min_of_le_one hrate hunit
  calc
    error ≤ C * (T + F / (12 * (δ + t)) + K * (12 * (δ + t))) :=
      hmaster _ hadmissible
    _ ≤ C * (13 * (T + B + K * δ)) := by
      apply mul_le_mul_of_nonneg_left _ hC
      rw [hendpoint]
      nlinarith [mul_nonneg hK hδ.le]
    _ = 13 * C * (T + B + K * δ) := by ring

/-- Optimizing a nonnegative fourth-order coefficient `F` against the
endpoint coefficient `K` produces `sqrt(F*K)`, with no division by `F`. -/
theorem weighted_rate_of_master {error δ T F K C : ℝ}
    (hδ : 0 < δ) (hT : 0 ≤ T) (hF : 0 ≤ F) (hK : 0 < K) (hC : 0 ≤ C)
    (hunit : error ≤ 1)
    (hmaster : ∀ h : ℝ, 12 * δ ≤ h → error ≤ C * (T + F / h + K * h)) :
    error ≤ max 1 (13 * C) * min 1 (T + Real.sqrt (F * K) + K * δ) := by
  have hsK : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK
  have hfactor : F = Real.sqrt (F * K) * (Real.sqrt F / Real.sqrt K) := by
    rw [Real.sqrt_mul hF]
    calc
      F = Real.sqrt F ^ 2 := (Real.sq_sqrt hF).symm
      _ = (Real.sqrt F * Real.sqrt K) * (Real.sqrt F / Real.sqrt K) := by
        field_simp [hsK.ne']
        ring
  have hbalance : K * (Real.sqrt F / Real.sqrt K) = Real.sqrt (F * K) := by
    rw [Real.sqrt_mul hF, ← mul_div_assoc]
    apply (div_eq_iff hsK.ne').mpr
    calc
      K * Real.sqrt F = Real.sqrt F * Real.sqrt K ^ 2 := by
        rw [Real.sq_sqrt hK.le]
        ring
      _ = Real.sqrt F * Real.sqrt K * Real.sqrt K := by ring
  exact rate_of_balanced_master hδ hT hK.le (Real.sqrt_nonneg _)
    (div_nonneg (Real.sqrt_nonneg _) hsK.le) hfactor hbalance hC hunit hmaster

/-- Exact square-root simplification of the balanced fourth-order term.
Its coefficient is `β₄/sqrt c`, so the global branch is `1/(b*sqrt c)`. -/
theorem combined_fourth_balance {γ₄ L β c : ℝ}
    (hγ₄ : 0 ≤ γ₄) (hL : 0 ≤ L) (hβ : 0 ≤ β) (hc : 0 < c) :
    Real.sqrt ((γ₄ * L * Real.sqrt L * β ^ 2) * (Real.sqrt L / c)) =
      Real.sqrt γ₄ * L / Real.sqrt c * β := by
  have hexpr : (γ₄ * L * Real.sqrt L * β ^ 2) * (Real.sqrt L / c) =
      (γ₄ * (L * β) ^ 2) / c := by
    rw [show (γ₄ * L * Real.sqrt L * β ^ 2) * (Real.sqrt L / c) =
      γ₄ * L * (Real.sqrt L) ^ 2 * β ^ 2 / c by ring, Real.sq_sqrt hL]
    ring
  rw [hexpr, Real.sqrt_div (by positivity), Real.sqrt_mul hγ₄,
    Real.sqrt_sq (mul_nonneg hL hβ)]
  ring

/-- Scalar derivation of the exact combined rate from the corresponding
master expression. The analytic master expression remains an assumption. -/
theorem combined_rate_of_master {error δ γ₃ γ₄ L b c a₃ a₄ C : ℝ}
    (hδ : 0 < δ) (hγ₃ : 0 ≤ γ₃) (hγ₄ : 0 ≤ γ₄) (hL : 1 ≤ L)
    (hc : 0 < c) (ha₃ : 0 < a₃) (ha₄ : 0 < a₄) (hC : 0 ≤ C)
    (hunit : error ≤ 1)
    (hmaster : ∀ h : ℝ, 12 * δ ≤ h → error ≤ C *
      (γ₃ * L * Real.sqrt L * combinedThirdCoefficient b c a₃ +
        γ₄ * L * Real.sqrt L * combinedFourthCoefficient b c a₃ a₄ ^ 2 / h +
        Real.sqrt L / c * h)) :
    error ≤ max 1 (13 * C) *
      min 1 (combinedCoefficientRate δ γ₃ γ₄ L b c a₃ a₄) := by
  have hL₀ : 0 ≤ L := by linarith
  have hsL : 0 < Real.sqrt L := Real.sqrt_pos.mpr (by linarith)
  have hβ₃ := combinedThirdCoefficient_nonneg (b := b) hc ha₃
  have hβ₄ := combinedFourthCoefficient_nonneg (b := b) hc ha₃ ha₄
  have hoptimized := weighted_rate_of_master hδ
    (show 0 ≤ γ₃ * L * Real.sqrt L * combinedThirdCoefficient b c a₃ by positivity)
    (show 0 ≤ γ₄ * L * Real.sqrt L * combinedFourthCoefficient b c a₃ a₄ ^ 2 by
      positivity)
    (div_pos hsL hc) hC hunit hmaster
  rw [combined_fourth_balance hγ₄ hL₀ hβ₄ hc] at hoptimized
  simpa only [combinedCoefficientRate, div_mul_eq_mul_div, mul_comm δ] using hoptimized

end RectangleCLT
