import RectangleCLT.Optimization

/-!
# Scalar optimization with local covariance coefficients

These are quantitative scalar implications from an explicit master estimate.
They do not assert that the analytic master estimate has been proved for
random vectors. No global smallest-eigenvalue parameter occurs in the inputs.
The manuscript's `L^(3/2)` is written as `L * sqrt L`.
-/

namespace RectangleCLT

/-- Bandwidth for independently selected cubic and fourth-order coefficients. -/
noncomputable def coefficientOptimizedBandwidth (δ γ₄ L c β₄ : ℝ) : ℝ :=
  12 * (δ + β₄ * Real.sqrt (c * γ₄ * L))

theorem coefficientOptimizedBandwidth_eq_optimizedBandwidth
    (δ γ₄ L c β₄ : ℝ) (hβ₄ : 0 ≤ β₄) :
    coefficientOptimizedBandwidth δ γ₄ L c β₄ =
      optimizedBandwidth δ (c * γ₄ * β₄ ^ 2) L := by
  unfold coefficientOptimizedBandwidth optimizedBandwidth
  have hrad : (c * γ₄ * β₄ ^ 2) * L = β₄ ^ 2 * (c * γ₄ * L) := by ring
  rw [hrad, Real.sqrt_mul (sq_nonneg β₄), Real.sqrt_sq hβ₄]

theorem twelve_delta_le_coefficientOptimizedBandwidth
    (δ γ₄ L c β₄ : ℝ) (hβ₄ : 0 ≤ β₄) :
    12 * δ ≤ coefficientOptimizedBandwidth δ γ₄ L c β₄ := by
  unfold coefficientOptimizedBandwidth
  nlinarith [mul_nonneg hβ₄ (Real.sqrt_nonneg (c * γ₄ * L))]

theorem coefficientOptimizedBandwidth_pos {δ γ₄ L c β₄ : ℝ}
    (hδ : 0 < δ) (hβ₄ : 0 ≤ β₄) :
    0 < coefficientOptimizedBandwidth δ γ₄ L c β₄ := by
  have h := twelve_delta_le_coefficientOptimizedBandwidth δ γ₄ L c β₄ hβ₄
  linarith

/-- Rescaling the old optimizer yields the coefficient rate. This identity
also covers a zero fourth moment or a zero fourth-order coefficient. -/
theorem coefficient_normalized_rate {δ γ₃ γ₄ L c β₃ β₄ : ℝ}
    (hc : 0 < c) (hγ₄ : 0 ≤ γ₄) (hβ₄ : 0 ≤ β₄) :
    ((c * γ₃ * β₃) * L * Real.sqrt L +
        Real.sqrt (c * γ₄ * β₄ ^ 2) * L + δ * Real.sqrt L) /
        (Real.sqrt c) ^ 2 =
      γ₃ * L * Real.sqrt L * β₃ +
        Real.sqrt γ₄ * L * β₄ / Real.sqrt c + δ * Real.sqrt L / c := by
  rw [Real.sq_sqrt hc.le,
    Real.sqrt_mul (mul_nonneg hc.le hγ₄), Real.sqrt_mul hc.le, Real.sqrt_sq hβ₄]
  have hfirst : (c * γ₃ * β₃) * L * Real.sqrt L / c =
      γ₃ * L * Real.sqrt L * β₃ := by
    field_simp
    ring
  have hsecond : Real.sqrt c * Real.sqrt γ₄ * β₄ * L / c =
      Real.sqrt γ₄ * L * β₄ / Real.sqrt c := by
    calc
      _ = (Real.sqrt c / c) * (Real.sqrt γ₄ * L * β₄) := by ring
      _ = (Real.sqrt c)⁻¹ * (Real.sqrt γ₄ * L * β₄) := by rw [Real.sqrt_div_self]
      _ = _ := by ring
  simp only [add_div, hfirst, hsecond]

/-- Optimization for arbitrary nonnegative cubic and fourth-order coefficients.
The chosen bandwidth is `12 * (δ + β₄ * sqrt (c*γ₄*L))`; the explicit final
constant is `max 1 (13*C)`, independently of every scalar data parameter. -/
theorem coefficient_rate_of_master {error δ γ₃ γ₄ L c β₃ β₄ C : ℝ}
    (hδ : 0 < δ) (hγ₃ : 0 ≤ γ₃) (hγ₄ : 0 ≤ γ₄)
    (hL : 1 ≤ L) (hc : 0 < c) (hβ₃ : 0 ≤ β₃) (hβ₄ : 0 ≤ β₄)
    (hC : 0 ≤ C) (hunit : error ≤ 1)
    (hmaster : ∀ h : ℝ, 12 * δ ≤ h →
      error ≤ C * (γ₃ * L * Real.sqrt L * β₃ +
        γ₄ * L * Real.sqrt L * β₄ ^ 2 / h + h * Real.sqrt L / c)) :
    error ≤ max 1 (13 * C) *
      min 1 (γ₃ * L * Real.sqrt L * β₃ +
        Real.sqrt γ₄ * L * β₄ / Real.sqrt c + δ * Real.sqrt L / c) := by
  have hscaled : ∀ h : ℝ, 12 * δ ≤ h →
      error ≤ C / (Real.sqrt c) ^ 2 *
        ((c * γ₃ * β₃) * L * Real.sqrt L +
          (c * γ₄ * β₄ ^ 2) * L * Real.sqrt L / h + h * Real.sqrt L) := by
    intro h hh
    have hhpos : 0 < h := by linarith
    have halg : C / (Real.sqrt c) ^ 2 *
        ((c * γ₃ * β₃) * L * Real.sqrt L +
          (c * γ₄ * β₄ ^ 2) * L * Real.sqrt L / h + h * Real.sqrt L) =
        C * (γ₃ * L * Real.sqrt L * β₃ +
          γ₄ * L * Real.sqrt L * β₄ ^ 2 / h + h * Real.sqrt L / c) := by
      rw [Real.sq_sqrt hc.le]
      field_simp
      ring
    rw [halg]
    exact hmaster h hh
  have hbound := bounded_rate_of_master hδ
    (mul_nonneg (mul_nonneg hc.le hγ₃) hβ₃)
    (mul_nonneg (mul_nonneg hc.le hγ₄) (sq_nonneg β₄))
    hL (Real.sqrt_pos.mpr hc) hC hunit hscaled
  rw [coefficient_normalized_rate hc hγ₄ hβ₄] at hbound
  exact hbound

/-- The fourth-order local covariance scale `d₄ = (c*a₃*a₄)^(1/3)`. -/
noncomputable def localFourthScale (c a₃ a₄ : ℝ) : ℝ :=
  Real.rpow (c * a₃ * a₄) (1 / 3 : ℝ)

theorem localFourthScale_pos {c a₃ a₄ : ℝ}
    (hc : 0 < c) (ha₃ : 0 < a₃) (ha₄ : 0 < a₄) :
    0 < localFourthScale c a₃ a₄ :=
  Real.rpow_pos_of_pos (mul_pos (mul_pos hc ha₃) ha₄) _

theorem localFourthScale_sq {c a₃ a₄ : ℝ}
    (hc : 0 < c) (ha₃ : 0 < a₃) (ha₄ : 0 < a₄) :
    (localFourthScale c a₃ a₄) ^ 2 =
      Real.rpow (c * a₃ * a₄) (2 / 3 : ℝ) := by
  unfold localFourthScale
  simp only [Real.rpow_eq_pow]
  rw [← Real.rpow_mul_natCast (mul_pos (mul_pos hc ha₃) ha₄).le (1 / 3 : ℝ) 2]
  norm_num

/-- The fractional denominator in the manuscript follows exactly from
`sqrt c * d₄`; the parameters are covariance eigenvalues, not their roots. -/
theorem sqrt_mul_localFourthScale {c a₃ a₄ : ℝ}
    (hc : 0 < c) (ha₃ : 0 < a₃) (ha₄ : 0 < a₄) :
    Real.sqrt c * localFourthScale c a₃ a₄ =
      Real.rpow c (5 / 6 : ℝ) * Real.rpow (a₃ * a₄) (1 / 3 : ℝ) := by
  unfold localFourthScale
  simp only [Real.rpow_eq_pow]
  rw [mul_assoc c a₃ a₄, Real.mul_rpow hc.le (mul_pos ha₃ ha₄).le,
    Real.sqrt_eq_rpow, ← mul_assoc, ← Real.rpow_add hc]
  norm_num

/-- The exact smoothing choice in the local theorem, including `γ₄ = 0`. -/
noncomputable def localOptimizedBandwidth (δ γ₄ L c a₃ a₄ : ℝ) : ℝ :=
  12 * (δ + Real.sqrt (c * γ₄ * L) / localFourthScale c a₃ a₄)

theorem localOptimizedBandwidth_eq_coefficient
    (δ γ₄ L c a₃ a₄ : ℝ) :
    localOptimizedBandwidth δ γ₄ L c a₃ a₄ =
      coefficientOptimizedBandwidth δ γ₄ L c (1 / localFourthScale c a₃ a₄) := by
  unfold localOptimizedBandwidth coefficientOptimizedBandwidth
  ring

theorem twelve_delta_le_localOptimizedBandwidth {δ γ₄ L c a₃ a₄ : ℝ}
    (hc : 0 < c) (ha₃ : 0 < a₃) (ha₄ : 0 < a₄) :
    12 * δ ≤ localOptimizedBandwidth δ γ₄ L c a₃ a₄ := by
  rw [localOptimizedBandwidth_eq_coefficient]
  exact twelve_delta_le_coefficientOptimizedBandwidth _ _ _ _ _
    (one_div_nonneg.mpr (localFourthScale_pos hc ha₃ ha₄).le)

theorem localOptimizedBandwidth_pos {δ γ₄ L c a₃ a₄ : ℝ}
    (hδ : 0 < δ) (hc : 0 < c) (ha₃ : 0 < a₃) (ha₄ : 0 < a₄) :
    0 < localOptimizedBandwidth δ γ₄ L c a₃ a₄ := by
  have h := twelve_delta_le_localOptimizedBandwidth
    (δ := δ) (γ₄ := γ₄) (L := L) hc ha₃ ha₄
  linarith

/-- The scalar local-covariance main rate from the selected local alternatives
of the master estimate. This is precisely the optimization in the supplied
manuscript, with final absolute factor `max 1 (13*C)`.

The premise is the analytic estimate for all admissible `h`; proving that
estimate for actual random vectors remains a separate obligation. -/
theorem local_rate_of_master {error δ γ₃ γ₄ L c a₃ a₄ C : ℝ}
    (hδ : 0 < δ) (hγ₃ : 0 ≤ γ₃) (hγ₄ : 0 ≤ γ₄) (hL : 1 ≤ L)
    (hc : 0 < c) (ha₃ : 0 < a₃) (ha₄ : 0 < a₄)
    (hC : 0 ≤ C) (hunit : error ≤ 1)
    (hmaster : ∀ h : ℝ, 12 * δ ≤ h →
      error ≤ C * (γ₃ * L * Real.sqrt L / (c * a₃) +
        γ₄ * L * Real.sqrt L /
          (h * Real.rpow (c * a₃ * a₄) (2 / 3 : ℝ)) + h * Real.sqrt L / c)) :
    error ≤ max 1 (13 * C) * min 1
      (γ₃ * L * Real.sqrt L / (c * a₃) +
        Real.sqrt γ₄ * L /
          (Real.rpow c (5 / 6 : ℝ) * Real.rpow (a₃ * a₄) (1 / 3 : ℝ)) +
        δ * Real.sqrt L / c) := by
  have hd := localFourthScale_pos hc ha₃ ha₄
  have hselected : ∀ h : ℝ, 12 * δ ≤ h →
      error ≤ C * (γ₃ * L * Real.sqrt L * (1 / (c * a₃)) +
        γ₄ * L * Real.sqrt L * (1 / localFourthScale c a₃ a₄) ^ 2 / h +
        h * Real.sqrt L / c) := by
    intro h hh
    have halg : γ₃ * L * Real.sqrt L * (1 / (c * a₃)) +
        γ₄ * L * Real.sqrt L * (1 / localFourthScale c a₃ a₄) ^ 2 / h +
        h * Real.sqrt L / c =
        γ₃ * L * Real.sqrt L / (c * a₃) +
        γ₄ * L * Real.sqrt L /
          (h * Real.rpow (c * a₃ * a₄) (2 / 3 : ℝ)) + h * Real.sqrt L / c := by
      rw [← localFourthScale_sq hc ha₃ ha₄]
      ring
    rw [halg]
    exact hmaster h hh
  have hbound := coefficient_rate_of_master hδ hγ₃ hγ₄ hL hc
    (one_div_nonneg.mpr (mul_pos hc ha₃).le) (one_div_nonneg.mpr hd.le)
    hC hunit hselected
  have hrate : γ₃ * L * Real.sqrt L * (1 / (c * a₃)) +
      Real.sqrt γ₄ * L * (1 / localFourthScale c a₃ a₄) / Real.sqrt c +
      δ * Real.sqrt L / c =
      γ₃ * L * Real.sqrt L / (c * a₃) + Real.sqrt γ₄ * L /
        (Real.rpow c (5 / 6 : ℝ) * Real.rpow (a₃ * a₄) (1 / 3 : ℝ)) +
        δ * Real.sqrt L / c := by
    rw [← sqrt_mul_localFourthScale hc ha₃ ha₄]
    ring
  rw [hrate] at hbound
  exact hbound

end RectangleCLT
