import Kane.Analytic

/-!
# The scalar optimization following the rectangle CLT master estimate

These lemmas prove the optimization in Section 6 of the supplied manuscript.
The final theorem is conditional on the analytic master estimate. In particular,
it does not establish that estimate for random vectors or assert a rectangle CLT.
-/

namespace RectangleCLT

/-- The smoothing bandwidth used to optimize the master estimate. -/
noncomputable def optimizedBandwidth (δ γ₄ L : ℝ) : ℝ :=
  12 * (δ + Real.sqrt (γ₄ * L))

theorem optimizedBandwidth_pos {δ γ₄ L : ℝ} (hδ : 0 < δ) :
    0 < optimizedBandwidth δ γ₄ L := by
  unfold optimizedBandwidth
  positivity

theorem twelve_delta_le_optimizedBandwidth (δ γ₄ L : ℝ) :
    12 * δ ≤ optimizedBandwidth δ γ₄ L := by
  unfold optimizedBandwidth
  nlinarith [Real.sqrt_nonneg (γ₄ * L)]

/-- The endpoint term after choosing the bandwidth, including zero fourth moment. -/
theorem optimizedBandwidth_mul_sqrt {δ γ₄ L : ℝ}
    (hγ₄ : 0 ≤ γ₄) (hL : 0 ≤ L) :
    optimizedBandwidth δ γ₄ L * Real.sqrt L =
      12 * (δ * Real.sqrt L + Real.sqrt γ₄ * L) := by
  unfold optimizedBandwidth
  rw [Real.sqrt_mul hγ₄]
  calc
    12 * (δ + Real.sqrt γ₄ * Real.sqrt L) * Real.sqrt L =
        12 * (δ * Real.sqrt L + Real.sqrt γ₄ * (Real.sqrt L) ^ 2) := by ring
    _ = 12 * (δ * Real.sqrt L + Real.sqrt γ₄ * L) := by rw [Real.sq_sqrt hL]

/-- The fourth-moment term after choosing the bandwidth. -/
theorem fourth_term_le_at_optimizedBandwidth {δ γ₄ L : ℝ}
    (hδ : 0 < δ) (hγ₄ : 0 ≤ γ₄) (hL : 0 ≤ L) :
    γ₄ * L * Real.sqrt L / optimizedBandwidth δ γ₄ L ≤
      Real.sqrt γ₄ * L / 12 := by
  apply (div_le_iff₀ (optimizedBandwidth_pos hδ)).2
  have hprod : γ₄ * L * Real.sqrt L =
      (Real.sqrt γ₄ * L) * Real.sqrt (γ₄ * L) := by
    rw [Real.sqrt_mul hγ₄]
    calc
      γ₄ * L * Real.sqrt L = (Real.sqrt γ₄) ^ 2 * L * Real.sqrt L := by
        rw [Real.sq_sqrt hγ₄]
      _ = (Real.sqrt γ₄ * L) * (Real.sqrt γ₄ * Real.sqrt L) := by ring
  rw [hprod]
  have hq : 0 ≤ Real.sqrt γ₄ * L := by positivity
  unfold optimizedBandwidth
  nlinarith [mul_nonneg hδ.le hq]

/-- An error bounded by one and by a nonnegative multiple of a rate can be
written using the minimum of one and that rate. -/
theorem le_max_mul_min_of_le_one {error factor rate : ℝ}
    (hrate : 0 ≤ rate) (hunit : error ≤ 1)
    (hbound : error ≤ factor * rate) :
    error ≤ max 1 factor * min 1 rate := by
  by_cases hsmall : rate ≤ 1
  · rw [min_eq_right hsmall]
    exact hbound.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hrate)
  · rw [min_eq_left (le_of_not_ge hsmall), mul_one]
    exact hunit.trans (le_max_left _ _)

/-- Optimization of the manuscript's master estimate. The assumptions explicitly
include that estimate for every admissible bandwidth; no probabilistic or
analytic part of the CLT is asserted by this scalar implication.

The manuscript writes `L^(3/2)`; here it is represented by `L * sqrt L`.
The explicit constant `max 1 (13 * C)` absorbs the bandwidth constants and the
trivial bound by one. The proof covers `γ₃ = 0` and `γ₄ = 0` without limits. -/
theorem bounded_rate_of_master {error δ γ₃ γ₄ L b C : ℝ}
    (hδ : 0 < δ) (hγ₃ : 0 ≤ γ₃) (hγ₄ : 0 ≤ γ₄)
    (hL : 1 ≤ L) (hb : 0 < b) (hC : 0 ≤ C)
    (hunit : error ≤ 1)
    (hmaster : ∀ h : ℝ, 12 * δ ≤ h →
      error ≤ C / b ^ 2 *
        (γ₃ * L * Real.sqrt L + γ₄ * L * Real.sqrt L / h + h * Real.sqrt L)) :
    error ≤ max 1 (13 * C) *
      min 1 ((γ₃ * L * Real.sqrt L + Real.sqrt γ₄ * L + δ * Real.sqrt L) /
        b ^ 2) := by
  have hL0 : 0 ≤ L := by linarith
  have hb2 : 0 < b ^ 2 := sq_pos_of_pos hb
  have hrate : 0 ≤
      (γ₃ * L * Real.sqrt L + Real.sqrt γ₄ * L + δ * Real.sqrt L) / b ^ 2 := by
    positivity
  apply le_max_mul_min_of_le_one hrate hunit
  have hchosen := hmaster (optimizedBandwidth δ γ₄ L)
    (twelve_delta_le_optimizedBandwidth δ γ₄ L)
  have hfourth := fourth_term_le_at_optimizedBandwidth hδ hγ₄ hL0
  have hendpoint := optimizedBandwidth_mul_sqrt (δ := δ) hγ₄ hL0
  have hsum : γ₃ * L * Real.sqrt L +
        γ₄ * L * Real.sqrt L / optimizedBandwidth δ γ₄ L +
        optimizedBandwidth δ γ₄ L * Real.sqrt L ≤
      13 * (γ₃ * L * Real.sqrt L + Real.sqrt γ₄ * L + δ * Real.sqrt L) := by
    rw [hendpoint]
    have hthird : 0 ≤ γ₃ * L * Real.sqrt L := by positivity
    have hfourth' : 0 ≤ Real.sqrt γ₄ * L := by positivity
    have henvelope : 0 ≤ δ * Real.sqrt L := by positivity
    nlinarith
  calc
    error ≤ C / b ^ 2 *
        (γ₃ * L * Real.sqrt L +
          γ₄ * L * Real.sqrt L / optimizedBandwidth δ γ₄ L +
          optimizedBandwidth δ γ₄ L * Real.sqrt L) := hchosen
    _ ≤ C / b ^ 2 *
        (13 * (γ₃ * L * Real.sqrt L + Real.sqrt γ₄ * L + δ * Real.sqrt L)) :=
      mul_le_mul_of_nonneg_left hsum (div_nonneg hC hb2.le)
    _ = (13 * C) *
        ((γ₃ * L * Real.sqrt L + Real.sqrt γ₄ * L + δ * Real.sqrt L) / b ^ 2) := by
      ring

/-- The dimension factor `log (e p)` is at least one in positive dimension. -/
theorem log_exp_mul_nat_ge_one {p : ℕ} (hp : 1 ≤ p) :
    1 ≤ Real.log (Real.exp 1 * (p : ℝ)) := by
  have hp' : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hprod : Real.exp 1 ≤ Real.exp 1 * (p : ℝ) := by
    nlinarith [Real.exp_pos (1 : ℝ)]
  simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hprod

/-- The logarithm in the rectangle sensitivity bound is controlled by twice
the dimension logarithm used in the CLT rate. -/
theorem log_two_mul_nat_add_one_le_two_log_exp_mul {p : ℕ} (hp : 1 ≤ p) :
    Real.log (2 * (p : ℝ) + 1) ≤ 2 * Real.log (Real.exp 1 * (p : ℝ)) := by
  have hp' : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := by linarith
  have he : (2 : ℝ) ≤ Real.exp 1 := by
    simpa only [one_add_one_eq_two] using Real.add_one_le_exp (1 : ℝ)
  have hbase : 2 * (p : ℝ) + 1 ≤ (2 * (p : ℝ)) ^ 2 := by nlinarith
  have hsq : (2 * (p : ℝ)) ^ 2 ≤ (Real.exp 1 * (p : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right he hp0) 2
  have hlog := Real.log_le_log (by positivity : 0 < 2 * (p : ℝ) + 1)
    (hbase.trans hsq)
  simpa only [Real.log_pow, Nat.cast_ofNat] using hlog

/-- The bounded-summand fourth-moment estimate simplifies the two lower-order
terms in the rate numerator. The nonnegativity of `γ₄` is not needed for this
scalar implication because the real square root vanishes on negative inputs. -/
theorem rate_numerator_le_third_add_two_delta_log {δ γ₃ γ₄ L : ℝ}
    (hδ : 0 ≤ δ) (hγ₄ : γ₄ ≤ δ ^ 2) (hL : 1 ≤ L) :
    γ₃ * L * Real.sqrt L + Real.sqrt γ₄ * L + δ * Real.sqrt L ≤
      γ₃ * L * Real.sqrt L + 2 * δ * L := by
  have hL0 : 0 ≤ L := by linarith
  have hsγ : Real.sqrt γ₄ ≤ δ := Real.sqrt_le_iff.mpr ⟨hδ, hγ₄⟩
  have hsL : Real.sqrt L ≤ L := by
    calc
      Real.sqrt L = Real.sqrt L * 1 := by ring
      _ ≤ Real.sqrt L * Real.sqrt L :=
        mul_le_mul_of_nonneg_left (Real.one_le_sqrt.mpr hL) (Real.sqrt_nonneg L)
      _ = L := Real.mul_self_sqrt hL0
  have hfourth := mul_le_mul_of_nonneg_right hsγ hL0
  have henvelope := mul_le_mul_of_nonneg_left hsL hδ
  linarith

/-- The envelope bounds on both aggregate moments give the familiar
`δ L^(3/2)` numerator, with the explicit scalar constant three. -/
theorem rate_numerator_le_three_delta_log_sqrt {δ γ₃ γ₄ L : ℝ}
    (hδ : 0 ≤ δ) (hγ₃ : γ₃ ≤ δ) (hγ₄ : γ₄ ≤ δ ^ 2) (hL : 1 ≤ L) :
    γ₃ * L * Real.sqrt L + Real.sqrt γ₄ * L + δ * Real.sqrt L ≤
      3 * δ * L * Real.sqrt L := by
  have hL0 : 0 ≤ L := by linarith
  have hthird : γ₃ * L * Real.sqrt L ≤ δ * L * Real.sqrt L := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hγ₃ hL0) (Real.sqrt_nonneg L)
  have hlower : 2 * δ * L ≤ 2 * δ * L * Real.sqrt L := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (Real.one_le_sqrt.mpr hL)
        (show 0 ≤ 2 * δ * L by positivity)
  calc
    γ₃ * L * Real.sqrt L + Real.sqrt γ₄ * L + δ * Real.sqrt L ≤
        γ₃ * L * Real.sqrt L + 2 * δ * L :=
      rate_numerator_le_third_add_two_delta_log hδ hγ₄ hL
    _ ≤ 3 * δ * L * Real.sqrt L := by linarith

/-- Cancellation of the aggregate third moments leaves the sharper `δ L`
numerator under the bounded-summand fourth-moment estimate. -/
theorem rate_numerator_le_two_delta_log_of_third_eq_zero {δ γ₃ γ₄ L : ℝ}
    (hδ : 0 ≤ δ) (hγ₃ : γ₃ = 0) (hγ₄ : γ₄ ≤ δ ^ 2) (hL : 1 ≤ L) :
    γ₃ * L * Real.sqrt L + Real.sqrt γ₄ * L + δ * Real.sqrt L ≤
      2 * δ * L := by
  simpa only [hγ₃, zero_mul, zero_add] using
    rate_numerator_le_third_add_two_delta_log (γ₃ := γ₃) hδ hγ₄ hL

end RectangleCLT
