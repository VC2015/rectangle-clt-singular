import RectangleCLTCompanion.Optimization
import RectangleCLT.InterpolationIntegration
import RectangleCLT.DerivativeIntegration

/-!
# Integrating the companion's two derivative ranges

The actual continuous curve and its derivative occur in these statements.
The probabilistic early and late estimates remain explicit hypotheses. The
switching time is `L * h²`; integrating the reciprocal time factor produces
`comparisonLog L h`. These lemmas do not assert the companion CLT.
-/

open MeasureTheory Set
open scoped Interval

namespace RectangleCLT.Companion

private theorem abs_sub_le_integral_on_interval
    {P d g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn P (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt P (d t) t)
    (hg : IntegrableOn g (Icc a b))
    (hbound : ∀ t ∈ Ioo a b, |d t| ≤ g t) :
    |P b - P a| ≤ ∫ t in a..b, g t := by
  have hp := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hab hc
    (fun t ht => (hd t ht).hasDerivWithinAt) hg
    (fun t ht => (abs_le.mp (hbound t ht)).2)
  have hn := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hab hc.neg
    (fun t ht => (hd t ht).neg.hasDerivWithinAt) hg
    (fun t ht => by linarith [(abs_le.mp (hbound t ht)).1])
  exact abs_le.mpr ⟨by linarith, hp⟩

/-- An admissible bandwidth places the switching time after the lower
cutoff at which the late probabilistic derivative estimate is available. -/
theorem switchTime_ge_derivative_cutoff {A d₀ δ L h : ℝ}
    (hA : 0 ≤ A) (hδ : 0 ≤ δ) (hL : 0 ≤ L) (hband : A * δ ≤ h)
    (hcutoff : d₀ ≤ A ^ 2) :
    d₀ * δ ^ 2 * L ≤ L * h ^ 2 := by
  have hsq := pow_le_pow_left₀ (mul_nonneg hA hδ) hband 2
  rw [mul_pow] at hsq
  have hm := mul_le_mul_of_nonneg_right hcutoff (sq_nonneg δ)
  have hs : d₀ * δ ^ 2 ≤ h ^ 2 := hm.trans hsq
  simpa only [mul_comm L] using mul_le_mul_of_nonneg_right hs hL

/-- Integrate arbitrary nonnegative cubic and fourth-order coefficients.
No integrability of the derivative is assumed: the fundamental theorem of
calculus is applied directly with integrable comparison functions. -/
theorem abs_sub_le_of_two_ranges
    {P d : ℝ → ℝ} {C a b L h : ℝ}
    (hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b) (hL : 0 < L) (hh : 0 < h)
    (hc : ContinuousOn P (Icc 0 1))
    (hd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt P (d t) t)
    (hearly : ∀ t ∈ Ioo (0 : ℝ) 1,
      |d t| ≤ C * Real.sqrt L * (t * a / h ^ 2 + b / h ^ 3))
    (hlate : ∀ t ∈ Ioo (0 : ℝ) 1, L * h ^ 2 ≤ t →
      |d t| ≤ C * L * Real.sqrt L * (a + b / (t * h))) :
    |P 1 - P 0| ≤ C * L * Real.sqrt L *
      (2 * a + (b / h) * (1 + comparisonLog L h)) := by
  let τ := L * h ^ 2
  let K := C * L * Real.sqrt L
  have hτ : 0 < τ := mul_pos hL (sq_pos_of_pos hh)
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg hC hL.le) (Real.sqrt_nonneg L)
  have hbh : 0 ≤ b / h := div_nonneg hb hh.le
  have hlog : 0 ≤ comparisonLog L h := le_max_left _ _
  have hlogτ : Real.log (1 / τ) ≤ comparisonLog L h := le_max_right _ _
  have hconst : IntegrableOn (fun _ : ℝ => (C * Real.sqrt L * (a / h ^ 2 + b / h ^ 3)))
      (Icc (0 : ℝ) 1) := continuousOn_const.integrableOn_Icc
  have hwhole : |P 1 - P 0| ≤ C * Real.sqrt L * (a / h ^ 2 + b / h ^ 3) := by
    have hp := abs_sub_le_integral_on_interval (by norm_num : (0 : ℝ) ≤ 1) hc hd hconst
      (fun t ht => by
        have hm : t * a / h ^ 2 ≤ a / h ^ 2 := by
          simpa only [one_mul] using div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right ht.2.le ha) (sq_nonneg h)
        exact (hearly t ht).trans (mul_le_mul_of_nonneg_left
          (add_le_add_right hm _) (mul_nonneg hC (Real.sqrt_nonneg L))))
    simpa only [intervalIntegral.integral_const, sub_zero, one_smul] using hp
  by_cases hτ1 : τ ≤ 1
  · have hcont0 : ContinuousOn P (Icc 0 τ) := hc.mono (Icc_subset_Icc le_rfl hτ1)
    have hcont1 : ContinuousOn P (Icc τ 1) := hc.mono (Icc_subset_Icc hτ.le le_rfl)
    have hleft0 : |P τ - P 0| ≤ τ *
        (C * Real.sqrt L * (τ * a / h ^ 2 + b / h ^ 3)) := by
      have hp := abs_sub_le_integral_on_interval hτ.le hcont0
        (fun t ht => hd t ⟨ht.1, ht.2.trans_le hτ1⟩)
        continuousOn_const.integrableOn_Icc
        (fun t ht => (hearly t ⟨ht.1, ht.2.trans_le hτ1⟩).trans
          (mul_le_mul_of_nonneg_left
            (add_le_add_right (div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right ht.2.le ha) (sq_nonneg h)) _)
            (mul_nonneg hC (Real.sqrt_nonneg L))))
      simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] using hp
    have hbalance : τ * (C * Real.sqrt L * (τ * a / h ^ 2 + b / h ^ 3)) =
        K * (a * τ + b / h) := by
      dsimp [τ, K]
      field_simp
      ring
    have hleft : |P τ - P 0| ≤ K * (a + b / h) := by
      rw [hbalance] at hleft0
      exact hleft0.trans (mul_le_mul_of_nonneg_left
        (add_le_add_right (mul_le_of_le_one_right ha hτ1) _) hK)
    have hInv : ContinuousOn (fun t : ℝ => t⁻¹) (Icc τ 1) :=
      continuousOn_id.inv₀ (fun t ht => ne_of_gt (hτ.trans_le ht.1))
    have hg : IntegrableOn (fun t : ℝ => K * a + (K * b / h) * t⁻¹) (Icc τ 1) :=
      (continuousOn_const.add (continuousOn_const.mul hInv)).integrableOn_Icc
    have hright0 := abs_sub_le_integral_on_interval hτ1 hcont1
      (fun t ht => hd t ⟨hτ.trans ht.1, ht.2⟩) hg
      (fun t ht => (hlate t ⟨hτ.trans ht.1, ht.2⟩ ht.1.le).trans_eq (by
        dsimp [K]
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring))
    rw [intervalIntegral.integral_add intervalIntegrable_const
      ((hInv.intervalIntegrable_of_Icc hτ1).const_mul (K * b / h)),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      integral_inv_of_pos hτ (by norm_num : (0 : ℝ) < 1)] at hright0
    simp only [smul_eq_mul] at hright0
    have hright : |P 1 - P τ| ≤ K * (a + (b / h) * comparisonLog L h) := by
      have hcubic : (1 - τ) * (K * a) ≤ K * a := by
        have hm := mul_nonneg hτ.le (mul_nonneg hK ha)
        nlinarith
      have hfourth := mul_le_mul_of_nonneg_left hlogτ
        (div_nonneg (mul_nonneg hK hb) hh.le)
      apply hright0.trans
      exact (add_le_add hcubic hfourth).trans_eq (by ring)
    have htriangle : |P 1 - P 0| ≤ |P 1 - P τ| + |P τ - P 0| := abs_sub_le _ _ _
    exact (htriangle.trans (add_le_add hright hleft)).trans_eq (by dsimp [K]; ring)
  · have hτge : 1 ≤ τ := le_of_lt (lt_of_not_ge hτ1)
    have hA : 0 ≤ C * Real.sqrt L * (a / h ^ 2 + b / h ^ 3) :=
      mul_nonneg (mul_nonneg hC (Real.sqrt_nonneg L))
        (add_nonneg (div_nonneg ha (sq_nonneg h)) (div_nonneg hb (pow_nonneg hh.le 3)))
    have hbalance : (C * Real.sqrt L * (a / h ^ 2 + b / h ^ 3)) * τ =
        K * (a + b / h) := by
      dsimp [τ, K]
      field_simp
      ring
    have hcap : C * Real.sqrt L * (a / h ^ 2 + b / h ^ 3) ≤ K * (a + b / h) := by
      have hm := mul_le_mul_of_nonneg_left hτge hA
      rw [mul_one, hbalance] at hm
      exact hm
    exact (hwhole.trans hcap).trans (mul_le_mul_of_nonneg_left (by
      nlinarith [mul_nonneg hbh hlog]) hK)

/-- Appendix D's general smoothed comparison, with an explicit factor three.
The early and late probabilistic estimates are explicit hypotheses. -/
theorem smoothed_gap_le_of_early_late
    {P d : ℝ → ℝ} {C δ L h : ℝ}
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hL : 1 ≤ L) (hh : 0 < h) (hδh : δ ≤ h)
    (hc : ContinuousOn P (Icc 0 1))
    (hd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt P (d t) t)
    (hearly : ∀ t ∈ Ioo (0 : ℝ) 1,
      |d t| ≤ C * Real.sqrt L * (t * δ / h ^ 2 + δ ^ 2 / h ^ 3))
    (hlate : ∀ t ∈ Ioo (0 : ℝ) 1, L * h ^ 2 ≤ t →
      |d t| ≤ C * L * Real.sqrt L * (δ + δ ^ 2 / (t * h))) :
    |P 1 - P 0| ≤ 3 * C * L * Real.sqrt L *
      (δ + (δ ^ 2 / h) * comparisonLog L h) := by
  have hm := abs_sub_le_of_two_ranges hC hδ (sq_nonneg δ)
    (lt_of_lt_of_le zero_lt_one hL) hh hc hd hearly hlate
  have hsmall : δ ^ 2 / h ≤ δ := by
    apply (div_le_iff₀ hh).mpr
    nlinarith [mul_nonneg hδ (sub_nonneg.mpr hδh)]
  have hq : 0 ≤ comparisonLog L h := le_max_left _ _
  have hb : 0 ≤ δ ^ 2 / h := div_nonneg (sq_nonneg _) hh.le
  have hs : 2 * δ + (δ ^ 2 / h) * (1 + comparisonLog L h) ≤
      3 * (δ + (δ ^ 2 / h) * comparisonLog L h) := by
    nlinarith [mul_nonneg hb hq]
  exact hm.trans ((mul_le_mul_of_nonneg_left hs
    (mul_nonneg (mul_nonneg hC (by linarith : 0 ≤ L)) (Real.sqrt_nonneg L))).trans_eq (by ring))

/-- Under cancellation of the cubic term, integration retains the smaller
fourth-order expression, including its additive one before the logarithm. -/
theorem zero_cubic_gap_le_of_early_late
    {P d : ℝ → ℝ} {C δ L h : ℝ}
    (hC : 0 ≤ C) (hL : 0 < L) (hh : 0 < h)
    (hc : ContinuousOn P (Icc 0 1))
    (hd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt P (d t) t)
    (hearly : ∀ t ∈ Ioo (0 : ℝ) 1,
      |d t| ≤ C * Real.sqrt L * (δ ^ 2 / h ^ 3))
    (hlate : ∀ t ∈ Ioo (0 : ℝ) 1, L * h ^ 2 ≤ t →
      |d t| ≤ C * L * Real.sqrt L * (δ ^ 2 / (t * h))) :
    |P 1 - P 0| ≤ C * L * Real.sqrt L * (δ ^ 2 / h) * (1 + comparisonLog L h) := by
  have hm := abs_sub_le_of_two_ranges (a := 0) (b := δ ^ 2) hC le_rfl
    (sq_nonneg δ) hL hh hc hd
    (fun t ht => by simpa only [mul_zero, zero_div, zero_add] using hearly t ht)
    (fun t ht hb => by simpa only [zero_add] using hlate t ht hb)
  simpa only [mul_zero, zero_add, mul_assoc] using hm

end RectangleCLT.Companion
