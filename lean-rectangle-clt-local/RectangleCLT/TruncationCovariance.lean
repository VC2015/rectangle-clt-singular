import RectangleCLT.ProxyCovariance
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Coordinate normalization with a fixed covariance proxy

The matrix used as proxy is an independent argument throughout.  No local
eigenvalue of a truncated or normalized covariance is introduced.
-/

namespace RectangleCLT

noncomputable section

/-- Coordinate normalization of a covariance matrix by standard deviations. -/
def normalizeCovariance {p : ℕ} (C : Matrix (Fin p) (Fin p) ℝ)
    (d : Vector p) : Matrix (Fin p) (Fin p) ℝ :=
  fun j k => C j k / (d j * d k)

theorem normalizeCovariance_unit_diagonal {p : ℕ}
    (C : Matrix (Fin p) (Fin p) ℝ) (d : Vector p)
    (hd : ∀ j, 0 < d j) (hdiag : ∀ j, d j ^ 2 = C j j) :
    ∀ j, normalizeCovariance C d j j = 1 := by
  intro j
  unfold normalizeCovariance
  rw [← hdiag j, pow_two]
  exact div_self (mul_ne_zero (ne_of_gt (hd j)) (ne_of_gt (hd j)))

/-- If both diagonal variances lie in `[1-ε,1]`, their standard-deviation
product also lies in `[1-ε,1]`. -/
theorem standard_deviation_product_bounds {ε d e : ℝ}
    (hε : ε < 1) (hd : 0 < d) (he : 0 < e)
    (hdlo : 1 - ε ≤ d ^ 2) (helo : 1 - ε ≤ e ^ 2)
    (hdhi : d ^ 2 ≤ 1) (hehi : e ^ 2 ≤ 1) :
    1 - ε ≤ d * e ∧ d * e ≤ 1 := by
  have hd1 : d ≤ 1 := by nlinarith
  have he1 : e ≤ 1 := by nlinarith
  have hprod : (1 - ε) * (1 - ε) ≤ d ^ 2 * e ^ 2 :=
    mul_le_mul hdlo helo (by linarith) (sq_nonneg d)
  constructor
  · nlinarith [mul_pos hd he]
  · simpa only [one_mul] using mul_le_mul hd1 he1 he.le (by norm_num : (0 : ℝ) ≤ 1)

/-- The diagonal inverse remains close to one when the discarded variance
is at most `ε<1/2`. -/
theorem standard_deviation_inverse_sub_le {ε d : ℝ}
    (hε : 0 ≤ ε) (hεhalf : ε < 1 / 2) (hd : 0 < d)
    (hdlo : 1 - ε ≤ d ^ 2) (hdhi : d ^ 2 ≤ 1) :
    |1 - d⁻¹| ≤ 2 * ε := by
  have hd1 : d ≤ 1 := by nlinarith
  have hdlo' : 1 - ε ≤ d := by nlinarith [mul_nonneg hd.le (by linarith : 0 ≤ 1 - d)]
  have hdhalf : 1 / 2 ≤ d := by linarith
  have heq : 1 - d⁻¹ = -(1 - d) / d := by
    field_simp [ne_of_gt hd]
    <;> ring
  rw [heq, abs_div, abs_neg, abs_of_nonneg (by linarith : 0 ≤ 1 - d), abs_of_pos hd]
  apply (div_le_iff₀ hd).mpr
  nlinarith [mul_nonneg hε (by linarith : 0 ≤ 2 * d - 1)]

/-- A normalized entry moves by at most the variance error.  The bound
`|x| ≤ d*e` is the covariance Cauchy--Schwarz inequality. -/
theorem normalized_entry_sub_le {ε d e x : ℝ}
    (hε : ε < 1) (hd : 0 < d) (he : 0 < e)
    (hdlo : 1 - ε ≤ d ^ 2) (helo : 1 - ε ≤ e ^ 2)
    (hdhi : d ^ 2 ≤ 1) (hehi : e ^ 2 ≤ 1) (hx : |x| ≤ d * e) :
    |x / (d * e) - x| ≤ ε := by
  have ht := standard_deviation_product_bounds hε hd he hdlo helo hdhi hehi
  have hde : 0 < d * e := mul_pos hd he
  have hrepr : x / (d * e) - x = x * (1 - d * e) / (d * e) := by
    field_simp [ne_of_gt hd, ne_of_gt he]
    <;> ring
  rw [hrepr, abs_div, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - d * e),
    abs_of_pos hde]
  calc
    |x| * (1 - d * e) / (d * e) ≤
        (d * e) * (1 - d * e) / (d * e) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hx (by linarith)) hde.le
    _ = 1 - d * e := by field_simp [ne_of_gt hd, ne_of_gt he]
    _ ≤ ε := by linarith [ht.1]

/-- The normalized truncated covariance differs from the original fixed
proxy by `Δ+2ε`.  This statement does not change the proxy. -/
theorem normalized_covariance_fixed_proxy_discrepancy {p : ℕ}
    (S C Q : Matrix (Fin p) (Fin p) ℝ) (d : Vector p) {ε : ℝ}
    (hε : 0 ≤ ε) (hε1 : ε < 1)
    (hd : ∀ j, 0 < d j)
    (hdlo : ∀ j, 1 - ε ≤ d j ^ 2) (hdhi : ∀ j, d j ^ 2 ≤ 1)
    (hCS : ∀ j k, |C j k| ≤ d j * d k)
    (hSC : ∀ j k, |S j k - C j k| ≤ ε) :
    proxyCovarianceDiscrepancy (normalizeCovariance C d) Q ≤
      proxyCovarianceDiscrepancy S Q + 2 * ε := by
  apply (Finset.fold_max_le _).mpr
  refine ⟨by linarith [proxyCovarianceDiscrepancy_nonneg S Q], ?_⟩
  intro jk _
  rcases jk with ⟨j, k⟩
  have hnorm := normalized_entry_sub_le hε1 (hd j) (hd k)
    (hdlo j) (hdlo k) (hdhi j) (hdhi k) (hCS j k)
  change |C j k / (d j * d k) - Q j k| ≤ _
  calc
    |C j k / (d j * d k) - Q j k| =
        |(C j k / (d j * d k) - C j k) +
          (C j k - S j k) + (S j k - Q j k)| := by congr 1 <;> ring
    _ ≤ |C j k / (d j * d k) - C j k| +
        |C j k - S j k| + |S j k - Q j k| :=
      (abs_add _ _).trans (add_le_add_right (abs_add _ _) _)
    _ ≤ ε + ε + proxyCovarianceDiscrepancy S Q := by
      exact add_le_add (add_le_add hnorm (by simpa only [abs_sub_comm] using hSC j k))
        (abs_entry_sub_le_proxyCovarianceDiscrepancy S Q j k)
    _ = proxyCovarianceDiscrepancy S Q + 2 * ε := by ring

end

end RectangleCLT
