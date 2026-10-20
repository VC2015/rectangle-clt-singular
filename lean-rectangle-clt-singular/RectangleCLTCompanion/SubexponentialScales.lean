import RectangleCLTCompanion.SubexponentialRates

/-! Cutoff, union-bound and transfer-error scales for the tail corollary.
The estimates use only positive dimensions and `K ≥ 1`; in particular the
cutoff remains proportional to `log(en)`, independently of the dimension. -/

namespace RectangleCLT.Companion

noncomputable section

set_option autoImplicit false

def subexponentialUnionLog (n p : ℕ) : ℝ := Real.log (4 * (n : ℝ) * (p : ℝ))

def subexponentialTailFactor (n : ℕ) : ℝ := Real.exp (-2 * dimensionLog n)

def subexponentialResidualSD (n : ℕ) (K : ℝ) : ℝ :=
  2 * K * subexponentialTailFactor n

def subexponentialResidualRadius (n p : ℕ) (K : ℝ) : ℝ :=
  8 * K * subexponentialTailFactor n * Real.sqrt (subexponentialUnionLog n p) +
    4 * K * subexponentialUnionLog n p / Real.sqrt (n : ℝ)

def subexponentialGaussianRadius (n p : ℕ) (K : ℝ) : ℝ :=
  subexponentialResidualSD n K * Real.sqrt (2 * subexponentialUnionLog n p)

theorem dimensionLog_eq_one_add_log {n : ℕ} (hn : 1 ≤ n) :
    dimensionLog n = 1 + Real.log (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [dimensionLog, Real.log_mul (Real.exp_ne_zero _) hnR.ne', Real.log_exp]

theorem subexponentialUnionLog_pos {n p : ℕ} (hn : 1 ≤ n) (hp : 1 ≤ p) :
    0 < subexponentialUnionLog n p := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  apply Real.log_pos
  have hnp : (1 : ℝ) ≤ (n : ℝ) * (p : ℝ) :=
    one_le_mul_of_one_le_of_one_le hnR hpR
  nlinarith

theorem subexponentialUnionLog_le {n p : ℕ} (hn : 1 ≤ n) (hp : 1 ≤ p) :
    subexponentialUnionLog n p ≤ 3 * dimensionLog n * dimensionLog p := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hl : 1 ≤ dimensionLog n := log_exp_mul_nat_ge_one hn
  have hL : 1 ≤ dimensionLog p := log_exp_mul_nat_ge_one hp
  have hln : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hlp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp)
  have hfour : Real.log (4 : ℝ) ≤ 3 := by
    simpa using Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
  have heq : subexponentialUnionLog n p =
      Real.log (4 : ℝ) + Real.log (n : ℝ) + Real.log (p : ℝ) := by
    rw [subexponentialUnionLog,
      Real.log_mul (mul_ne_zero (by norm_num) hnR.ne') hpR.ne',
      Real.log_mul (by norm_num) hnR.ne']
  have hc := mul_nonneg (sub_nonneg.mpr hl) (sub_nonneg.mpr hL)
  have hprod : 1 ≤ dimensionLog n * dimensionLog p :=
    one_le_mul_of_one_le_of_one_le hl hL
  rw [heq, dimensionLog_eq_one_add_log hn, dimensionLog_eq_one_add_log hp] at *
  nlinarith

theorem subexponentialTailFactor_nonneg (n : ℕ) :
    0 ≤ subexponentialTailFactor n := Real.exp_nonneg _

theorem subexponentialResidualSD_nonneg {n : ℕ} {K : ℝ} (hK : 0 ≤ K) :
    0 ≤ subexponentialResidualSD n K := by
  unfold subexponentialResidualSD subexponentialTailFactor
  positivity

theorem subexponentialResidualRadius_nonneg {n p : ℕ} {K : ℝ}
    (hn : 1 ≤ n) (hp : 1 ≤ p) (hK : 0 ≤ K) :
    0 ≤ subexponentialResidualRadius n p K := by
  have hs : 0 ≤ subexponentialUnionLog n p := (subexponentialUnionLog_pos hn hp).le
  unfold subexponentialResidualRadius subexponentialTailFactor
  positivity

theorem subexponentialGaussianRadius_nonneg {n p : ℕ} {K : ℝ} (hK : 0 ≤ K) :
    0 ≤ subexponentialGaussianRadius n p K :=
  mul_nonneg (subexponentialResidualSD_nonneg hK) (Real.sqrt_nonneg _)

theorem subexponentialTailFactor_le_inv_two_mul {n : ℕ} (hn : 1 ≤ n) :
    subexponentialTailFactor n ≤ 1 / (2 * (n : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hl : 0 ≤ dimensionLog n := zero_le_one.trans (log_exp_mul_nat_ge_one hn)
  have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hden : 2 * (n : ℝ) ≤ Real.exp (2 * dimensionLog n) := by
    calc
      _ ≤ Real.exp 1 * (n : ℝ) := mul_le_mul_of_nonneg_right he hnR.le
      _ = Real.exp (dimensionLog n) :=
        (Real.exp_log (mul_pos (Real.exp_pos _) hnR)).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  unfold subexponentialTailFactor
  rw [show -2 * dimensionLog n = -(2 * dimensionLog n) by ring, Real.exp_neg]
  simpa only [one_div] using
    one_div_le_one_div_of_le (mul_pos (by norm_num) hnR) hden

theorem sqrt_nat_le_nat {n : ℕ} (hn : 1 ≤ n) :
    Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  apply Real.sqrt_le_iff.mpr
  exact ⟨by positivity, by
    nlinarith [mul_nonneg (sub_nonneg.mpr hnR) (show (0 : ℝ) ≤ n by positivity)]⟩

theorem subexponentialTailFactor_le_inv_sqrt {n : ℕ} (hn : 1 ≤ n) :
    subexponentialTailFactor n ≤ 1 / Real.sqrt (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsn := sqrt_nat_le_nat hn
  exact (subexponentialTailFactor_le_inv_two_mul hn).trans
    (one_div_le_one_div_of_le (Real.sqrt_pos.mpr hnR) (by linarith))

theorem quotient_le_subexponentialScale {n : ℕ} {K : ℝ}
    (hn : 1 ≤ n) (hK : 0 ≤ K) : K / (n : ℝ) ≤ subexponentialScale n K := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hl : 1 ≤ dimensionLog n := log_exp_mul_nat_ge_one hn
  unfold subexponentialScale
  calc
    _ ≤ K / Real.sqrt (n : ℝ) :=
      div_le_div_of_nonneg_left hK (Real.sqrt_pos.mpr hnR) (sqrt_nat_le_nat hn)
    _ ≤ _ := div_le_div_of_nonneg_right (le_mul_of_one_le_right hK hl) (Real.sqrt_nonneg _)

theorem subexponentialResidualSD_le_scale {n : ℕ} {K : ℝ}
    (hn : 1 ≤ n) (hK : 0 ≤ K) :
    subexponentialResidualSD n K ≤ subexponentialScale n K := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have ht := mul_le_mul_of_nonneg_left (subexponentialTailFactor_le_inv_two_mul hn)
    (show 0 ≤ 2 * K by positivity)
  have heq : (2 * K) * (1 / (2 * (n : ℝ))) = K / (n : ℝ) := by
    field_simp [hnR.ne'] <;> ring
  exact ht.trans (heq.symm ▸ quotient_le_subexponentialScale hn hK)

theorem subexponentialResidualSD_le_half {n : ℕ} {K : ℝ}
    (hn : 1 ≤ n) (hK : 0 ≤ K) (hb : subexponentialScale n K < 1 / 16) :
    subexponentialResidualSD n K ≤ 1 / 2 := by
  have h := subexponentialResidualSD_le_scale hn hK
  linarith

theorem four_mul_subexponentialResidualSD_lt_half_gap {n : ℕ} {K c₀ : ℝ}
    (hn : 1 ≤ n) (hK : 0 ≤ K) (hb : subexponentialScale n K < c₀ / 8) :
    4 * subexponentialResidualSD n K < c₀ / 2 := by
  have h := subexponentialResidualSD_le_scale hn hK
  linarith

theorem subexponential_radii_le {n p : ℕ} {K : ℝ}
    (hn : 1 ≤ n) (hp : 1 ≤ p) (hK : 0 ≤ K) :
    subexponentialResidualRadius n p K + subexponentialGaussianRadius n p K ≤
      58 * subexponentialScale n K * dimensionLog p := by
  let s := subexponentialUnionLog n p
  let w := K / Real.sqrt (n : ℝ)
  have hw : 0 ≤ w := div_nonneg hK (Real.sqrt_nonneg _)
  have hs : 0 ≤ s := (subexponentialUnionLog_pos hn hp).le
  have hsqrt : Real.sqrt s ≤ s + 1 := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by linarith, by nlinarith [sq_nonneg s]⟩
  have hsqrt2 : Real.sqrt (2 * s) ≤ 2 * s + 1 := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by linarith, by nlinarith [sq_nonneg s]⟩
  have ht : K * subexponentialTailFactor n ≤ w := by
    exact (mul_le_mul_of_nonneg_left (subexponentialTailFactor_le_inv_sqrt hn) hK).trans_eq
      (by dsimp [w]; ring)
  have hfirst : 8 * K * subexponentialTailFactor n * Real.sqrt s ≤ 8 * w * (s + 1) := by
    calc
      _ = 8 * (K * subexponentialTailFactor n) * Real.sqrt s := by ring
      _ ≤ 8 * w * Real.sqrt s :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht (by norm_num))
          (Real.sqrt_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hsqrt (by positivity)
  have hsecond : subexponentialResidualSD n K * Real.sqrt (2 * s) ≤
      2 * w * (2 * s + 1) := by
    calc
      _ = 2 * (K * subexponentialTailFactor n) * Real.sqrt (2 * s) := by
        unfold subexponentialResidualSD
        ring
      _ ≤ 2 * w * Real.sqrt (2 * s) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht (by norm_num))
          (Real.sqrt_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hsqrt2 (by positivity)
  have hrad : subexponentialResidualRadius n p K + subexponentialGaussianRadius n p K ≤
      w * (16 * s + 10) := by
    unfold subexponentialResidualRadius subexponentialGaussianRadius
    change 8 * K * subexponentialTailFactor n * Real.sqrt s +
      4 * K * s / Real.sqrt (n : ℝ) +
      subexponentialResidualSD n K * Real.sqrt (2 * s) ≤ _
    have heq : 4 * K * s / Real.sqrt (n : ℝ) = 4 * w * s := by dsimp [w]; ring
    rw [heq]
    nlinarith [hfirst, hsecond]
  have hlog : s ≤ 3 * dimensionLog n * dimensionLog p := subexponentialUnionLog_le hn hp
  have hprod : 1 ≤ dimensionLog n * dimensionLog p :=
    one_le_mul_of_one_le_of_one_le (log_exp_mul_nat_ge_one hn) (log_exp_mul_nat_ge_one hp)
  have hin : 16 * s + 10 ≤ 58 * dimensionLog n * dimensionLog p := by nlinarith
  exact hrad.trans ((mul_le_mul_of_nonneg_left hin hw).trans_eq (by
    dsimp [w, subexponentialScale]
    ring))

theorem reciprocal_n_le_subexponential_base {n p : ℕ} {K : ℝ}
    (hn : 1 ≤ n) (hp : 1 ≤ p) (hK : 1 ≤ K) :
    1 / (n : ℝ) ≤ subexponentialScale n K * dimensionLog p ^ (3 / 2 : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hb : 0 ≤ subexponentialScale n K := (subexponentialScale_pos hn hK).le
  have hL : 1 ≤ dimensionLog p := log_exp_mul_nat_ge_one hp
  have hLp : 0 < dimensionLog p := zero_lt_one.trans_le hL
  have hpow : 1 ≤ dimensionLog p ^ (3 / 2 : ℝ) := by
    rw [rpow_three_halves_eq_mul_sqrt hLp]
    exact one_le_mul_of_one_le_of_one_le hL (Real.one_le_sqrt.mpr hL)
  calc
    _ ≤ K / (n : ℝ) := div_le_div_of_nonneg_right hK hnR.le
    _ ≤ subexponentialScale n K := quotient_le_subexponentialScale hn (zero_le_one.trans hK)
    _ ≤ _ := le_mul_of_one_le_right hb hpow

/-- The two coupling radii and exceptional probability have the same
baseline order as the bounded comparison. -/
theorem subexponential_transfer_error_le {n p : ℕ} {K : ℝ}
    (hn : 1 ≤ n) (hp : 1 ≤ p) (hK : 1 ≤ K) :
    (subexponentialResidualRadius n p K + subexponentialGaussianRadius n p K) *
        Real.sqrt (dimensionLog p) + 1 / (n : ℝ) ≤
      100 * subexponentialScale n K * dimensionLog p ^ (3 / 2 : ℝ) := by
  have hL : 0 < dimensionLog p := zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp)
  have hrad := mul_le_mul_of_nonneg_right
    (subexponential_radii_le hn hp (zero_le_one.trans hK)) (Real.sqrt_nonneg (dimensionLog p))
  have hrad' : (subexponentialResidualRadius n p K + subexponentialGaussianRadius n p K) *
      Real.sqrt (dimensionLog p) ≤
      58 * subexponentialScale n K * dimensionLog p ^ (3 / 2 : ℝ) := by
    calc
      _ ≤ (58 * subexponentialScale n K * dimensionLog p) *
          Real.sqrt (dimensionLog p) := hrad
      _ = _ := by rw [rpow_three_halves_eq_mul_sqrt hL]; ring
  have hprob := reciprocal_n_le_subexponential_base hn hp hK
  have hb : 0 ≤ subexponentialScale n K * dimensionLog p ^ (3 / 2 : ℝ) :=
    mul_nonneg (subexponentialScale_pos hn hK).le (Real.rpow_nonneg hL.le _)
  nlinarith [hrad']

/-- The same bound with any rectangle concentration constant at least one. -/
theorem subexponential_transfer_error_weighted_le {n p : ℕ} {K C : ℝ}
    (hn : 1 ≤ n) (hp : 1 ≤ p) (hK : 1 ≤ K) (hC : 1 ≤ C) :
    C * (subexponentialResidualRadius n p K + subexponentialGaussianRadius n p K) *
        Real.sqrt (dimensionLog p) + 1 / (n : ℝ) ≤
      (100 * C) * subexponentialScale n K * dimensionLog p ^ (3 / 2 : ℝ) := by
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hprob : 1 / (n : ℝ) ≤ C * (1 / (n : ℝ)) :=
    le_mul_of_one_le_left (by positivity) hC
  calc
    _ ≤ C * ((subexponentialResidualRadius n p K + subexponentialGaussianRadius n p K) *
        Real.sqrt (dimensionLog p) + 1 / (n : ℝ)) := by nlinarith
    _ ≤ C * (100 * subexponentialScale n K * dimensionLog p ^ (3 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left (subexponential_transfer_error_le hn hp hK) hC0
    _ = _ := by ring

end
end RectangleCLT.Companion
