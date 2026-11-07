import RectangleCLTCompanion.NormalQuantileRate

/-! Numeric calibration limits for the common symmetric lower family. -/
open Filter
open scoped Topology
namespace RectangleCLT.Companion.SplitV4
noncomputable section

variable {ell : ℕ → ℝ}

theorem tendsto_lower_ell_div_n (hEll : Tendsto ell atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => ell n^3/(n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => ell n/(n : ℝ)) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsmall
  · filter_upwards [hEll.eventually (eventually_ge_atTop 1)] with n hn
    exact div_nonneg (by linarith) (Nat.cast_nonneg n)
  · filter_upwards [hEll.eventually (eventually_ge_atTop 1)] with n hn
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    nlinarith [sq_nonneg (ell n-1), mul_nonneg (by linarith : 0 ≤ ell n) (by nlinarith [sq_nonneg (ell n-1)] : 0 ≤ (ell n)^2-1)]

theorem tendsto_lower_sqrt_ell_div_sqrt_n (hEll : Tendsto ell atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => ell n^3/(n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => Real.sqrt (ell n)/Real.sqrt (n : ℝ)) atTop (𝓝 0) := by
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp (tendsto_lower_ell_div_n hEll hsmall)
  simp only [Real.sqrt_zero] at hh
  apply hh.congr'
  filter_upwards [hEll.eventually (eventually_ge_atTop 0)] with n hn
  dsimp only [Function.comp_apply]
  rw [Real.sqrt_div hn]

theorem tendsto_lower_activation_probability (hEll : Tendsto ell atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => ell n^3/(n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => ell n/(2*(n : ℝ))) atTop (𝓝 0) := by
  have hh := (tendsto_lower_ell_div_n hEll hsmall).div_const 2
  simpa only [div_div, mul_comm, zero_div] using hh

private theorem rpow_three_halves {x : ℝ} (hx : 0 < x) :
    x^(3/2 : ℝ) = x*Real.sqrt x := by
  rw [show (3/2 : ℝ) = 1+1/2 by norm_num, Real.rpow_add hx, Real.rpow_one, Real.sqrt_eq_rpow]

private theorem lower_remainder_ratio_identity {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (Real.sqrt x/Real.sqrt y+x^2/y)/(x^(3/2 : ℝ)/Real.sqrt y) = 1/x+Real.sqrt x/Real.sqrt y := by
  have hsx : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hx)
  have hsy : Real.sqrt y ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hy)
  rw [rpow_three_halves hx, add_div]
  have h₁ : (Real.sqrt x/Real.sqrt y)/(x*Real.sqrt x/Real.sqrt y) = 1/x := by field_simp; ring
  rw [h₁]
  congr 1
  apply (div_eq_iff (div_ne_zero (mul_ne_zero (ne_of_gt hx) hsx) hsy)).mpr
  calc
    x^2/y = x*(Real.sqrt x)^2/(Real.sqrt y)^2 := by rw [Real.sq_sqrt hx.le, Real.sq_sqrt hy.le]; ring
    _ = (Real.sqrt x/Real.sqrt y)*(x*Real.sqrt x/Real.sqrt y) := by ring

theorem tendsto_lower_comparison_remainder_div_rate (hEll : Tendsto ell atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => ell n^3/(n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (Real.sqrt (ell n)/Real.sqrt (n : ℝ)+(ell n)^2/(n : ℝ)) /
      ((ell n)^(3/2 : ℝ)/Real.sqrt (n : ℝ))) atTop (𝓝 0) := by
  have hh := ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop hEll).add (tendsto_lower_sqrt_ell_div_sqrt_n hEll hsmall)
  have hh' : Tendsto (fun n : ℕ => 1/ell n+Real.sqrt (ell n)/Real.sqrt (n : ℝ)) atTop (𝓝 0) := by
    simpa using hh
  apply hh'.congr'
  filter_upwards [hEll.eventually (eventually_gt_atTop (0 : ℝ)), eventually_ge_atTop 1] with n hn hn1
  exact (lower_remainder_ratio_identity hn (by exact_mod_cast (show 0 < n by omega))).symm

private theorem lower_rate_conversion_identity {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    ((2/Real.sqrt y)*(1+2*x)^(3/2 : ℝ))/(x^(3/2 : ℝ)/(2*Real.sqrt y)) =
      4*((1+2*x)/x)^(3/2 : ℝ) := by
  rw [Real.div_rpow (by linarith : 0 ≤ 1+2*x) hx.le]
  field_simp [ne_of_gt (Real.sqrt_pos.mpr hy), ne_of_gt (Real.rpow_pos_of_pos hx (3/2 : ℝ))]
  ring

/-- Exact conversion from the construction's shift scale to the normalized
bounded-observation rate. -/
theorem tendsto_lower_bounded_rate_conversion (hEll : Tendsto ell atTop atTop) :
    Tendsto (fun n : ℕ => ((2/Real.sqrt (n : ℝ))*(1+2*ell n)^(3/2 : ℝ)) /
      ((ell n)^(3/2 : ℝ)/(2*Real.sqrt (n : ℝ)))) atTop (𝓝 ((2 : ℝ)^(7/2 : ℝ))) := by
  have hbase : Tendsto (fun n : ℕ => (1+2*ell n)/ell n) atTop (𝓝 (2 : ℝ)) := by
    have hh := ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop hEll).const_add 2
    simp only [add_zero] at hh
    apply hh.congr'
    filter_upwards [hEll.eventually (eventually_gt_atTop (0 : ℝ))] with n hn
    field_simp [ne_of_gt hn]
    ring
  have hh := (hbase.rpow_const (p := (3/2 : ℝ)) (Or.inl (by norm_num : (2 : ℝ) ≠ 0))).const_mul 4
  have he : (4 : ℝ)*(2 : ℝ)^(3/2 : ℝ) = (2 : ℝ)^(7/2 : ℝ) := by
    rw [show (7/2 : ℝ) = 2+3/2 by norm_num, Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_two]
    norm_num
  rw [he] at hh
  apply hh.congr'
  filter_upwards [hEll.eventually (eventually_gt_atTop (0 : ℝ)), eventually_ge_atTop 1] with n hn hn1
  exact (lower_rate_conversion_identity hn (by exact_mod_cast (show 0 < n by omega))).symm

private theorem lower_signal_eq_sqrt {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    x^(3/2 : ℝ)/Real.sqrt y = Real.sqrt (x^3/y) := by
  rw [Real.sqrt_div (pow_nonneg hx.le 3), rpow_three_halves hx]
  congr 1
  symm
  apply (Real.sqrt_eq_iff_eq_sq (pow_nonneg hx.le 3) (mul_nonneg hx.le (Real.sqrt_nonneg _))).2
  rw [mul_pow, Real.sq_sqrt hx.le]
  ring

theorem tendsto_lower_signal_rate (hEll : Tendsto ell atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => ell n^3/(n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (ell n)^(3/2 : ℝ)/Real.sqrt (n : ℝ)) atTop (𝓝 0) := by
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hsmall
  simp only [Real.sqrt_zero] at hh
  apply hh.congr'
  filter_upwards [hEll.eventually (eventually_gt_atTop (0 : ℝ)), eventually_ge_atTop 1] with n hn hn1
  exact (lower_signal_eq_sqrt hn (by exact_mod_cast (show 0 < n by omega))).symm

theorem tendsto_lower_shift_remainder_div_rate (hEll : Tendsto ell atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => ell n^3/(n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => ((ell n)^3/(n : ℝ))/
      ((ell n)^(3/2 : ℝ)/Real.sqrt (n : ℝ))) atTop (𝓝 0) := by
  apply (tendsto_lower_signal_rate hEll hsmall).congr'
  filter_upwards [hEll.eventually (eventually_gt_atTop (0 : ℝ)), eventually_ge_atTop 1] with n hn hn1
  have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [lower_signal_eq_sqrt hn hnp]
  have hp : 0 < (ell n)^3/(n : ℝ) := div_pos (pow_pos hn 3) hnp
  have hh := Real.sq_sqrt hp.le
  have hs : Real.sqrt ((ell n)^3/(n : ℝ)) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hp)
  apply (eq_div_iff hs).mpr
  nlinarith

end
end RectangleCLT.Companion.SplitV4
