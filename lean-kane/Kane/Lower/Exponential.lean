import Kane.Cube
import Mathlib.Algebra.Order.Ring.Pow

/-! Elementary exponential estimates for the lower-bound construction. -/

open scoped BigOperators

namespace Kane.Lower

theorem one_add_half_sq_le_cosh (t : ℝ) : 1 + t ^ 2 / 2 ≤ Real.cosh t := by
  have h := (Real.hasSum_cosh t).summable.sum_le_tsum (Finset.range 2)
    (fun i _ => div_nonneg (by rw [pow_mul]; positivity) (by positivity))
  rw [← Real.cosh_eq_tsum] at h
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  exact h

theorem quarter_sq_le_log_cosh (t : ℝ) (ht : t ^ 2 ≤ 1) :
    t ^ 2 / 4 ≤ Real.log (Real.cosh t) := by
  have hpos : 0 < 1 + t ^ 2 / 2 := by positivity
  have hlog := Real.one_sub_inv_le_log_of_pos hpos
  have hmono := Real.log_le_log hpos (one_add_half_sq_le_cosh t)
  have halg : t ^ 2 / 4 ≤ 1 - (1 + t ^ 2 / 2)⁻¹ := by
    have heq : 1 - (1 + t ^ 2 / 2)⁻¹ = (t ^ 2 / 2) / (1 + t ^ 2 / 2) := by
      field_simp
    rw [heq]
    apply (le_div_iff₀ hpos).mpr
    nlinarith [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr ht)]
  exact halg.trans (hlog.trans hmono)

theorem one_add_n_half_sq_le_cosh_pow (n : ℕ) (t : ℝ) :
    1 + (n : ℝ) * t ^ 2 / 2 ≤ Real.cosh t ^ n := by
  calc
    _ = 1 + (n : ℝ) * (t ^ 2 / 2) := by ring
    _ ≤ (1 + t ^ 2 / 2) ^ n :=
      one_add_mul_le_pow (by nlinarith [sq_nonneg t]) n
    _ ≤ Real.cosh t ^ n :=
      pow_le_pow_left₀ (by positivity) (one_add_half_sq_le_cosh t) n

noncomputable def largeTilt (n : ℕ) (L : ℝ) : ℝ :=
  Real.sqrt (L / (8 * (n : ℝ)))

noncomputable def tiltThreshold (n : ℕ) (t : ℝ) : ℝ :=
  ((n : ℝ) * Real.log (Real.cosh t) - Real.log 2) / t

theorem largeTilt_pos {n : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 < L) :
    0 < largeTilt n L := by
  unfold largeTilt
  apply Real.sqrt_pos.mpr
  positivity

theorem largeTilt_sq {n : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 ≤ L) :
    (largeTilt n L) ^ 2 = L / (8 * (n : ℝ)) := by
  unfold largeTilt
  apply Real.sq_sqrt
  positivity

theorem largeTilt_normalized {n : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 ≤ L) :
    (n : ℝ) * (largeTilt n L) ^ 2 = L / 8 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [largeTilt_sq hn hL]
  field_simp
  ring

theorem largeTilt_sq_le_one {n : ℕ} (hn : 0 < n) {L : ℝ}
    (hL : 0 ≤ L) (hLn : L ≤ (n : ℝ)) : (largeTilt n L) ^ 2 ≤ 1 := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [largeTilt_sq hn hL]
  apply (div_le_iff₀ (by positivity : 0 < 8 * (n : ℝ))).mpr
  linarith

/-- The tilted halfspace has a threshold of order `sqrt (n * L)`. The
constant is deliberately weakened to keep the later amplification simple. -/
theorem largeTilt_threshold_lower {n : ℕ} (hn : 0 < n) {L : ℝ}
    (hL : 64 ≤ L) (hLn : L ≤ (n : ℝ)) :
    Real.sqrt ((n : ℝ) * L) / 64 ≤ tiltThreshold n (largeTilt n L) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hLpos : 0 < L := by linarith
  have ht := largeTilt_pos hn hLpos
  have hnorm := largeTilt_normalized hn hLpos.le
  have hcosh := quarter_sq_le_log_cosh _ (largeTilt_sq_le_one hn hLpos.le hLn)
  have hlogtwo : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hnum : L / 64 ≤ (n : ℝ) * Real.log (Real.cosh (largeTilt n L)) - Real.log 2 := by
    have hscaled := mul_le_mul_of_nonneg_left hcosh hn'.le
    nlinarith
  have hroot : Real.sqrt ((n : ℝ) * L) ≤ 8 * (n : ℝ) * largeTilt n L := by
    apply (Real.sqrt_le_left (by positivity : 0 ≤ 8 * (n : ℝ) * largeTilt n L)).mpr
    have hscaled := congrArg (fun x : ℝ => (n : ℝ) * x) hnorm
    nlinarith [mul_nonneg hn'.le hLpos.le]
  have halg : (L / 64) / largeTilt n L = (8 * (n : ℝ) * largeTilt n L) / 64 := by
    apply (div_eq_iff ht.ne').mpr
    nlinarith [hnorm]
  calc
    _ ≤ (8 * (n : ℝ) * largeTilt n L) / 64 := by gcongr
    _ = (L / 64) / largeTilt n L := halg.symm
    _ ≤ tiltThreshold n (largeTilt n L) := by
      exact div_le_div_of_nonneg_right hnum ht.le

/-- The exponential Paley--Zygmund probability is at least `exp (-L)` in
the large-logarithm regime. -/
theorem largeTilt_probability_lower {n : ℕ} (hn : 0 < n) {L : ℝ}
    (hL : 64 ≤ L) :
    Real.exp (-L) ≤ Real.exp (-2 * (n : ℝ) * (largeTilt n L) ^ 2) / 4 := by
  have hnorm := largeTilt_normalized hn (show 0 ≤ L by linarith)
  have hfour : (4 : ℝ) ≤ Real.exp (3 * L / 4) := by
    have h := Real.add_one_le_exp (3 * L / 4)
    linarith
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
  calc
    Real.exp (-L) * 4 ≤ Real.exp (-L) * Real.exp (3 * L / 4) :=
      mul_le_mul_of_nonneg_left hfour (Real.exp_nonneg _)
    _ = Real.exp (-2 * (n : ℝ) * (largeTilt n L) ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      nlinarith

noncomputable def smallTilt (n : ℕ) : ℝ := 1 / Real.sqrt (n : ℝ)

theorem smallTilt_pos {n : ℕ} (hn : 0 < n) : 0 < smallTilt n := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  unfold smallTilt
  positivity

theorem smallTilt_normalized {n : ℕ} (hn : 0 < n) :
    (n : ℝ) * (smallTilt n) ^ 2 = 1 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold smallTilt
  rw [div_pow, one_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  exact mul_one_div_cancel hn'

theorem smallTilt_mean_lower {n : ℕ} (hn : 0 < n) :
    (3 / 2 : ℝ) ≤ Real.cosh (smallTilt n) ^ n := by
  have h := one_add_n_half_sq_le_cosh_pow n (smallTilt n)
  rw [smallTilt_normalized hn] at h
  norm_num at h ⊢
  exact h

theorem log_nine_eighths_pos : 0 < Real.log (9 / 8 : ℝ) :=
  Real.log_pos (by norm_num)

/-- A fixed positive multiple of `sqrt n` lies below the threshold of the
three-quarter Paley--Zygmund event. -/
theorem smallTilt_threshold_lower {n : ℕ} (hn : 0 < n) :
    Real.log (9 / 8 : ℝ) * Real.sqrt (n : ℝ) ≤
      Real.log ((3 / 4 : ℝ) * Real.cosh (smallTilt n) ^ n) / smallTilt n := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have ht := smallTilt_pos hn
  have hlevel : (9 / 8 : ℝ) ≤ (3 / 4 : ℝ) * Real.cosh (smallTilt n) ^ n := by
    nlinarith [smallTilt_mean_lower hn]
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 9 / 8) hlevel
  have halg : Real.log (9 / 8 : ℝ) * Real.sqrt (n : ℝ) =
      Real.log (9 / 8 : ℝ) / smallTilt n := by
    unfold smallTilt
    field_simp
  rw [halg]
  exact div_le_div_of_nonneg_right hlog ht.le

theorem smallTilt_probability_eq {n : ℕ} (hn : 0 < n) :
    Real.exp (-2 * (n : ℝ) * (smallTilt n) ^ 2) / 16 = Real.exp (-2) / 16 := by
  congr 2
  nlinarith [smallTilt_normalized hn]

end Kane.Lower
