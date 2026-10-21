import RectangleCLT.GlobalDerivativeIntegration

/-! Scalar conversions for the genuine full-dual moment estimates. -/

open Set

namespace RectangleCLT

theorem global_gaussian_boundary_scale_le {ν L v C : ℝ} {q : ℕ}
    (hν : 0 ≤ ν) (hL : 0 < L) (hv : 0 < v) (hC : 0 ≤ C) (hq : q ≤ 4) :
    C * ((q : ℝ) * (Real.sqrt ν / (4 * Real.sqrt L))) * Real.sqrt (L / v) ≤
      C * Real.sqrt ν / Real.sqrt v := by
  have hLs := Real.sqrt_pos.mpr hL
  have hvs := Real.sqrt_pos.mpr hv
  have hqR : (q : ℝ) ≤ 4 := by exact_mod_cast hq
  rw [Real.sqrt_div hL.le]
  apply (le_div_iff₀ hvs).mpr
  rw [mul_assoc, div_mul_cancel₀ _ hvs.ne']
  have he : (q : ℝ) * (Real.sqrt ν / (4 * Real.sqrt L)) * Real.sqrt L =
      (q : ℝ) * Real.sqrt ν / 4 := by field_simp; ring
  calc
    _ = C * ((q : ℝ) * (Real.sqrt ν / (4 * Real.sqrt L)) * Real.sqrt L) := by ring
    _ = C * ((q : ℝ) * Real.sqrt ν / 4) := by rw [he]
    _ ≤ C * Real.sqrt ν := mul_le_mul_of_nonneg_left (by
      nlinarith [Real.sqrt_nonneg ν]) hC

theorem global_gaussian_half_boundary_scale_le {ν L C : ℝ} {q : ℕ}
    (hν : 0 ≤ ν) (hL : 0 < L) (hC : 0 ≤ C) (hq : q ≤ 4) :
    C * ((q : ℝ) * (Real.sqrt (ν / 2) / (4 * Real.sqrt L))) *
        Real.sqrt (L / (1 / 2)) ≤ C * Real.sqrt (ν / 2) * Real.sqrt 2 := by
  have hh := global_gaussian_boundary_scale_le (show 0 ≤ ν / 2 by positivity)
    hL (by norm_num : (0 : ℝ) < 1 / 2) hC hq
  have he : C * Real.sqrt (ν / 2) / Real.sqrt (1 / 2 : ℝ) =
      C * Real.sqrt (ν / 2) * Real.sqrt 2 := by
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1)]
    simp only [Real.sqrt_one]
    field_simp
  exact hh.trans_eq he

theorem global_early_boundary_scale_le
    {ν L h δ t C : ℝ} {q : ℕ}
    (hν : 0 < ν) (hL : 1 ≤ L) (hh : 0 < h) (hδ : 0 ≤ δ)
    (hband : 12 * δ ≤ h) (ht : 0 < t) (ht1 : t < 1)
    (hlarge : (1 / ν) * L * h ^ 2 ≤ t) (hC : 0 ≤ C) (hq : q ≤ 4) :
    C * ((q : ℝ) * (Real.sqrt ν / (4 * Real.sqrt L)) + 2 * δ / Real.sqrt t) *
        Real.sqrt (L / ((1 - t) / t)) ≤
      2 * C * Real.sqrt ν / Real.sqrt ((1 - t) / t) := by
  have hL0 : 0 < L := by linarith
  have hLs := Real.sqrt_pos.mpr hL0
  have hνs := Real.sqrt_pos.mpr hν
  have hts := Real.sqrt_pos.mpr ht
  have hvs : 0 < Real.sqrt ((1 - t) / t) := Real.sqrt_pos.mpr (div_pos (by linarith) ht)
  have hquad : L * h ^ 2 ≤ ν * t := by
    have hx := mul_le_mul_of_nonneg_left hlarge hν.le
    field_simp [hν.ne'] at hx
    nlinarith
  have hscale : h * Real.sqrt L ≤ Real.sqrt ν * Real.sqrt t := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    simpa only [mul_pow, Real.sq_sqrt hL0.le, Real.sq_sqrt hν.le,
      Real.sq_sqrt ht.le, mul_comm] using hquad
  have hδscale : 2 * δ * Real.sqrt L / Real.sqrt t ≤ Real.sqrt ν := by
    apply (div_le_iff₀ hts).mpr
    have hx : 2 * δ ≤ h := by linarith
    exact (mul_le_mul_of_nonneg_right hx hLs.le).trans hscale
  have hqR : (q : ℝ) ≤ 4 := by exact_mod_cast hq
  have hface : (q : ℝ) * (Real.sqrt ν / (4 * Real.sqrt L)) * Real.sqrt L ≤
      Real.sqrt ν := by
    have he : (q : ℝ) * (Real.sqrt ν / (4 * Real.sqrt L)) * Real.sqrt L =
        (q : ℝ) * Real.sqrt ν / 4 := by field_simp; ring
    rw [he]
    nlinarith
  rw [Real.sqrt_div hL0.le]
  apply (le_div_iff₀ hvs).mpr
  have he : C * ((q : ℝ) * (Real.sqrt ν / (4 * Real.sqrt L)) + 2 * δ / Real.sqrt t) *
      (Real.sqrt L / Real.sqrt ((1 - t) / t)) * Real.sqrt ((1 - t) / t) =
      C * ((q : ℝ) * (Real.sqrt ν / (4 * Real.sqrt L)) * Real.sqrt L +
        2 * δ * Real.sqrt L / Real.sqrt t) := by
    rw [mul_assoc, div_mul_cancel₀ _ hvs.ne']
    ring
  rw [he]
  exact (mul_le_mul_of_nonneg_left (add_le_add hface hδscale) hC).trans_eq (by ring)

theorem global_early_fourth_time_scale_le
    {A t : ℝ} (hA : 0 ≤ A) (ht : 0 < t) (ht2 : t ≤ 1 / 2) :
    (A / Real.sqrt ((1 - t) / t)) / t ^ 2 ≤
      2 * A * t ^ (-(3 / 2 : ℝ)) := by
  have ht1 : t < 1 := by linarith
  have htm : 0 < 1 - t := by linarith
  have hs := Real.sqrt_pos.mpr ht
  have hm := Real.sqrt_pos.mpr htm
  have hmhalf : (1 : ℝ) / 2 ≤ Real.sqrt (1 - t) := by
    have hh := Real.sq_sqrt htm.le
    nlinarith [Real.sqrt_nonneg (1 - t)]
  have hpow : t ^ (-(3 / 2 : ℝ)) = Real.sqrt t / t ^ 2 := by
    rw [show -(3 / 2 : ℝ) = (1 / 2 : ℝ) - 2 by norm_num,
      Real.rpow_sub ht, ← Real.sqrt_eq_rpow, Real.rpow_two]
  rw [hpow, Real.sqrt_div htm.le]
  have hinv : 1 / Real.sqrt (1 - t) ≤ 2 := by
    apply (div_le_iff₀ hm).mpr
    linarith
  calc
    _ = (1 / Real.sqrt (1 - t)) * (A * Real.sqrt t / t ^ 2) := by
      field_simp
    _ ≤ 2 * (A * Real.sqrt t / t ^ 2) :=
      mul_le_mul_of_nonneg_right hinv (by positivity)
    _ = _ := by ring

theorem global_half_boundary_scale {ν C : ℝ} (hν : 0 ≤ ν) :
    C * Real.sqrt (ν / 2) * Real.sqrt 2 = C * Real.sqrt ν := by
  rw [Real.sqrt_div hν]
  field_simp

theorem global_half_third_scale_le {ν C L : ℝ}
    (hν : 0 < ν) (hC : 0 ≤ C) (hL : 0 ≤ L) :
    608 * Real.exp 10 * (C * Real.sqrt (ν / 2) * Real.sqrt 2) *
        (Real.sqrt L) ^ 3 / (Real.sqrt (ν / 2)) ^ 3 ≤
      8192 * C * Real.exp 10 * (L * Real.sqrt L) / ν := by
  have hn := Real.sqrt_pos.mpr hν
  have hhalf := Real.sqrt_pos.mpr (show 0 < ν / 2 by positivity)
  have htwo : Real.sqrt (2 : ℝ) ≤ 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have hνsq := Real.sq_sqrt hν.le
  have hLsq := Real.sq_sqrt hL
  rw [global_half_boundary_scale hν.le]
  have he : 608 * Real.exp 10 * (C * Real.sqrt ν) * (Real.sqrt L) ^ 3 /
      (Real.sqrt (ν / 2)) ^ 3 =
      1216 * C * Real.exp 10 * (L * Real.sqrt L) / ν * Real.sqrt 2 := by
    rw [Real.sqrt_div hν.le]
    have htwoSq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hνcube : (Real.sqrt ν) ^ 3 = ν * Real.sqrt ν := by
      calc
        _ = (Real.sqrt ν) ^ 2 * Real.sqrt ν := by ring
        _ = _ := by rw [hνsq]
    have hLcube : (Real.sqrt L) ^ 3 = L * Real.sqrt L := by
      calc
        _ = (Real.sqrt L) ^ 2 * Real.sqrt L := by ring
        _ = _ := by rw [hLsq]
    have htwoCube : (Real.sqrt (2 : ℝ)) ^ 3 = 2 * Real.sqrt 2 := by
      calc
        _ = (Real.sqrt (2 : ℝ)) ^ 2 * Real.sqrt 2 := by ring
        _ = _ := by rw [htwoSq]
    rw [div_pow, hνcube, hLcube, htwoCube]
    field_simp
    <;> ring
  rw [he]
  have hx : 0 ≤ C * Real.exp 10 * (L * Real.sqrt L) / ν := by positivity
  calc
    _ = 1216 * (C * Real.exp 10 * (L * Real.sqrt L) / ν) * Real.sqrt 2 := by ring
    _ ≤ 1216 * (C * Real.exp 10 * (L * Real.sqrt L) / ν) * 2 :=
      mul_le_mul_of_nonneg_left htwo (by positivity)
    _ = 2432 * (C * Real.exp 10 * (L * Real.sqrt L) / ν) := by ring
    _ ≤ 8192 * (C * Real.exp 10 * (L * Real.sqrt L) / ν) :=
      mul_le_mul_of_nonneg_right (by norm_num) hx
    _ = _ := by ring

theorem global_half_fourth_scale_le {ν C L : ℝ}
    (hν : 0 < ν) (hC : 0 ≤ C) (hL : 0 ≤ L) :
    12672 * Real.exp 19 * (C * Real.sqrt (ν / 2) * Real.sqrt 2) *
        (Real.sqrt L) ^ 4 / (Real.sqrt (ν / 2)) ^ 4 ≤
      65536 * C * Real.exp 19 * (1 / Real.sqrt ν) ^ 3 * L ^ 2 := by
  have hn := Real.sqrt_pos.mpr hν
  rw [global_half_boundary_scale hν.le]
  have hh := Real.sq_sqrt (show 0 ≤ ν / 2 by positivity)
  have hνsq := Real.sq_sqrt hν.le
  have hLsq := Real.sq_sqrt hL
  have he : 12672 * Real.exp 19 * (C * Real.sqrt ν) * (Real.sqrt L) ^ 4 /
      (Real.sqrt (ν / 2)) ^ 4 =
      50688 * C * Real.exp 19 * (1 / Real.sqrt ν) ^ 3 * L ^ 2 := by
    rw [show (Real.sqrt (ν / 2)) ^ 4 = (ν / 2) ^ 2 by nlinarith only [hh],
      show (Real.sqrt L) ^ 4 = L ^ 2 by nlinarith only [hLsq]]
    have hνfour : (Real.sqrt ν) ^ 4 = ν ^ 2 := by
      calc
        _ = ((Real.sqrt ν) ^ 2) ^ 2 := by ring
        _ = _ := by rw [hνsq]
    field_simp
    ring_nf
    rw [hνfour]
    ring
  rw [he]
  have hx : 0 ≤ C * Real.exp 19 * (1 / Real.sqrt ν) ^ 3 * L ^ 2 := by positivity
  nlinarith

end RectangleCLT
