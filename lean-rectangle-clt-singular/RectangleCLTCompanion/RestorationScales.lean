import RectangleCLTCompanion.RestorationFourthBound

/-! Explicit scalar constants for translated restoration.  A fixed linear
bandwidth condition makes the exact convergent-series factor universal. -/

namespace RectangleCLT.Companion

noncomputable section
set_option autoImplicit false

variable {p : ℕ}

def restorationBandwidthConstant (C : ℝ) : ℝ :=
  1 / Real.log (1 + 1 / (2 * C))

theorem restorationBandwidthConstant_pos {C : ℝ} (hC : 1 ≤ C) :
    0 < restorationBandwidthConstant C := by
  have hc : 0 < C := lt_of_lt_of_le (by norm_num) hC
  have hp : 0 < 1 / (2 * C) := by positivity
  exact one_div_pos.mpr (Real.log_pos (by linarith))

theorem restoration_small_of_bandwidth
    (s : FaceSmoother p) {C R : ℝ} (hC : 1 ≤ C) (_hR : 0 ≤ R)
    (hband : restorationBandwidthConstant C * R ≤ s.bandwidth) :
    C * (Real.exp (R / s.bandwidth) - 1) ≤ 1 / 2 := by
  have hc : 0 < C := lt_of_lt_of_le (by norm_num) hC
  have hp : 0 < 1 / (2 * C) := by positivity
  have hlog : 0 < Real.log (1 + 1 / (2 * C)) := Real.log_pos (by linarith)
  have hr : R / Real.log (1 + 1 / (2 * C)) ≤ s.bandwidth := by
    have heq : restorationBandwidthConstant C * R = R / Real.log (1 + 1 / (2 * C)) := by
      unfold restorationBandwidthConstant
      ring
    rwa [heq] at hband
  have hr' := (div_le_iff₀ hlog).mp hr
  have harg : R / s.bandwidth ≤ Real.log (1 + 1 / (2 * C)) :=
    (div_le_iff₀ s.bandwidth_pos).mpr (by simpa only [mul_comm] using hr')
  have he := Real.exp_le_exp.mpr harg
  rw [Real.exp_log (by positivity : 0 < 1 + 1 / (2 * C))] at he
  calc
    _ ≤ C * (1 / (2 * C)) := mul_le_mul_of_nonneg_left (by linarith) hc.le
    _ = _ := by field_simp; ring

theorem restorationSelectorCap_le
    (s : FaceSmoother p) {b K R C T : ℝ}
    (hb : 0 ≤ b) (hK : 0 ≤ K) (hR : 0 ≤ R) (hC : 1 ≤ C) (hT : 0 ≤ T)
    (hsmall : C * (Real.exp (R / s.bandwidth) - 1) ≤ 1 / 2) (k : ℕ) :
    restorationSelectorCap s b K R C T k ≤
      (b * K * C ^ (k + 1) * T) * (3 / 2 : ℝ) ^ k * 2 ^ (k + 1) := by
  let η := Real.exp (R / s.bandwidth) - 1
  have hη : 0 ≤ η := sub_nonneg.mpr
    (Real.one_le_exp_iff.mpr (div_nonneg hR s.bandwidth_pos.le))
  have hηhalf : η ≤ 1 / 2 := (le_mul_of_one_le_left hη hC).trans hsmall
  have he : Real.exp (R / s.bandwidth) ≤ (3 / 2 : ℝ) := by
    dsimp only [η] at hηhalf
    linarith
  have hep : Real.exp ((k : ℝ) * R / s.bandwidth) ≤ (3 / 2 : ℝ) ^ k := by
    rw [show (k : ℝ) * R / s.bandwidth = (k : ℝ) * (R / s.bandwidth) by ring,
      Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos _).le he k
  have hden : (1 / 2 : ℝ) ≤ 1 - C * η := by dsimp only [η]; linarith
  have hdenp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hden (k + 1)
  have hc : 0 ≤ C := (by norm_num : (0 : ℝ) ≤ 1).trans hC
  have hbK : 0 ≤ b * K * C ^ (k + 1) * T := by positivity
  unfold restorationSelectorCap
  calc
    _ = ((b * K * C ^ (k + 1) * T) * Real.exp ((k : ℝ) * R / s.bandwidth)) /
        (1 - C * η) ^ (k + 1) := by dsimp only [η]; ring
    _ ≤ ((b * K * C ^ (k + 1) * T) * (3 / 2 : ℝ) ^ k) /
        (1 / 2 : ℝ) ^ (k + 1) :=
      div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hep hbK)
        (by positivity) hdenp
    _ = _ := by
      have hd : (1 / 2 : ℝ) ^ (k + 1) = 1 / (2 : ℝ) ^ (k + 1) := by rw [div_pow, one_pow]
      rw [hd, div_div_eq_mul_div, div_one]

theorem two_restorationSelectorCaps_le
    (s : FaceSmoother p) {b K R C T : ℝ}
    (hb : 0 ≤ b) (hK : 0 ≤ K) (hR : 0 ≤ R) (hC : 1 ≤ C) (hT : 0 ≤ T)
    (hsmall : C * (Real.exp (R / s.bandwidth) - 1) ≤ 1 / 2) :
    2 * restorationSelectorCap s b K R C T 2 + restorationSelectorCap s b K R C T 1 ≤
      42 * b * K * C ^ 3 * T := by
  have h1 := restorationSelectorCap_le s hb hK hR hC hT hsmall 1
  have h2 := restorationSelectorCap_le s hb hK hR hC hT hsmall 2
  norm_num at h1 h2
  have hc : 0 ≤ C := (by norm_num : (0 : ℝ) ≤ 1).trans hC
  have hCpow : C ^ 2 ≤ C ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg C) (sub_nonneg.mpr hC)]
  have hBT : 0 ≤ b * K * T := by positivity
  have hprod := mul_le_mul_of_nonneg_left hCpow hBT
  nlinarith

end
end RectangleCLT.Companion
