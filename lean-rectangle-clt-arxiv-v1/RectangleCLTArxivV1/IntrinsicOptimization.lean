import RectangleCLTArxivV1.IntrinsicInputs

/-!
# The smoothing-width optimization with the intrinsic coefficient retained

These are scalar estimates. Any hypothesis about an error at a small width
is explicitly an input of the scalar reduction, not a proved comparison of
probability laws. The final theorem must supply that estimate analytically.
-/

namespace RectangleCLTArxivV1

open RectangleCLT.Companion

noncomputable def intrinsicBandwidth (A δ s₄ L : ℝ) : ℝ :=
  A * max δ (Real.sqrt (s₄ * D_L δ L))

noncomputable def intrinsicComparisonLog (L h : ℝ) : ℝ :=
  1 + Real.log (1 + 1 / (L * h ^ 2))

def intrinsicOptimizationConstant (A C : ℝ) : ℝ := 1 + 2 * A + C * (A + 3)

theorem intrinsicBandwidth_admissible {A δ s₄ L : ℝ} (hA : 0 ≤ A) :
    A * δ ≤ intrinsicBandwidth A δ s₄ L :=
  mul_le_mul_of_nonneg_left (le_max_left _ _) hA

theorem intrinsicBandwidth_pos {A δ s₄ L : ℝ} (hA : 0 < A) (hδ : 0 < δ) :
    0 < intrinsicBandwidth A δ s₄ L :=
  mul_pos hA (hδ.trans_le (le_max_left _ _))

theorem intrinsicBandwidth_le_sum {A δ s₄ L : ℝ} (hA : 0 ≤ A) (hδ : 0 ≤ δ) :
    intrinsicBandwidth A δ s₄ L ≤ A * (δ + Real.sqrt (s₄ * D_L δ L)) := by
  apply mul_le_mul_of_nonneg_left _ hA
  exact max_le (le_add_of_nonneg_right (Real.sqrt_nonneg _)) (le_add_of_nonneg_left hδ)

theorem intrinsic_log_one_add_square {x : ℝ} (hx : 0 < x) :
    Real.log (1 + x ^ 2) ≤ Real.log 2 + 2 * logPlus x := by
  by_cases hs : x ≤ 1
  · have hx2 : x ^ 2 ≤ 1 := by nlinarith
    have hl := Real.log_le_log (by positivity : 0 < 1 + x ^ 2)
      (show 1 + x ^ 2 ≤ 2 by linarith)
    exact hl.trans (le_add_of_nonneg_right (mul_nonneg (by norm_num) (logPlus_nonneg x)))
  · have hx1 : 1 ≤ x := (lt_of_not_ge hs).le
    have hx2 : 1 ≤ x ^ 2 := by nlinarith
    have hl := Real.log_le_log (by positivity : 0 < 1 + x ^ 2)
      (show 1 + x ^ 2 ≤ 2 * x ^ 2 by linarith)
    rw [Real.log_mul (by norm_num) (pow_ne_zero 2 hx.ne'), Real.log_pow] at hl
    exact hl.trans (add_le_add_left (mul_le_mul_of_nonneg_left (le_max_right _ _)
      (by norm_num)) _)

theorem intrinsicComparisonLog_le_D_L {δ L h : ℝ}
    (hδ : 0 < δ) (hL : 0 < L) (hband : δ ≤ h) :
    intrinsicComparisonLog L h ≤ 2 * D_L δ L := by
  have hh : 0 < h := hδ.trans_le hband
  have hd : 0 < δ * Real.sqrt L := mul_pos hδ (Real.sqrt_pos.mpr hL)
  have hs : δ ^ 2 ≤ h ^ 2 := (sq_le_sq₀ hδ.le hh.le).mpr hband
  have hden : (δ * Real.sqrt L) ^ 2 ≤ L * h ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hL.le]
    nlinarith [mul_le_mul_of_nonneg_left hs hL.le]
  have hratio : 1 / (L * h ^ 2) ≤ (1 / (δ * Real.sqrt L)) ^ 2 := by
    rw [div_pow, one_pow]
    exact one_div_le_one_div_of_le (sq_pos_of_pos hd) hden
  have hlog := Real.log_le_log (by positivity : 0 < 1 + 1 / (L * h ^ 2))
    (add_le_add_left hratio 1)
  have hb := intrinsic_log_one_add_square (one_div_pos.mpr hd)
  have htwo : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  unfold intrinsicComparisonLog D_L
  linarith

theorem intrinsicBandwidth_fourth_cost_le {A δ s₄ L : ℝ}
    (hA : 1 ≤ A) (hδ : 0 < δ) (hs₄ : 0 ≤ s₄) :
    s₄ / intrinsicBandwidth A δ s₄ L * (2 * D_L δ L) ≤
      2 * Real.sqrt (s₄ * D_L δ L) := by
  have hh := intrinsicBandwidth_pos (s₄ := s₄) (L := L) (zero_lt_one.trans_le hA) hδ
  have hD := D_L_nonneg δ L
  have hsq := Real.sq_sqrt (mul_nonneg hs₄ hD)
  have hr : Real.sqrt (s₄ * D_L δ L) ≤ intrinsicBandwidth A δ s₄ L := by
    have hm : 0 ≤ max δ (Real.sqrt (s₄ * D_L δ L)) := hδ.le.trans (le_max_left _ _)
    exact (le_max_right _ _).trans (le_mul_of_one_le_left hm hA)
  rw [show s₄ / intrinsicBandwidth A δ s₄ L * (2 * D_L δ L) =
    (2 * (s₄ * D_L δ L)) / intrinsicBandwidth A δ s₄ L by ring]
  apply (div_le_iff₀ hh).mpr
  nlinarith [mul_le_mul_of_nonneg_left hr (Real.sqrt_nonneg (s₄ * D_L δ L))]

theorem intrinsicBandwidth_total_cost_le {A δ s₄ L : ℝ}
    (hA : 1 ≤ A) (hδ : 0 < δ) (hL : 0 < L) (hs₄ : 0 ≤ s₄) :
    intrinsicBandwidth A δ s₄ L + δ +
      s₄ / intrinsicBandwidth A δ s₄ L *
        intrinsicComparisonLog L (intrinsicBandwidth A δ s₄ L) ≤
          (A + 3) * (δ + Real.sqrt (s₄ * D_L δ L)) := by
  have hh := intrinsicBandwidth_pos (s₄ := s₄) (L := L) (zero_lt_one.trans_le hA) hδ
  have hband : δ ≤ intrinsicBandwidth A δ s₄ L :=
    (le_mul_of_one_le_left hδ.le hA).trans (intrinsicBandwidth_admissible (zero_le_one.trans hA))
  have hl := intrinsicComparisonLog_le_D_L hδ hL hband
  have hc := (mul_le_mul_of_nonneg_left hl (div_nonneg hs₄ hh.le)).trans
    (intrinsicBandwidth_fourth_cost_le hA hδ hs₄)
  have hb := intrinsicBandwidth_le_sum (zero_le_one.trans hA) hδ.le (s₄ := s₄) (L := L)
  nlinarith [Real.sqrt_nonneg (s₄ * D_L δ L)]

/-- The large-bandwidth branch costs only the elementary probability bound. -/
theorem large_intrinsicBandwidth_rate {A κ δ s₄ L : ℝ}
    (hA : 1 ≤ A) (hκ : 1 ≤ κ) (hδ : 0 < δ) (hL : 1 ≤ L)
    (hlarge : (1 / 4 : ℝ) ≤ L * (intrinsicBandwidth A δ s₄ L) ^ 2) :
    1 ≤ 2 * A * intrinsicRelativeRate κ δ s₄ L := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hh := intrinsicBandwidth_pos (s₄ := s₄) (L := L) (zero_lt_one.trans_le hA) hδ
  have hy : (1 / 2 : ℝ) ≤ Real.sqrt L * intrinsicBandwidth A δ s₄ L := by
    have he : (Real.sqrt L * intrinsicBandwidth A δ s₄ L) ^ 2 =
        L * (intrinsicBandwidth A δ s₄ L) ^ 2 := by rw [mul_pow, Real.sq_sqrt hLp.le]
    have hn := mul_nonneg (Real.sqrt_nonneg L) hh.le
    nlinarith
  have hb := mul_le_mul_of_nonneg_left
    (intrinsicBandwidth_le_sum (zero_le_one.trans hA) hδ.le (s₄ := s₄) (L := L))
    (Real.sqrt_nonneg L)
  have hs : Real.sqrt L ≤ L := (Real.sqrt_le_iff).mpr ⟨hLp.le, by nlinarith⟩
  have hk : Real.sqrt L ≤ κ * L := hs.trans (le_mul_of_one_le_left hLp.le hκ)
  have hm := mul_le_mul_of_nonneg_right hk
    (add_nonneg hδ.le (Real.sqrt_nonneg (s₄ * D_L δ L)))
  unfold intrinsicRelativeRate
  nlinarith [mul_le_mul_of_nonneg_left hm (zero_le_one.trans hA)]

/-- Scalar reduction retaining `κ` throughout. The probabilistic assembly
must supply `hsmall` from the actual two-stage comparison and smoothing. -/
theorem intrinsic_rate_of_small_bandwidth_estimate {A C κ δ s₄ L error : ℝ}
    (hA : 1 ≤ A) (hC : 0 ≤ C) (hκ : 1 ≤ κ) (hδ : 0 < δ) (hL : 1 ≤ L) (hs₄ : 0 ≤ s₄)
    (hone : error ≤ 1)
    (hsmall : L * (intrinsicBandwidth A δ s₄ L) ^ 2 < 1 / 4 →
      error ≤ C * κ * L * (intrinsicBandwidth A δ s₄ L + δ +
        s₄ / intrinsicBandwidth A δ s₄ L *
          intrinsicComparisonLog L (intrinsicBandwidth A δ s₄ L))) :
    error ≤ intrinsicOptimizationConstant A C * min 1 (intrinsicRelativeRate κ δ s₄ L) := by
  have hK1 : 1 ≤ intrinsicOptimizationConstant A C := by
    unfold intrinsicOptimizationConstant
    nlinarith [mul_nonneg hC (show 0 ≤ A + 3 by linarith)]
  have hKA : 2 * A ≤ intrinsicOptimizationConstant A C := by
    unfold intrinsicOptimizationConstant
    nlinarith [mul_nonneg hC (show 0 ≤ A + 3 by linarith)]
  have hKC : C * (A + 3) ≤ intrinsicOptimizationConstant A C := by
    unfold intrinsicOptimizationConstant
    linarith
  have hr := intrinsicRelativeRate_nonneg (zero_le_one.trans hκ) hδ.le (zero_le_one.trans hL)
    (s₄ := s₄)
  have hraw : error ≤ intrinsicOptimizationConstant A C * intrinsicRelativeRate κ δ s₄ L := by
    by_cases hs : L * (intrinsicBandwidth A δ s₄ L) ^ 2 < 1 / 4
    · have hb := intrinsicBandwidth_total_cost_le hA hδ (zero_lt_one.trans_le hL) hs₄
      have he := (hsmall hs).trans (mul_le_mul_of_nonneg_left hb
        (mul_nonneg (mul_nonneg hC (zero_le_one.trans hκ)) (zero_le_one.trans hL)))
      have he' : error ≤ (C * (A + 3)) * intrinsicRelativeRate κ δ s₄ L := by
        simpa only [intrinsicRelativeRate] using he.trans_eq (by ring)
      exact he'.trans (mul_le_mul_of_nonneg_right hKC hr)
    · exact hone.trans ((large_intrinsicBandwidth_rate hA hκ hδ hL (le_of_not_gt hs)).trans
        (mul_le_mul_of_nonneg_right hKA hr))
  by_cases hs : intrinsicRelativeRate κ δ s₄ L ≤ 1
  · simpa only [min_eq_right hs] using hraw
  · simpa only [min_eq_left (le_of_not_ge hs), mul_one] using hone.trans hK1

/-- In the complementary envelope regime the target rate already has a
fixed lower bound, so no interpolation estimate is needed. -/
theorem intrinsic_trivial_large_envelope {error g δ s₄ L : ℝ}
    (hone : error ≤ 1) (hg : Real.sqrt (2 / Real.pi) ≤ g)
    (_hδ : 0 ≤ δ) (hL : 1 ≤ L) (hlarge : g < δ * L) :
    error ≤ (Real.pi / 2) * intrinsicRelativeRate g δ s₄ L := by
  have hc : 0 < Real.sqrt (2 / Real.pi) := by positivity
  have hg0 : 0 ≤ g := hc.le.trans hg
  have hgsq : 2 / Real.pi ≤ g ^ 2 := by
    have hs := Real.sq_sqrt (show 0 ≤ 2 / Real.pi by positivity)
    nlinarith [sq_nonneg (g - Real.sqrt (2 / Real.pi))]
  have hr : g ^ 2 ≤ intrinsicRelativeRate g δ s₄ L := by
    have hh := mul_le_mul_of_nonneg_left hlarge.le hg0
    have he := mul_nonneg (mul_nonneg hg0 (zero_le_one.trans hL))
      (Real.sqrt_nonneg (s₄ * D_L δ L))
    unfold intrinsicRelativeRate
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left (hgsq.trans hr) (show 0 ≤ Real.pi / 2 by positivity)
  have heq : (Real.pi / 2) * (2 / Real.pi) = 1 := by field_simp
  rw [heq] at hmul
  exact hone.trans hmul

/-- Multiplying a nonnegative uncapped rate loses at most the same fixed
factor after capping the probability bound at one. -/
theorem intrinsic_min_one_mul_le {C x : ℝ} (_hC : 0 ≤ C) (hx : 0 ≤ x) :
    min 1 (C * x) ≤ max 1 C * min 1 x := by
  by_cases hs : x ≤ 1
  · rw [min_eq_right hs]
    exact (min_le_right _ _).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hx)
  · rw [min_eq_left (le_of_not_ge hs), mul_one]
    exact (min_le_left _ _).trans (le_max_left _ _)

/-- The intrinsic rate is linear in its expected-maximum coefficient. -/
theorem intrinsicRelativeRate_le_coefficient {κ C g δ s₄ L : ℝ}
    (hcoef : κ ≤ C * g) (hδ : 0 ≤ δ) (hL : 0 ≤ L) :
    intrinsicRelativeRate κ δ s₄ L ≤ C * intrinsicRelativeRate g δ s₄ L := by
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoef hL)
    (add_nonneg hδ (Real.sqrt_nonneg (s₄ * D_L δ L)))
  exact hh.trans_eq (by unfold intrinsicRelativeRate; ring)

theorem intrinsicRelativeRate_capped_le_coefficient {κ C g δ s₄ L : ℝ}
    (hcoef : κ ≤ C * g) (hC : 0 ≤ C) (hg : 0 ≤ g) (hδ : 0 ≤ δ) (hL : 0 ≤ L) :
    min 1 (intrinsicRelativeRate κ δ s₄ L) ≤
      max 1 C * min 1 (intrinsicRelativeRate g δ s₄ L) := by
  exact (min_le_min_left 1 (intrinsicRelativeRate_le_coefficient hcoef hδ hL)).trans
    (intrinsic_min_one_mul_le hC (intrinsicRelativeRate_nonneg hg hδ hL))

/-- The elementary probability bound is retained when an uncapped scalar
estimate is converted to the paper's displayed capped rate. -/
theorem intrinsic_capped_of_le_one_and_mul {error C x : ℝ}
    (hx : 0 ≤ x) (hone : error ≤ 1) (hraw : error ≤ C * x) :
    error ≤ max 1 C * min 1 x := by
  by_cases hs : x ≤ 1
  · rw [min_eq_right hs]
    exact hraw.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hx)
  · rw [min_eq_left (le_of_not_ge hs), mul_one]
    exact hone.trans (le_max_left _ _)

/-- The envelope supplies the paper's simpler rate. -/
theorem intrinsicRelativeRate_envelope_le {g δ L : ℝ}
    (hg : 0 ≤ g) (hδ : 0 ≤ δ) (hL : 0 ≤ L) :
    intrinsicRelativeRate g δ (δ ^ 2) L ≤
      2 * (δ * g * L * Real.sqrt (D_L δ L)) := by
  have hD : 1 ≤ D_L δ L := one_le_D_L δ L
  have hs : Real.sqrt (δ ^ 2 * D_L δ L) = δ * Real.sqrt (D_L δ L) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hδ]
  have hr : 1 ≤ Real.sqrt (D_L δ L) := Real.one_le_sqrt.mpr hD
  unfold intrinsicRelativeRate
  rw [hs]
  have hm := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hr hδ) (mul_nonneg hg hL)
  nlinarith only [hm]

end RectangleCLTArxivV1
