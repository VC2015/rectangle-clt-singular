import RectangleCLTCompanion.Rates
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Scalar bandwidth optimization for the relative fourth-moment rate.
These lemmas are independent of probability laws. The final scalar reduction
labels its small-bandwidth estimate as an explicit input; the CLT endpoint
must discharge that input with the actual initialization/seeded theorems. -/

namespace RectangleCLT.Companion.SplitV4
noncomputable section

def relativeRate (δ s₄ L : ℝ) : ℝ :=
  L^(3/2 : ℝ)*(δ+Real.sqrt (s₄*D_L δ L))

def relativeBandwidth (A δ s₄ L : ℝ) : ℝ :=
  A*max δ (Real.sqrt (s₄*D_L δ L))

def relativeComparisonLog (L h : ℝ) : ℝ :=
  1+Real.log (1+1/(L*h^2))

def relativeOptimizationConstant (A C : ℝ) : ℝ :=
  1+2*A+C*(A+3)

theorem relativeRate_nonneg {δ s₄ L : ℝ} (hδ : 0 ≤ δ) (hL : 0 ≤ L) :
    0 ≤ relativeRate δ s₄ L := by unfold relativeRate; positivity

theorem relativeBandwidth_admissible {A δ s₄ L : ℝ} (hA : 0 ≤ A) :
    A*δ ≤ relativeBandwidth A δ s₄ L :=
  mul_le_mul_of_nonneg_left (le_max_left _ _) hA

theorem relativeBandwidth_pos {A δ s₄ L : ℝ} (hA : 0 < A) (hδ : 0 < δ) :
    0 < relativeBandwidth A δ s₄ L :=
  mul_pos hA (hδ.trans_le (le_max_left _ _))

theorem relativeBandwidth_le_sum {A δ s₄ L : ℝ} (hA : 0 ≤ A) (hδ : 0 ≤ δ) :
    relativeBandwidth A δ s₄ L ≤ A*(δ+Real.sqrt (s₄*D_L δ L)) := by
  apply mul_le_mul_of_nonneg_left _ hA
  exact max_le (le_add_of_nonneg_right (Real.sqrt_nonneg _)) (le_add_of_nonneg_left hδ)

theorem log_one_add_square_le_logPlus {x : ℝ} (hx : 0 < x) :
    Real.log (1+x^2) ≤ Real.log 2+2*logPlus x := by
  by_cases hsmall : x ≤ 1
  · have hx2 : x^2 ≤ 1 := by nlinarith
    have hl := Real.log_le_log (by positivity : 0 < 1+x^2) (show 1+x^2 ≤ 2 by linarith)
    exact hl.trans (le_add_of_nonneg_right (mul_nonneg (by norm_num) (logPlus_nonneg x)))
  · have hx1 : 1 ≤ x := (lt_of_not_ge hsmall).le
    have hx2 : 1 ≤ x^2 := by nlinarith
    have hl := Real.log_le_log (by positivity : 0 < 1+x^2) (show 1+x^2 ≤ 2*x^2 by linarith)
    rw [Real.log_mul (by norm_num) (pow_ne_zero 2 hx.ne'), Real.log_pow] at hl
    exact hl.trans (add_le_add_left (mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)) _)

theorem relativeComparisonLog_le_D_L {δ L h : ℝ}
    (hδ : 0 < δ) (hL : 0 < L) (hband : δ ≤ h) :
    relativeComparisonLog L h ≤ 2*D_L δ L := by
  have hh : 0 < h := hδ.trans_le hband
  have hd : 0 < δ*Real.sqrt L := mul_pos hδ (Real.sqrt_pos.mpr hL)
  have hs : δ^2 ≤ h^2 := (sq_le_sq₀ hδ.le hh.le).mpr hband
  have hden : (δ*Real.sqrt L)^2 ≤ L*h^2 := by
    rw [mul_pow, Real.sq_sqrt hL.le]
    nlinarith [mul_le_mul_of_nonneg_left hs hL.le]
  have hratio : 1/(L*h^2) ≤ (1/(δ*Real.sqrt L))^2 := by
    rw [div_pow, one_pow]
    exact one_div_le_one_div_of_le (sq_pos_of_pos hd) hden
  have hlog := Real.log_le_log (by positivity : 0 < 1+1/(L*h^2)) (add_le_add_left hratio 1)
  have hbound := log_one_add_square_le_logPlus (one_div_pos.mpr hd)
  have htwo : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  unfold relativeComparisonLog D_L
  linarith

theorem relativeBandwidth_fourth_cost_le {A δ s₄ L : ℝ}
    (hA : 1 ≤ A) (hδ : 0 < δ) (hs₄ : 0 ≤ s₄) :
    s₄/relativeBandwidth A δ s₄ L*(2*D_L δ L) ≤
      2*Real.sqrt (s₄*D_L δ L) := by
  have hAp : 0 < A := zero_lt_one.trans_le hA
  have hh := relativeBandwidth_pos (s₄ := s₄) (L := L) hAp hδ
  have hD := D_L_nonneg δ L
  have hsq := Real.sq_sqrt (mul_nonneg hs₄ hD)
  have hroot : Real.sqrt (s₄*D_L δ L) ≤ relativeBandwidth A δ s₄ L := by
    have hm : 0 ≤ max δ (Real.sqrt (s₄*D_L δ L)) := (hδ.le.trans (le_max_left _ _))
    exact (le_max_right _ _).trans (le_mul_of_one_le_left hm hA)
  rw [show s₄/relativeBandwidth A δ s₄ L*(2*D_L δ L) =
    (2*(s₄*D_L δ L))/relativeBandwidth A δ s₄ L by ring]
  apply (div_le_iff₀ hh).mpr
  nlinarith [mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg (s₄*D_L δ L))]

theorem relativeBandwidth_total_cost_le {A δ s₄ L : ℝ}
    (hA : 1 ≤ A) (hδ : 0 < δ) (hL : 0 < L) (hs₄ : 0 ≤ s₄) :
    relativeBandwidth A δ s₄ L+δ+
      s₄/relativeBandwidth A δ s₄ L*relativeComparisonLog L (relativeBandwidth A δ s₄ L) ≤
        (A+3)*(δ+Real.sqrt (s₄*D_L δ L)) := by
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hh := relativeBandwidth_pos (s₄ := s₄) (L := L) (zero_lt_one.trans_le hA) hδ
  have hband : δ ≤ relativeBandwidth A δ s₄ L :=
    (le_mul_of_one_le_left hδ.le hA).trans (relativeBandwidth_admissible hA0)
  have hl := relativeComparisonLog_le_D_L hδ hL hband
  have hcost := (mul_le_mul_of_nonneg_left hl (div_nonneg hs₄ hh.le)).trans
    (relativeBandwidth_fourth_cost_le hA hδ hs₄)
  have hb := relativeBandwidth_le_sum hA0 hδ.le (s₄ := s₄) (L := L)
  nlinarith [Real.sqrt_nonneg (s₄*D_L δ L)]

theorem large_relativeBandwidth_rate {A δ s₄ L : ℝ}
    (hA : 1 ≤ A) (hδ : 0 < δ) (hL : 1 ≤ L)
    (hlarge : (1/4 : ℝ) ≤ L*(relativeBandwidth A δ s₄ L)^2) :
    1 ≤ 2*A*relativeRate δ s₄ L := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hh := relativeBandwidth_pos (s₄ := s₄) (L := L) (zero_lt_one.trans_le hA) hδ
  have hsqrt := Real.sq_sqrt hLp.le
  have hy : (1/2 : ℝ) ≤ Real.sqrt L*relativeBandwidth A δ s₄ L := by
    have hnonneg := mul_nonneg (Real.sqrt_nonneg L) hh.le
    have he : (Real.sqrt L*relativeBandwidth A δ s₄ L)^2 = L*(relativeBandwidth A δ s₄ L)^2 := by
      rw [mul_pow, hsqrt]
    nlinarith
  have hb := mul_le_mul_of_nonneg_left
    (relativeBandwidth_le_sum hA0 hδ.le (s₄ := s₄) (L := L)) (Real.sqrt_nonneg L)
  have hmono : Real.sqrt L*(δ+Real.sqrt (s₄*D_L δ L)) ≤
      L*(Real.sqrt L*(δ+Real.sqrt (s₄*D_L δ L))) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hL
      (mul_nonneg (Real.sqrt_nonneg L) (add_nonneg hδ.le (Real.sqrt_nonneg (s₄*D_L δ L))))
  unfold relativeRate
  rw [rpow_three_halves_eq_mul_sqrt hLp]
  nlinarith [mul_le_mul_of_nonneg_left hmono hA0]

/-- Explicit scalar reduction only. The probabilistic theorem supplies
`hsmall` from the proved initialization, seeded comparison, and smoothing. -/
theorem relative_rate_of_small_bandwidth_estimate {A C δ s₄ L error : ℝ}
    (hA : 1 ≤ A) (hC : 0 ≤ C) (hδ : 0 < δ) (hL : 1 ≤ L) (hs₄ : 0 ≤ s₄)
    (hone : error ≤ 1)
    (hsmall : L*(relativeBandwidth A δ s₄ L)^2 < 1/4 →
      error ≤ C*L^(3/2 : ℝ)*(relativeBandwidth A δ s₄ L+δ+
        s₄/relativeBandwidth A δ s₄ L*relativeComparisonLog L (relativeBandwidth A δ s₄ L))) :
    error ≤ relativeOptimizationConstant A C*min 1 (relativeRate δ s₄ L) := by
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hK1 : 1 ≤ relativeOptimizationConstant A C := by
    unfold relativeOptimizationConstant
    nlinarith [mul_nonneg hC (show 0 ≤ A+3 by linarith)]
  have hKA : 2*A ≤ relativeOptimizationConstant A C := by
    unfold relativeOptimizationConstant
    nlinarith [mul_nonneg hC (show 0 ≤ A+3 by linarith)]
  have hKC : C*(A+3) ≤ relativeOptimizationConstant A C := by
    unfold relativeOptimizationConstant
    linarith
  have hrate := relativeRate_nonneg hδ.le (zero_le_one.trans hL) (s₄ := s₄)
  have hraw : error ≤ relativeOptimizationConstant A C*relativeRate δ s₄ L := by
    by_cases hs : L*(relativeBandwidth A δ s₄ L)^2 < 1/4
    · have hb := relativeBandwidth_total_cost_le hA hδ (zero_lt_one.trans_le hL) hs₄
      have he := (hsmall hs).trans (mul_le_mul_of_nonneg_left hb
        (mul_nonneg hC (Real.rpow_nonneg (zero_le_one.trans hL) _)))
      have he' : error ≤ (C*(A+3))*relativeRate δ s₄ L := by
        simpa only [relativeRate] using he.trans_eq (by ring)
      exact he'.trans (mul_le_mul_of_nonneg_right hKC hrate)
    · exact hone.trans ((large_relativeBandwidth_rate hA hδ hL (le_of_not_gt hs)).trans
        (mul_le_mul_of_nonneg_right hKA hrate))
  by_cases hr : relativeRate δ s₄ L ≤ 1
  · simpa only [min_eq_right hr] using hraw
  · simpa only [min_eq_left (le_of_not_ge hr), mul_one] using hone.trans hK1

theorem relativeRate_envelope_le {δ L : ℝ} (hδ : 0 ≤ δ) (hL : 0 < L) :
    relativeRate δ (δ^2) L ≤ 2*unrestrictedRate δ L := by
  have hD := D_L_nonneg δ L
  have hroot : Real.sqrt (δ^2*D_L δ L) = δ*Real.sqrt (D_L δ L) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_of_nonneg hδ]
  have hs : 1 ≤ Real.sqrt (D_L δ L) := Real.one_le_sqrt.mpr (one_le_D_L δ L)
  unfold relativeRate unrestrictedRate
  rw [hroot]
  have hh := mul_le_mul_of_nonneg_left hs hδ
  nlinarith [mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hL.le (3/2 : ℝ))]

theorem relativeRate_envelope_capped_le {δ L : ℝ} (hδ : 0 ≤ δ) (hL : 0 < L) :
    min 1 (relativeRate δ (δ^2) L) ≤ 2*min 1 (unrestrictedRate δ L) := by
  by_cases hr : unrestrictedRate δ L ≤ 1
  · rw [min_eq_right hr]
    exact (min_le_right _ _).trans (relativeRate_envelope_le hδ hL)
  · rw [min_eq_left (le_of_not_ge hr)]
    exact (min_le_left _ _).trans (by norm_num)

end
end RectangleCLT.Companion.SplitV4
