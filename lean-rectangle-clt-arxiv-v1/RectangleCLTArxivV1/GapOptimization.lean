import RectangleCLTArxivV1.GapIntegration
import RectangleCLTArxivV1.IntrinsicOptimization

/-! The actual bandwidth choice and the large-bandwidth branch in
Corollary 4. The final scalar reduction states its small-width comparison
premise explicitly; it is not a replacement for the H matrix suppliers. -/
namespace RectangleCLTArxivV1
open RectangleCLT.Companion
noncomputable section
set_option autoImplicit false

def positiveGapBandwidth (A δ c : ℝ) : ℝ := A*δ*Real.sqrt (positiveGapGain c)

def positiveGapRate (κ δ L c : ℝ) : ℝ := δ*κ*L*Real.sqrt (positiveGapGain c)

theorem positiveGapBandwidth_admissible {A δ c : ℝ} (hA : 0 ≤ A) (hδ : 0 ≤ δ)
    (hc : 0 < c) (hc1 : c ≤ 1) : A*δ ≤ positiveGapBandwidth A δ c :=
  le_mul_of_one_le_right (mul_nonneg hA hδ)
    (Real.one_le_sqrt.2 (one_le_positiveGapGain hc hc1))

theorem positiveGapBandwidth_pos {A δ c : ℝ} (hA : 0 < A) (hδ : 0 < δ)
    (hc : 0 < c) (hc1 : c ≤ 1) : 0 < positiveGapBandwidth A δ c :=
  (mul_pos hA hδ).trans_le (positiveGapBandwidth_admissible hA.le hδ.le hc hc1)

theorem positiveGapBandwidth_total_cost {A δ c : ℝ} (hA : 1 ≤ A) (hδ : 0 < δ)
    (hc : 0 < c) (hc1 : c ≤ 1) :
    positiveGapBandwidth A δ c+δ+δ^2*positiveGapGain c/positiveGapBandwidth A δ c ≤
      (A+2)*δ*Real.sqrt (positiveGapGain c) := by
  let J := positiveGapGain c
  let h := positiveGapBandwidth A δ c
  have hJ : 1 ≤ J := one_le_positiveGapGain hc hc1
  have hs : 1 ≤ Real.sqrt J := Real.one_le_sqrt.2 hJ
  have hh : 0 < h := positiveGapBandwidth_pos (zero_lt_one.trans_le hA) hδ hc hc1
  have hroot : δ*Real.sqrt J ≤ h := by
    change _ ≤ A*δ*Real.sqrt J
    nlinarith [mul_nonneg hδ.le (Real.sqrt_nonneg J)]
  have hsquare : (δ*Real.sqrt J)^2=δ^2*J := by
    rw [mul_pow,Real.sq_sqrt (zero_le_one.trans hJ)]
  have hlast : δ^2*J/h ≤ δ*Real.sqrt J := by
    rw [← hsquare]
    apply (div_le_iff₀ hh).2
    nlinarith [mul_le_mul_of_nonneg_left hroot (mul_nonneg hδ.le (Real.sqrt_nonneg J))]
  have hδroot : δ ≤ δ*Real.sqrt J := le_mul_of_one_le_right hδ.le hs
  have heq : h=A*(δ*Real.sqrt J) := by dsimp [h,positiveGapBandwidth,J]; ring
  change h+δ+δ^2*J/h ≤ (A+2)*δ*Real.sqrt J
  nlinarith

theorem positiveGap_large_bandwidth_rate {A κ δ L c : ℝ}
    (hA : 1 ≤ A) (hκ : 1 ≤ κ) (hδ : 0 < δ) (hL : 1 ≤ L)
    (hc : 0 < c) (hc1 : c ≤ 1)
    (hlarge : 1/4 ≤ L*positiveGapBandwidth A δ c^2) :
    1 ≤ 2*A*positiveGapRate κ δ L c := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hh := positiveGapBandwidth_pos (zero_lt_one.trans_le hA) hδ hc hc1
  have hs : Real.sqrt L ≤ L := (Real.sqrt_le_iff).2 ⟨hLp.le, by nlinarith⟩
  have hk : Real.sqrt L ≤ κ*L := hs.trans (le_mul_of_one_le_left hLp.le hκ)
  have hsq : (Real.sqrt L*positiveGapBandwidth A δ c)^2=
      L*positiveGapBandwidth A δ c^2 := by rw [mul_pow,Real.sq_sqrt hLp.le]
  have hhalf : 1/2 ≤ Real.sqrt L*positiveGapBandwidth A δ c := by
    nlinarith [mul_nonneg (Real.sqrt_nonneg L) hh.le]
  have hscale := mul_le_mul_of_nonneg_right hk hh.le
  unfold positiveGapBandwidth positiveGapRate at *
  nlinarith only [hhalf,hscale]

/-- A scalar intermediate with the small-width estimate visible in its
type. Both width branches and the cap by one are proved here. -/
theorem positiveGap_rate_of_small_bandwidth_estimate {A C κ δ L c error : ℝ}
    (hA : 1 ≤ A) (hC : 0 ≤ C) (hκ : 1 ≤ κ) (hδ : 0 < δ) (hL : 1 ≤ L)
    (hc : 0 < c) (hc1 : c ≤ 1) (hone : error ≤ 1)
    (hsmall : L*positiveGapBandwidth A δ c^2 < 1/4 →
      error ≤ C*κ*L*(positiveGapBandwidth A δ c+δ+
        δ^2*positiveGapGain c/positiveGapBandwidth A δ c)) :
    error ≤ intrinsicOptimizationConstant A C*min 1 (positiveGapRate κ δ L c) := by
  have hK1 : 1 ≤ intrinsicOptimizationConstant A C := by
    unfold intrinsicOptimizationConstant
    nlinarith [mul_nonneg hC (by linarith : 0 ≤ A+3)]
  have hKA : 2*A ≤ intrinsicOptimizationConstant A C := by
    unfold intrinsicOptimizationConstant
    nlinarith [mul_nonneg hC (by linarith : 0 ≤ A+3)]
  have hKC : C*(A+2) ≤ intrinsicOptimizationConstant A C := by
    unfold intrinsicOptimizationConstant
    nlinarith
  have hr : 0 ≤ positiveGapRate κ δ L c := by unfold positiveGapRate; positivity
  have hraw : error ≤ intrinsicOptimizationConstant A C*positiveGapRate κ δ L c := by
    by_cases hs : L*positiveGapBandwidth A δ c^2 < 1/4
    · have hb := positiveGapBandwidth_total_cost hA hδ hc hc1
      have he := (hsmall hs).trans (mul_le_mul_of_nonneg_left hb
        (by positivity : 0 ≤ C*κ*L))
      have he' : error ≤ (C*(A+2))*positiveGapRate κ δ L c := by
        convert he using 1
        unfold positiveGapRate
        ring
      exact he'.trans (mul_le_mul_of_nonneg_right hKC hr)
    · exact hone.trans ((positiveGap_large_bandwidth_rate hA hκ hδ hL hc hc1
        (le_of_not_gt hs)).trans (mul_le_mul_of_nonneg_right hKA hr))
  by_cases hs : positiveGapRate κ δ L c ≤ 1
  · simpa only [min_eq_right hs] using hraw
  · simpa only [min_eq_left (le_of_not_ge hs),mul_one] using hone.trans hK1

theorem positiveGapRate_le_coefficient {κ C g δ L c : ℝ}
    (hcoef : κ ≤ C*g) (hδ : 0 ≤ δ) (hL : 0 ≤ L) :
    positiveGapRate κ δ L c ≤ C*positiveGapRate g δ L c := by
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoef hδ) hL)
    (Real.sqrt_nonneg (positiveGapGain c))
  convert h using 1 <;> unfold positiveGapRate <;> ring

theorem positiveGap_trivial_large_envelope {error g δ L c : ℝ}
    (hone : error ≤ 1) (hg : Real.sqrt (2/Real.pi) ≤ g)
    (hδ : 0 ≤ δ) (hL : 1 ≤ L) (hc : 0 < c) (hc1 : c ≤ 1)
    (hlarge : g < δ*L) : error ≤ (Real.pi/2)*positiveGapRate g δ L c := by
  have hc0 : 0 < Real.sqrt (2/Real.pi) := by positivity
  have hg0 : 0 ≤ g := hc0.le.trans hg
  have hgsq : 2/Real.pi ≤ g^2 := by
    have hs := Real.sq_sqrt (show 0 ≤ 2/Real.pi by positivity)
    nlinarith [sq_nonneg (g-Real.sqrt (2/Real.pi))]
  have hsqrt : 1 ≤ Real.sqrt (positiveGapGain c) :=
    Real.one_le_sqrt.2 (one_le_positiveGapGain hc hc1)
  have hbase := mul_le_mul_of_nonneg_left hlarge.le hg0
  have hcost := le_mul_of_one_le_right
    (mul_nonneg (mul_nonneg hδ hg0) (zero_le_one.trans hL)) hsqrt
  have hr : g^2 ≤ positiveGapRate g δ L c := by
    unfold positiveGapRate
    nlinarith only [hbase,hcost]
  have hmul := mul_le_mul_of_nonneg_left (hgsq.trans hr) (show 0 ≤ Real.pi/2 by positivity)
  have heq : (Real.pi/2)*(2/Real.pi)=1 := by field_simp
  rw [heq] at hmul
  exact hone.trans hmul

end
end RectangleCLTArxivV1
