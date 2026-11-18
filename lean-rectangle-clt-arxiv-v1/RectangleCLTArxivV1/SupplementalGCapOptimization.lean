import RectangleCLTArxivV1.IntrinsicOptimization
import RectangleCLTArxivV1.SupplementalGCapIntegration

/- Scalar bandwidth choice in the dimension-cap proof. Actual comparison
estimates remain explicit inputs of this reduction. -/
namespace RectangleCLTArxivV1
open RectangleCLT.Companion
noncomputable section

def dimensionCapGain (δ L : ℝ) : ℝ := min (D_L δ L) L

def dimensionCapBandwidth (A δ L : ℝ) : ℝ := A * δ * Real.sqrt (dimensionCapGain δ L)

def dimensionCapRate (κ δ L : ℝ) : ℝ := δ * κ * L * Real.sqrt (dimensionCapGain δ L)

theorem one_le_dimensionCapGain {δ L : ℝ} (hL : 1 ≤ L) : 1 ≤ dimensionCapGain δ L :=
  le_min (one_le_D_L δ L) hL

theorem dimensionCapBandwidth_admissible {A δ L : ℝ} (hA : 0 ≤ A) (hδ : 0 ≤ δ)
    (hL : 1 ≤ L) : A * δ ≤ dimensionCapBandwidth A δ L := by
  exact le_mul_of_one_le_right (mul_nonneg hA hδ)
    (Real.one_le_sqrt.2 (one_le_dimensionCapGain hL))

theorem dimensionCapBandwidth_pos {A δ L : ℝ} (hA : 0 < A) (hδ : 0 < δ)
    (hL : 1 ≤ L) : 0 < dimensionCapBandwidth A δ L :=
  (mul_pos hA hδ).trans_le (dimensionCapBandwidth_admissible hA.le hδ.le hL)

theorem dimensionCap_time_log_le {δ L h : ℝ} (hδ : 0 < δ) (hL : 1 ≤ L)
    (hband : δ ≤ h) : min (1 + Real.log (1 / (L * h ^ 2))) L ≤
      2 * dimensionCapGain δ L := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hh : 0 < h := hδ.trans_le hband
  have hr : 0 < 1 / (L * h ^ 2) := by positivity
  have hl := Real.log_le_log hr (by linarith : 1 / (L * h ^ 2) ≤ 1 + 1 / (L * h ^ 2))
  have hlog := intrinsicComparisonLog_le_D_L hδ hLp hband
  have hd : 1 + Real.log (1 / (L * h ^ 2)) ≤ 2 * D_L δ L := by
    unfold intrinsicComparisonLog at hlog
    linarith
  by_cases hcase : D_L δ L ≤ L
  · unfold dimensionCapGain
    rw [min_eq_left hcase]
    exact (min_le_left _ _).trans hd
  · unfold dimensionCapGain
    rw [min_eq_right (le_of_not_ge hcase)]
    exact (min_le_right _ _).trans (by linarith)

theorem dimensionCapBandwidth_total_cost {A δ L : ℝ} (hA : 1 ≤ A) (hδ : 0 < δ)
    (hL : 1 ≤ L) :
    dimensionCapBandwidth A δ L + δ + δ ^ 2 / dimensionCapBandwidth A δ L *
      min (1 + Real.log (1 / (L * dimensionCapBandwidth A δ L ^ 2))) L ≤
      (A + 3) * δ * Real.sqrt (dimensionCapGain δ L) := by
  let J := dimensionCapGain δ L
  let h := dimensionCapBandwidth A δ L
  have hJ : 1 ≤ J := one_le_dimensionCapGain hL
  have hs : 1 ≤ Real.sqrt J := Real.one_le_sqrt.2 hJ
  have hh : 0 < h := dimensionCapBandwidth_pos (zero_lt_one.trans_le hA) hδ hL
  have hband : δ ≤ h := (le_mul_of_one_le_left hδ.le hA).trans
    (dimensionCapBandwidth_admissible (zero_le_one.trans hA) hδ.le hL)
  have hlog := dimensionCap_time_log_le hδ hL hband
  have hcost := mul_le_mul_of_nonneg_left hlog (div_nonneg (sq_nonneg δ) hh.le)
  have hroot : δ * Real.sqrt J ≤ h := by
    change _ ≤ A * δ * Real.sqrt J
    nlinarith [mul_nonneg hδ.le (Real.sqrt_nonneg J)]
  have hsquare : (δ * Real.sqrt J) ^ 2 = δ ^ 2 * J := by
    rw [mul_pow, Real.sq_sqrt (zero_le_one.trans hJ)]
  have hlast : δ ^ 2 / h * (2 * J) ≤ 2 * δ * Real.sqrt J := by
    rw [show δ ^ 2 / h * (2 * J) = 2 * (δ * Real.sqrt J) ^ 2 / h by rw [hsquare]; ring]
    apply (div_le_iff₀ hh).2
    nlinarith [mul_le_mul_of_nonneg_left hroot (mul_nonneg hδ.le (Real.sqrt_nonneg J))]
  change h + δ + _ ≤ _
  have hδroot : δ ≤ δ * Real.sqrt J := le_mul_of_one_le_right hδ.le hs
  have heq : h = A * (δ * Real.sqrt J) := by dsimp [h, dimensionCapBandwidth, J]; ring
  change _ ≤ (A + 3) * δ * Real.sqrt J
  change _ ≤ δ ^ 2 / h * (2 * J) at hcost
  nlinarith [hcost.trans hlast]

theorem dimensionCap_large_bandwidth_rate {A κ δ L : ℝ}
    (hA : 1 ≤ A) (hκ : 1 ≤ κ) (hδ : 0 < δ) (hL : 1 ≤ L)
    (hlarge : 1 / 4 ≤ L * dimensionCapBandwidth A δ L ^ 2) :
    1 ≤ 2 * A * dimensionCapRate κ δ L := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hh := dimensionCapBandwidth_pos (zero_lt_one.trans_le hA) hδ hL
  have hs : Real.sqrt L ≤ L := (Real.sqrt_le_iff).2 ⟨hLp.le, by nlinarith⟩
  have hk : Real.sqrt L ≤ κ * L := hs.trans (le_mul_of_one_le_left hLp.le hκ)
  have hsq : (Real.sqrt L * dimensionCapBandwidth A δ L) ^ 2 =
      L * dimensionCapBandwidth A δ L ^ 2 := by rw [mul_pow, Real.sq_sqrt hLp.le]
  have hhalf : 1 / 2 ≤ Real.sqrt L * dimensionCapBandwidth A δ L := by
    nlinarith [mul_nonneg (Real.sqrt_nonneg L) hh.le]
  have hscale := mul_le_mul_of_nonneg_right hk hh.le
  unfold dimensionCapBandwidth dimensionCapRate at *
  nlinarith only [hhalf, hscale]

/-- This scalar reduction consumes the actual small-width comparison. -/
theorem dimensionCap_rate_of_small_bandwidth_estimate {A C κ δ L error : ℝ}
    (hA : 1 ≤ A) (hC : 0 ≤ C) (hκ : 1 ≤ κ) (hδ : 0 < δ) (hL : 1 ≤ L)
    (hone : error ≤ 1)
    (hsmall : L * dimensionCapBandwidth A δ L ^ 2 < 1 / 4 →
      error ≤ C * κ * L * (dimensionCapBandwidth A δ L + δ +
        δ ^ 2 / dimensionCapBandwidth A δ L *
          min (1 + Real.log (1 / (L * dimensionCapBandwidth A δ L ^ 2))) L)) :
    error ≤ intrinsicOptimizationConstant A C * min 1 (dimensionCapRate κ δ L) := by
  have hK1 : 1 ≤ intrinsicOptimizationConstant A C := by
    unfold intrinsicOptimizationConstant
    nlinarith [mul_nonneg hC (by linarith : 0 ≤ A + 3)]
  have hKA : 2 * A ≤ intrinsicOptimizationConstant A C := by
    unfold intrinsicOptimizationConstant
    nlinarith [mul_nonneg hC (by linarith : 0 ≤ A + 3)]
  have hKC : C * (A + 3) ≤ intrinsicOptimizationConstant A C := by
    unfold intrinsicOptimizationConstant
    linarith
  have hr : 0 ≤ dimensionCapRate κ δ L := by
    unfold dimensionCapRate
    positivity
  have hraw : error ≤ intrinsicOptimizationConstant A C * dimensionCapRate κ δ L := by
    by_cases hs : L * dimensionCapBandwidth A δ L ^ 2 < 1 / 4
    · have hb := dimensionCapBandwidth_total_cost hA hδ hL
      have he := (hsmall hs).trans (mul_le_mul_of_nonneg_left hb
        (by positivity : 0 ≤ C * κ * L))
      have he' : error ≤ (C * (A + 3)) * dimensionCapRate κ δ L := by
        convert he using 1
        unfold dimensionCapRate
        ring
      exact he'.trans (mul_le_mul_of_nonneg_right hKC hr)
    · exact hone.trans ((dimensionCap_large_bandwidth_rate hA hκ hδ hL (le_of_not_gt hs)).trans
        (mul_le_mul_of_nonneg_right hKA hr))
  by_cases hs : dimensionCapRate κ δ L ≤ 1
  · simpa only [min_eq_right hs] using hraw
  · simpa only [min_eq_left (le_of_not_ge hs), mul_one] using hone.trans hK1

theorem dimensionCapRate_le_coefficient {κ C g δ L : ℝ}
    (hcoef : κ ≤ C * g) (hδ : 0 ≤ δ) (hL : 0 ≤ L) :
    dimensionCapRate κ δ L ≤ C * dimensionCapRate g δ L := by
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoef hδ) hL)
    (Real.sqrt_nonneg (dimensionCapGain δ L))
  convert h using 1
  unfold dimensionCapRate
  ring

theorem dimensionCap_trivial_large_envelope {error g δ L : ℝ}
    (hone : error ≤ 1) (hg : Real.sqrt (2 / Real.pi) ≤ g)
    (hδ : 0 ≤ δ) (hL : 1 ≤ L) (hlarge : g < δ * L) :
    error ≤ (Real.pi / 2) * dimensionCapRate g δ L := by
  have hc : 0 < Real.sqrt (2 / Real.pi) := by positivity
  have hg0 : 0 ≤ g := hc.le.trans hg
  have hgsq : 2 / Real.pi ≤ g ^ 2 := by
    have hs := Real.sq_sqrt (show 0 ≤ 2 / Real.pi by positivity)
    nlinarith [sq_nonneg (g - Real.sqrt (2 / Real.pi))]
  have hsqrt : 1 ≤ Real.sqrt (dimensionCapGain δ L) :=
    Real.one_le_sqrt.2 (one_le_dimensionCapGain hL)
  have hbase := mul_le_mul_of_nonneg_left hlarge.le hg0
  have hcost := le_mul_of_one_le_right
    (mul_nonneg (mul_nonneg hδ hg0) (zero_le_one.trans hL)) hsqrt
  have hr : g ^ 2 ≤ dimensionCapRate g δ L := by
    unfold dimensionCapRate
    nlinarith only [hbase, hcost]
  have hmul := mul_le_mul_of_nonneg_left (hgsq.trans hr) (show 0 ≤ Real.pi / 2 by positivity)
  have heq : (Real.pi / 2) * (2 / Real.pi) = 1 := by field_simp
  rw [heq] at hmul
  exact hone.trans hmul

end
end RectangleCLTArxivV1
