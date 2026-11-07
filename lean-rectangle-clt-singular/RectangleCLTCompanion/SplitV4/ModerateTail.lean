import RectangleCLTCompanion.SplitV4.ModerateProductTail
import RectangleCLTCompanion.SplitV4.ModerateSmallThreshold
import RectangleCLTCompanion.SplitV4.ModerateInverse

/-! The iid-free uniform moderate-tail estimate, derived from the actual Esscher laws. -/
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace RectangleCLT.Companion.SplitV4
noncomputable section

def moderateTailSmallConstant : ℝ :=
  100 * moderateTaylorConstant + 6 * moderateWeightedConstant +
    2 * scalarBerryEsseenConstant / standardNormalUpperTail 2 + 1

def moderateTailRemainderConstant : ℝ := moderateSmallTailConstant + 6 * moderateWeightedConstant +
  2 * moderateCancellationConstant moderateTaylorConstant + moderateLegendreConstant moderateTaylorConstant + 1

theorem moderateTailSmallConstant_bounds :
    0 < moderateTailSmallConstant ∧ 100 * moderateTaylorConstant ≤ moderateTailSmallConstant ∧
      6 * moderateWeightedConstant ≤ moderateTailSmallConstant ∧
      2 * scalarBerryEsseenConstant / standardNormalUpperTail 2 ≤ moderateTailSmallConstant := by
  have hB := moderateTaylorConstant_ge_one
  have hW := moderateWeightedConstant_pos
  have hC := scalarBerryEsseenConstant_pos
  have hT := standardNormalUpperTail_pos 2
  have hD : 0 ≤ 2 * scalarBerryEsseenConstant / standardNormalUpperTail 2 := by positivity
  unfold moderateTailSmallConstant
  constructor
  · positivity
  · constructor
    · linarith
    · constructor <;> linarith

theorem moderateTailRemainderConstant_bounds :
    0 < moderateTailRemainderConstant ∧ moderateSmallTailConstant ≤ moderateTailRemainderConstant ∧
      6 * moderateWeightedConstant + 2 * moderateCancellationConstant moderateTaylorConstant +
        moderateLegendreConstant moderateTaylorConstant ≤ moderateTailRemainderConstant := by
  have hB := moderateTaylorConstant_ge_one
  have hW := moderateWeightedConstant_pos
  have hC := moderateSmallTailConstant_pos
  have hK : 0 ≤ moderateCancellationConstant moderateTaylorConstant := by unfold moderateCancellationConstant; positivity
  have hL : 0 ≤ moderateLegendreConstant moderateTaylorConstant := by
    unfold moderateLegendreConstant moderateInverseDisplacementConstant
    positivity
  unfold moderateTailRemainderConstant
  constructor
  · positivity
  · constructor <;> linarith

set_option maxHeartbeats 1000000 in
theorem moderateProductTail_large_threshold {n : ℕ} (ν : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] (hn : 1 ≤ n) {δ x : ℝ} (hδ : 0 ≤ δ)
    (hbound : ∀ i, ∀ᵐ z ∂ν i, |z| ≤ δ) (hc : ∀ i, (∫ z, z ∂ν i) = 0)
    (hv : (∑ i, ∫ z, z ^ 2 ∂ν i) = 1) (hx : 2 ≤ x)
    (hsmall : moderateTailSmallConstant * (δ * (1 + x)) ≤ 1) :
    0 < (Measure.pi ν).real {z | x < ∑ i, z i} ∧
    |Real.log ((Measure.pi ν).real {z | x < ∑ i, z i} / standardNormalUpperTail x) -
      moderateArrayGamma (Measure.pi ν) (fun i z => z i) * x ^ 3 / 6| ≤
        moderateTailRemainderConstant * (δ * (1 + x) + δ ^ 2 * x ^ 4) := by
  have hx0 : 0 ≤ x := by linarith
  have hxpos : 0 < x := by linarith
  have hb := moderateProduct_coordinate_bound ν hbound
  have hc' (i : Fin n) : (∫ z : Fin n → ℝ, z i ∂Measure.pi ν) = 0 := by
    exact (moderateProduct_coordinate_integral ν i id measurable_id).trans (hc i)
  have hv' : (∑ i, ∫ z : Fin n → ℝ, (z i) ^ 2 ∂Measure.pi ν) = 1 := by
    calc
      _ = ∑ i, ∫ z, z ^ 2 ∂ν i := Finset.sum_congr rfl (fun i _ =>
        moderateProduct_coordinate_integral ν i (fun z => z ^ 2) (measurable_id.pow_const 2))
      _ = 1 := hv
  have hB := moderateTaylorConstant_ge_one
  have hB0 : 0 ≤ moderateTaylorConstant := zero_le_one.trans hB
  have hH := moderateTailSmallConstant_bounds
  have hW := moderateWeightedConstant_pos
  have hdx : 0 ≤ δ * x := mul_nonneg hδ hx0
  have hdx' : δ * x ≤ δ * (1 + x) := by nlinarith
  have hrootSmall : 100 * moderateTaylorConstant * (δ * x) ≤ 1 := by
    apply (mul_le_mul hH.2.1 hdx' hdx (le_of_lt hH.1)).trans hsmall
  have hweak : δ * x ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_right hB hdx]
  obtain ⟨t, ht, hroot⟩ := exists_moderateArrayMean_eq (fun i => measurable_pi_apply i) hδ hb hc' hv' hx0 hrootSmall
  have hdt : δ * t ≤ 2 := by nlinarith [ht.2]
  have hTaylor := moderateArray_local_taylor (fun i => measurable_pi_apply i) hδ hb hc' hv' ht.1 hdt
  have hm : |x - t - moderateArrayGamma (Measure.pi ν) (fun i z => z i) * t ^ 2 / 2| ≤
      moderateTaylorConstant * δ ^ 2 * t ^ 3 := by simpa only [hroot] using hTaylor.2.1
  have hgamma := moderateArrayGamma_abs_le (fun i => measurable_pi_apply i) hδ hb hv'
  have hV := moderateArray_local_variance_bounds (fun i => measurable_pi_apply i) hδ hb hc' hv' hx0 hrootSmall ht
  have hscale := moderate_tilted_threshold_scale hB hδ hx0 ht.1 ht.2 hrootSmall hgamma hV.1 hV.2 hm
  have hcancel := moderate_tilted_threshold_cancellation hB0 hδ hx0 ht.1 ht.2 hweak hgamma
    (by linarith : 0 ≤ moderateArrayVariance (Measure.pi ν) (fun i z => z i) t) hm hTaylor.2.2
  have hleg := moderate_legendre_expansion hB0 hδ hx0 ht.1 ht.2 hweak hgamma hm hTaylor.1
  rw [moderateProduct_variance_eq ν hbound t] at hV hscale hcancel
  rw [moderateProduct_cgf_eq ν t] at hleg
  have hroot' : (∑ i, genericTiltMean (ν i) t) = x := by
    rw [← moderateProduct_mean_eq ν hbound t]
    exact hroot
  change x / 2 ≤ moderateProductTailScale ν t ∧ moderateProductTailScale ν t ≤ 3 * x at hscale
  change |moderateProductTailScale ν t - x| ≤
    moderateCancellationConstant moderateTaylorConstant * δ ^ 2 * x ^ 3 at hcancel
  have hweightedSmall : moderateWeightedConstant * δ * moderateProductTailScale ν t ≤ 1 / 2 := by
    have hh := (mul_le_mul hH.2.2.1 hdx' hdx hH.1.le).trans hsmall
    have hp := mul_le_mul_of_nonneg_left hscale.2 (mul_nonneg hW.le hδ)
    nlinarith only [hh, hp]
  have hs : 1 ≤ moderateProductTailScale ν t := by linarith [hscale.1]
  have hlog := moderateProduct_log_esscher_error ν hn hδ hbound t hV.1 hxpos hroot' hs hweightedSmall
  refine ⟨hlog.1, ?_⟩
  have hmin : x / 2 ≤ min (moderateProductTailScale ν t) x := le_min hscale.1 (by linarith)
  have hdiv : |moderateProductTailScale ν t - x| / min (moderateProductTailScale ν t) x ≤
      2 * moderateCancellationConstant moderateTaylorConstant * δ ^ 2 * x ^ 2 := by
    apply (div_le_iff₀ (by linarith : 0 < min (moderateProductTailScale ν t) x)).mpr
    have hK : 0 ≤ moderateCancellationConstant moderateTaylorConstant := by unfold moderateCancellationConstant; positivity
    have hh := mul_le_mul_of_nonneg_left hmin (by positivity : 0 ≤ 2 * moderateCancellationConstant moderateTaylorConstant * δ ^ 2 * x ^ 2)
    nlinarith only [hcancel, hh]
  have hsum := (abs_add
    (Real.log ((Measure.pi ν).real {z | x < ∑ i, z i} / standardNormalUpperTail x) -
      ((∑ i, cgf id (ν i) t) - t * x + x ^ 2 / 2))
    (((∑ i, cgf id (ν i) t) - t * x + x ^ 2 / 2) -
      moderateArrayGamma (Measure.pi ν) (fun i z => z i) * x ^ 3 / 6)).trans (add_le_add hlog.2 hleg)
  have hsum' : |Real.log ((Measure.pi ν).real {z | x < ∑ i, z i} / standardNormalUpperTail x) -
      moderateArrayGamma (Measure.pi ν) (fun i z => z i) * x ^ 3 / 6| ≤
      2 * moderateWeightedConstant * δ * moderateProductTailScale ν t +
        |moderateProductTailScale ν t - x| / min (moderateProductTailScale ν t) x +
          moderateLegendreConstant moderateTaylorConstant * δ ^ 2 * x ^ 4 := by
    convert hsum using 1 <;> ring
  have hK : 0 ≤ moderateCancellationConstant moderateTaylorConstant := by unfold moderateCancellationConstant; positivity
  have hL : 0 ≤ moderateLegendreConstant moderateTaylorConstant := by
    unfold moderateLegendreConstant moderateInverseDisplacementConstant
    positivity
  have hx24 : x ^ 2 ≤ x ^ 4 := by nlinarith only [hx, sq_nonneg (x - 2), sq_nonneg (x ^ 2 - 1)]
  have hw := mul_le_mul_of_nonneg_left hscale.2 (by positivity : 0 ≤ 2 * moderateWeightedConstant * δ)
  have hk := mul_le_mul_of_nonneg_left hx24 (by positivity : 0 ≤ 2 * moderateCancellationConstant moderateTaylorConstant * δ ^ 2)
  have hC := moderateTailRemainderConstant_bounds
  have hr := mul_le_mul_of_nonneg_right hC.2.2 (by positivity : 0 ≤ δ * (1 + x) + δ ^ 2 * x ^ 4)
  have hpad1 : 0 ≤ (2 * moderateCancellationConstant moderateTaylorConstant + moderateLegendreConstant moderateTaylorConstant) * (δ * (1 + x)) := by positivity
  have hpad2 : 0 ≤ 6 * moderateWeightedConstant * (δ ^ 2 * x ^ 4) := by positivity
  apply hsum'.trans
  nlinarith only [hdiv, hw, hk, hr, hpad1, hpad2, mul_nonneg hW.le hδ]

end
end RectangleCLT.Companion.SplitV4
