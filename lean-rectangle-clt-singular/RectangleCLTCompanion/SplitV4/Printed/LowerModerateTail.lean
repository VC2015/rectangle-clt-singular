import RectangleCLTCompanion.SplitV4.Printed.LowerModerateCumulants
import RectangleCLTCompanion.SplitV4.Printed.LowerStrictTail

/-! The actual tilted F.1 proof at every positive threshold, including
arbitrarily small thresholds. Taylor bounds consume the literal two-copy
variance chain; no un-tilted small-x Berry–Esseen branch is used. -/
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

theorem moderateProduct_log_esscher_error_printed (ν : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    (hn : 1 ≤ n) {δ : ℝ} (hδ : 0 ≤ δ) (hbound : ∀ i, ∀ᵐ x ∂ν i, |x| ≤ δ) (t : ℝ)
    (hV : 1 / 2 ≤ genericTiltTotalVariance ν t) {x : ℝ} (hx : 0 < x)
    (hroot : (∑ i, genericTiltMean (ν i) t) = x)
    (hs : 0 < moderateProductTailScale ν t)
    (hsmall : moderateWeightedConstant * δ * (1+moderateProductTailScale ν t) ≤ 1 / 2) :
    0 < (Measure.pi ν).real {z | x < ∑ i, z i} ∧
    |Real.log ((Measure.pi ν).real {z | x < ∑ i, z i} / standardNormalUpperTail x) -
      ((∑ i, cgf id (ν i) t) - t * x + x ^ 2 / 2)| ≤
        2 * moderateWeightedConstant * δ * (1+moderateProductTailScale ν t) +
          |moderateProductTailScale ν t - x| / min (moderateProductTailScale ν t) x := by
  have hVpos : 0 < genericTiltTotalVariance ν t := by linarith
  have hE := moderateProductWeightedTail_log_error_nonneg ν hn hδ hbound t hV hs.le hsmall
  constructor
  · rw [moderateProduct_strict_tail_standardized ν hbound t hVpos hroot]
    exact mul_pos (Real.exp_pos _) hE.1
  · rw [moderateProduct_log_esscher ν hbound t hVpos hroot hE.1]
    have hh := (abs_add
      (Real.log (moderateProductWeightedTail ν t) - Real.log (normalWeightedTail (moderateProductTailScale ν t)))
      (Real.log (normalWeightedTail (moderateProductTailScale ν t)) - Real.log (normalWeightedTail x))).trans
      (add_le_add hE.2 (log_normalWeightedTail_lipschitz (by linarith : 0 < moderateProductTailScale ν t) hx))
    convert hh using 1 <;> ring

set_option maxHeartbeats 1000000 in
theorem moderateProductTail_positive_printed {n : ℕ} (ν : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] (hn : 1 ≤ n) {δ x : ℝ} (hδ : 0 ≤ δ)
    (hbound : ∀ i, ∀ᵐ z ∂ν i, |z| ≤ δ) (hc : ∀ i, (∫ z, z ∂ν i) = 0)
    (hv : (∑ i, ∫ z, z ^ 2 ∂ν i) = 1) (hx : 0 < x)
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
  obtain ⟨t, ht, hroot⟩ := exists_moderateArrayMean_eq_printed (fun i => measurable_pi_apply i) hδ hb hc' hv' hx0 hrootSmall
  have hdelta : δ*x≤1/100 := by nlinarith [mul_le_mul_of_nonneg_right hB hdx]
  have hdt : δ * t ≤ 1 := by nlinarith [ht.2]
  have hTaylor := moderateArray_local_taylor_printed (fun i => measurable_pi_apply i) hδ hb hc' hv' ht.1 hdt
  have hm : |x - t - moderateArrayGamma (Measure.pi ν) (fun i z => z i) * t ^ 2 / 2| ≤
      moderateTaylorConstant * δ ^ 2 * t ^ 3 := by simpa only [hroot] using hTaylor.2.1
  have hgamma := moderateArrayGamma_abs_le (fun i => measurable_pi_apply i) hδ hb hv'
  have hV := moderateArray_local_variance_bounds_printed (fun i => measurable_pi_apply i) hδ hb hc' hv' hx0 hrootSmall ht
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
  have hweightedSmall : moderateWeightedConstant*δ*(1+moderateProductTailScale ν t)≤1/2 := by
    have hh := (mul_le_mul hH.2.2.1 hdx' hdx hH.1.le).trans hsmall
    have hp := mul_le_mul_of_nonneg_left (show 1+moderateProductTailScale ν t≤3*(1+x) by linarith [hscale.2])
      (mul_nonneg hW.le hδ)
    nlinarith
  have hs : 0<moderateProductTailScale ν t := by linarith [hscale.1]
  have hlog := moderateProduct_log_esscher_error_printed ν hn hδ hbound t hV.1 hxpos hroot' hs hweightedSmall
  refine ⟨hlog.1,?_⟩
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
      2 * moderateWeightedConstant * δ * (1+moderateProductTailScale ν t) +
        |moderateProductTailScale ν t - x| / min (moderateProductTailScale ν t) x +
          moderateLegendreConstant moderateTaylorConstant * δ ^ 2 * x ^ 4 := by
    convert hsum using 1 <;> ring
  have hK : 0 ≤ moderateCancellationConstant moderateTaylorConstant := by unfold moderateCancellationConstant; positivity
  have hL : 0 ≤ moderateLegendreConstant moderateTaylorConstant := by
    unfold moderateLegendreConstant moderateInverseDisplacementConstant
    positivity
  have hbudget : δ^2*x^2≤δ*(1+x) := by
    have hh := mul_le_mul_of_nonneg_left hweak hdx
    nlinarith
  have hw := mul_le_mul_of_nonneg_left (show 1+moderateProductTailScale ν t≤3*(1+x) by linarith [hscale.2])
    (by positivity : 0≤2*moderateWeightedConstant*δ)
  have hk := mul_le_mul_of_nonneg_left hbudget (by positivity : 0≤2*moderateCancellationConstant moderateTaylorConstant)
  have hC := moderateTailRemainderConstant_bounds
  have hr := mul_le_mul_of_nonneg_right hC.2.2 (by positivity : 0≤δ*(1+x)+δ^2*x^4)
  have hpad1 : 0≤moderateLegendreConstant moderateTaylorConstant*(δ*(1+x)) := by positivity
  have hpad2 : 0≤(6*moderateWeightedConstant+2*moderateCancellationConstant moderateTaylorConstant)*(δ^2*x^4) := by positivity
  apply hsum'.trans
  nlinarith only [hdiv,hw,hk,hr,hpad1,hpad2]

theorem moderateProductTail_zero_printed {n : ℕ} (ν : Fin n→Measure ℝ)
    [∀i,IsProbabilityMeasure (ν i)] (hn : 1≤n) {δ : ℝ} (hδ : 0≤δ)
    (hb : ∀i,∀ᵐ z ∂ν i,|z|≤δ) (hc : ∀i,(∫z,z ∂ν i)=0)
    (hv : (∑i,∫z,z^2 ∂ν i)=1)
    (hsmall : moderateTailSmallConstant*δ≤1) :
    0<(Measure.pi ν).real {z | 0<∑i,z i} ∧
    |Real.log ((Measure.pi ν).real {z | 0<∑i,z i}/standardNormalUpperTail 0)|≤
      moderateTailRemainderConstant*δ := by
  have hbound := moderateProduct_coordinate_bound ν hb
  have hc' (i : Fin n) : (∫z : Fin n→ℝ,z i ∂Measure.pi ν)=0 :=
    (moderateProduct_coordinate_integral ν i id measurable_id).trans (hc i)
  have hv' : (∑i,∫z : Fin n→ℝ,(z i)^2 ∂Measure.pi ν)=1 := by
    calc
      _=∑i,∫z,z^2 ∂ν i := Finset.sum_congr rfl (fun i _ =>
        moderateProduct_coordinate_integral ν i (fun z => z^2) (measurable_id.pow_const 2))
      _=1 := hv
  have hV : genericTiltTotalVariance ν 0=1 := by
    rw [←moderateProduct_variance_eq ν hb,moderateArrayVariance_zero hc' hv']
  have hroot : (∑i,genericTiltMean (ν i) 0)=0 := by
    rw [←moderateProduct_mean_eq ν hb,moderateArrayMean_zero hc']
  have hs : moderateProductTailScale ν 0=0 := by simp [moderateProductTailScale]
  have hW := moderateWeightedConstant_pos
  have hH := moderateTailSmallConstant_bounds
  have hWsmall : moderateWeightedConstant*δ*(1+moderateProductTailScale ν 0)≤1/2 := by
    rw [hs]
    have hh := (mul_le_mul_of_nonneg_right hH.2.2.1 hδ).trans hsmall
    nlinarith
  have he := moderateProductWeightedTail_log_error_nonneg ν hn hδ hb 0
    (by rw [hV]; norm_num) (by rw [hs]) hWsmall
  have hp : 0<(Measure.pi ν).real {z | 0<∑i,z i} := by
    rw [moderateProduct_strict_tail_standardized ν hb 0 (by rw [hV]; norm_num) hroot]
    exact mul_pos (Real.exp_pos _) he.1
  refine ⟨hp,?_⟩
  have hlog := moderateProduct_log_esscher ν hb 0 (by rw [hV]; norm_num) hroot he.1
  simp only [cgf_zero,Finset.sum_const_zero,zero_mul,zero_pow (by decide : 2≠0),zero_div,
    sub_zero,add_zero,hs] at hlog
  rw [hlog]
  simp only [zero_add,sub_self,add_zero]
  have hC := moderateTailRemainderConstant_bounds
  have hB := moderateTaylorConstant_ge_one
  have hK : 0≤moderateCancellationConstant moderateTaylorConstant := by unfold moderateCancellationConstant; positivity
  have hL : 0≤moderateLegendreConstant moderateTaylorConstant := by unfold moderateLegendreConstant moderateInverseDisplacementConstant; positivity
  have hbC : 2*moderateWeightedConstant≤moderateTailRemainderConstant := by linarith [hC.2.2]
  have hboundC := mul_le_mul_of_nonneg_right hbC hδ
  rw [hs] at he
  simp only [add_zero,mul_one] at he
  exact he.2.trans hboundC

theorem moderateProductTail_nonneg_printed {n : ℕ} (ν : Fin n→Measure ℝ)
    [∀i,IsProbabilityMeasure (ν i)] (hn : 1≤n) {δ x : ℝ} (hδ : 0≤δ)
    (hb : ∀i,∀ᵐ z ∂ν i,|z|≤δ) (hc : ∀i,(∫z,z ∂ν i)=0)
    (hv : (∑i,∫z,z^2 ∂ν i)=1) (hx : 0≤x)
    (hsmall : moderateTailSmallConstant*(δ*(1+x))≤1) :
    0<(Measure.pi ν).real {z | x<∑i,z i} ∧
    |Real.log ((Measure.pi ν).real {z | x<∑i,z i}/standardNormalUpperTail x)-
      moderateArrayGamma (Measure.pi ν) (fun i z => z i)*x^3/6|≤
        moderateTailRemainderConstant*(δ*(1+x)+δ^2*x^4) := by
  rcases hx.eq_or_lt with he | he
  · subst x
    simpa using moderateProductTail_zero_printed ν hn hδ hb hc hv (by simpa using hsmall)
  · exact moderateProductTail_positive_printed ν hn hδ hb hc hv he hsmall

end
end RectangleCLT.Companion.SplitV4.Printed
